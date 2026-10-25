import NearNode.Rpc.ChainViews
import NearNode.Trie
import NearNode.Validator.Prepare

/-!
# Reading the state of a shard

`TrieViewer` (`runtime/runtime/src/state_viewer`) over the node's own tries: an account, an access key,
the contract code, the access keys of an account, the storage of a contract by prefix. Each reads the
trie of the shard of the account at the state root a block left (`ChunkExtra::state_root` of the block).
-/

namespace Near.Node.Rpc

open Lean Near.Node Near.Node.Borsh Near.Node.Chain Near.Node.Network Near.Node.Validator
  Near.Node.Apply Near.Node.Trie

/-- The state a query reads. -/
structure StateAt where
  block : BlockRec
  shard : ShardId
  root : CryptoHash
  src : NodeSource

/-- The state of the shard of `account` after `block`. -/
def stateAt (s : VState) (block : BlockRec) (account : AccountId) : Except String StateAt := do
  let epoch ←
    match s.st.epoch block.view.epochId with
    | .ok e =>
      pure e
    | .error e =>
      throw s!"{e.kind}"
  let some shard := epoch.layout.accountIdToShardId account | throw "no shard for the account"
  let some (.v5 x) := s.pr.extras[(block.hash.bytes, shard)]? | throw "no chunk extra for the block"
  pure
      { block, shard, root := x.stateRoot,
        src := s.pr.tables.nodeSource (shardKey epoch.layout shard) }

def StateAt.get (v : StateAt) (key : TrieKey) : Except String (Option ByteArray) := do
  let (r, _) ← Trie.get v.src v.root (TrieKey.toVec key)
  pure r

def StateAt.account (v : StateAt) (a : AccountId) : Except String (Option Account) := do
  match ← v.get (.account a) with
  | none =>
    pure none
  | some b =>
    some <$> (Codec.decodeAll (α := Account) b).mapError fun e => s!"account: {repr e}"

/-- The hash of the contract code the account itself holds (`Account::local_contract_hash`). -/
def _root_.Near.Node.Account.localHash : Account → Option CryptoHash
  | .v1 _ _ h _ => if h == CryptoHash.zero then none else some h
  | .v2 _ _ _ (.local h) => some h
  | .v2 .. => none

def accountView (a : Account) : Json :=
  let (amount, locked, usage) :=
    match a with
    | .v1 am lo _ us => (am, lo, us)
    | .v2 am lo us _ => (am, lo, us)
  let global : List (String × Json) :=
    match a with
    | .v2 _ _ _ (.global h) => [("global_contract_hash", jhash h)]
    | .v2 _ _ _ (.globalByAccount id) => [("global_contract_account_id", jacc id)]
    | _ => []
  Json.mkObj
    ([("amount", jbal amount), ("locked", jbal locked),
        ("code_hash", jhash (a.localHash.getD CryptoHash.zero)), ("storage_usage", jn usage.toNat),
        ("storage_paid_at", jn 0)] ++
      global)

def handleOfKey : PublicKey → Option PublicKeyHandle :=
  handleOf

def StateAt.accessKey (v : StateAt) (a : AccountId) (pk : PublicKey) :
    Except String (Option AccessKey) := do
  let some h := handleOf pk | return none
  match ← v.get (.accessKey a h) with
  | none =>
    pure none
  | some b =>
    some <$> (Codec.decodeAll (α := AccessKey) b).mapError fun e => s!"access key: {repr e}"

/-- The access keys of an account in trie order. -/
def StateAt.accessKeys (v : StateAt) (a : AccountId) :
    Except String (Array (PublicKey × AccessKey)) := do
  let prefix_ :=
    (TrieKey.toVec (.accessKey a (.ed25519 (ByteArray.mk (Array.replicate 32 0))))).extract 0
      (a.val.toUTF8.size + 2)
  let r ←
    Trie.foldFrom v.src v.root prefix_ (some #[] : Option (Array (ByteArray × ValueRef)))
        fun acc k ref =>
        if k.size ≥ prefix_.size && k.extract 0 prefix_.size == prefix_ then
          (acc.map (·.push (k, ref)), true)
        else (acc, false)
  let mut out := #[]
  for (k, ref) in r.getD #[] do
    let rest := k.extract prefix_.size k.size
    match Impl.Codec.get (Codec.impl : Impl.Codec PublicKeyHandle) rest 0 with
    | .ok h p =>
      if p == rest.size then
        let some raw := v.src.read ref.hash | throw "access key value missing"
        let key ← (Codec.decodeAll (α := AccessKey) raw).mapError fun e => s!"access key: {repr e}"
        let pk : PublicKey :=
          match h with
          | .ed25519 k => .ed25519 k
          | .secp256k1 k => .secp256k1 k
          | .mldsa65 k => .mldsa65 k
        out := out.push (pk, key)
    | .err _ =>
      pure ()
  pure out

/-- The contract data of an account whose key starts with `prefix_`, in trie order, from `after`
on (`ViewStateResult`). -/
def StateAt.contractData (v : StateAt) (a : AccountId) (prefix_ : ByteArray)
    (limit : Option Nat := none) : Except String (Array (ByteArray × ByteArray)) := do
  let base := TrieKey.toVec (.contractData a ByteArray.empty)
  let full := base ++ prefix_
  let r ←
    Trie.foldFrom v.src v.root full (#[] : Array (ByteArray × ValueRef)) fun acc k ref =>
        if k.size ≥ full.size && k.extract 0 full.size == full && !(limit.any (acc.size ≥ ·)) then
          (acc.push (k, ref), true)
        else (acc, false)
  r.mapM fun (k, ref) =>
      match v.src.read ref.hash with
      | some raw => pure (k.extract base.size k.size, raw)
      | none => throw "contract data value missing"

end Near.Node.Rpc
