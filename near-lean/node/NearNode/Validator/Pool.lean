import Std.Data.HashMap
import Std.Data.HashSet
import NearNode.Primitives

/-!
# The transaction pool

`chain/pool` (`TransactionPool`, `PoolIteratorWrapper`) at the pinned nearcore, for one shard:

* transactions are grouped by `(signer, public key[, nonce index])`; the group is keyed by
  `hash(borsh(public_key) ++ key_seed ++ account_id [++ nonce_index])` and the groups are visited in
  the order of those hashes, round robin, starting after the last key used;
* `insert` refuses duplicates (by transaction hash) and, above `limit` bytes of wire size,
  answers `noSpaceLeft`;
* `remove` takes out the transactions a chunk included;
* `prepare` is the loop of `Runtime::prepare_transactions_extra` over the pool's iterator: one
  transaction from each group in turn, until a limit is hit or the pool is out of transactions. The
  decision about a single transaction (congestion, validity period, signer state, cost) is a
  parameter, so this module knows nothing of chains and tries; `NearNode.Validator.Prepare` supplies it.

The pool keeps the transactions it handed out: `prepare` reintroduces the ones it returns
(`reintroduce_transactions`), they leave the pool when a block includes them.

Group lookup scans the keys of the pool (`O(groups)` per step); the pool of a localnet is small.
-/

namespace Near.Node

open Near.Node Near.Node.Borsh

namespace Transaction

def signerId : Transaction → AccountId
  | .v0 t => t.signerId
  | .v1 t => t.signerId

def receiverId : Transaction → AccountId
  | .v0 t => t.receiverId
  | .v1 t => t.receiverId

def publicKey : Transaction → PublicKey
  | .v0 t => t.publicKey
  | .v1 t => t.publicKey

def blockHash : Transaction → CryptoHash
  | .v0 t => t.blockHash
  | .v1 t => t.blockHash

def actions : Transaction → Array Action
  | .v0 t => t.actions
  | .v1 t => t.actions

/-- The nonce and, for a gas key, the index of its lane. -/
def nonce : Transaction → TransactionNonce
  | .v0 t => .nonce t.nonce
  | .v1 t => t.nonce

def nonceValue (t : Transaction) : Nonce :=
  match t.nonce with
  | .nonce n | .gasKeyNonce n _ => n

def nonceIndex (t : Transaction) : Option NonceIndex :=
  match t.nonce with
  | .nonce _ => none
  | .gasKeyNonce _ i => some i

def isStrict : Transaction → Bool
  | .v0 _ => false
  | .v1 t => t.nonceMode == .strict

end Transaction

/-- The size that counts against the pool and the chunk limits (`SignedTransaction::wire_size`,
which is `size_for_limits` from the protocol feature `PostQuantumSignatures`, so at protocol 86). -/
def SignedTransaction.wireSize (t : SignedTransaction) : Nat :=
  (Codec.encode t).size

end Near.Node

namespace Near.Node.Validator

open Near.Node Near.Node.Borsh

/-- The default `transaction_pool_size_limit` of `near_chain_configs::ClientConfig`. -/
def defaultPoolLimit : Nat :=
  100_000_000

/-- Compares two byte strings as `[u8; 32]` arrays (`CryptoHash` order). -/
def bytesLt (a b : ByteArray) : Bool :=
  Id.run do
    for i in [0:min a.size b.size] do
      if a.get! i != b.get! i then
        return a.get! i < b.get! i
    return a.size < b.size

inductive InsertResult where
  | success
  | duplicate
  | noSpaceLeft
  deriving BEq, Repr

structure Pool where
  /-- `key_seed`: randomizes the order of the groups. -/
  seed : ByteArray := ⟨Array.replicate 32 0⟩
  groups : Std.HashMap ByteArray (Array SignedTransaction) := {}
  hashes : Std.HashSet ByteArray := {}
  size : Nat := 0
  lastKey : ByteArray := ⟨Array.replicate 32 0⟩
  limit : Option Nat := some defaultPoolLimit

namespace Pool

def count (p : Pool) : Nat :=
  p.hashes.size

/-- `TransactionPool::key`. -/
def groupKey (p : Pool) (t : SignedTransaction) : ByteArray :=
  let tx := t.transaction
  let v := (Codec.encode tx.publicKey) ++ p.seed ++ tx.signerId.val.toUTF8
  let v :=
    match tx.nonceIndex with
    | some i => v ++ Codec.encode i
    | none => v
  (CryptoHash.hash v).bytes

def contains (p : Pool) (t : SignedTransaction) : Bool :=
  p.hashes.contains t.hash.bytes

/-- `TransactionPool::insert_transaction`. -/
def insert (p : Pool) (t : SignedTransaction) : Pool × InsertResult :=
  let h := t.hash.bytes
  if p.hashes.contains h then (p, .duplicate)
  else
    let size := p.size + t.wireSize
    if p.limit.any (size > ·) then (p, .noSpaceLeft)
    else
      let k := p.groupKey t
      ({ p with
          hashes := p.hashes.insert h, size,
          groups := p.groups.insert k ((p.groups.getD k #[]).push t) },
        .success)

/-- `TransactionPool::remove_transactions`. -/
def remove (p : Pool) (ts : Array SignedTransaction) : Pool :=
  Id.run do
    let mut p := p
    for t in ts do
      let h := t.hash.bytes
      unless p.hashes.contains h do
        continue
      p := { p with hashes := p.hashes.erase h }
      let k := p.groupKey t
      if let some g := p.groups[k]? then
        let g' := g.filter (·.hash.bytes != h)
        p := { p with size := p.size - t.wireSize }
        p :=
          if g'.isEmpty then { p with groups := p.groups.erase k }
          else { p with groups := p.groups.insert k g' }
    return p

/-- `TransactionPool::reintroduce_transactions`: the ones that are not in the pool are inserted
again (at the pool's own limit). -/
def reintroduce (p : Pool) (ts : Array SignedTransaction) : Pool :=
  ts.foldl (fun p t => (p.insert t).1) p

/-! ### The iterator -/

/-- A group taken out of the pool: transactions by increasing nonce, those before `pos` handed out. -/
structure Group where
  key : ByteArray
  txs : Array SignedTransaction
  pos : Nat := 0
  removed : Array SignedTransaction := #[]
  removedAny : Bool := false

def Group.peek (g : Group) : Option SignedTransaction :=
  g.txs[g.pos]?

def Group.next (g : Group) : Option (SignedTransaction × Group) :=
  match g.txs[g.pos]? with
  | some t =>
    some
      (t,
        { g with
          pos := g.pos + 1, removed := g.removed.push t, removedAny := true })
  | none => none

def Group.rest (g : Group) : Array SignedTransaction :=
  g.txs.extract g.pos g.txs.size

/-- The state of `PoolIteratorWrapper`. -/
structure Iter where
  pool : Pool
  queue : Array Group := #[]
  stalled : Array Group := #[]

def iter (p : Pool) : Iter :=
  { pool := p }

/-- The key of the next group to pull from the pool: the first key after `last_used_key`, else the
first key. -/
private def nextKey (p : Pool) : Option ByteArray :=
  Id.run do
    let mut after : Option ByteArray := none
    let mut first : Option ByteArray := none
    for (k, _) in p.groups.toList do
      if first.all (bytesLt k ·) then
        first := some k
      if bytesLt p.lastKey k && after.all (bytesLt k ·) then
        after := some k
    return after.orElse fun _ => first

/-- `TransactionGroupIterator::next`: the next group, taken out of the iterator (the caller puts it
back with `Iter.putBack` when it is done with it). -/
partial def Iter.next (it : Iter) : Option (Group × Iter) :=
  match nextKey it.pool with
  | some k =>
    let txs :=
      (it.pool.groups.getD k #[]).qsort fun a b =>
        a.transaction.nonceValue < b.transaction.nonceValue
    let pool :=
      { it.pool with
        groups := it.pool.groups.erase k, lastKey := k }
    some ({ key := k, txs }, { it with pool })
  | none =>
    if h : 0 < it.queue.size then
      let g := it.queue[0]
      let it := { it with queue := it.queue.extract 1 it.queue.size }
      if g.peek.isNone then
        -- a finished group: what it handed out leaves the pool for good
        let pool :=
          g.removed.foldl
            (fun (p : Pool) t =>
              { p with
                hashes := p.hashes.erase t.hash.bytes, size := p.size - t.wireSize })
            it.pool
        Iter.next { it with pool }
      else
        if !g.removedAny then Iter.next { it with stalled := it.stalled.push g }
        else some ({ g with removedAny := false }, it)
    else none

def Iter.putBack (it : Iter) (g : Group) : Iter :=
  { it with queue := it.queue.push g }

/-- `Drop for PoolIteratorWrapper`: groups with transactions go back to the pool; what was handed out
leaves it. -/
def Iter.finish (it : Iter) : Pool :=
  Id.run do
    let mut p := it.pool
    for g in it.queue ++ it.stalled do
      for t in g.removed do
        p :=
          { p with
            hashes := p.hashes.erase t.hash.bytes, size := p.size - t.wireSize }
      let rest := g.rest
      unless rest.isEmpty do
        p := { p with groups := p.groups.insert g.key rest }
    return p

/-! ### Preparing a chunk's transactions -/

/-- Why `prepare` stopped (`PrepareTransactionsLimit`). -/
inductive Limit where
  | noMoreTxsInPool
  | gas
  | size
  deriving BEq, Repr

def Limit.name : Limit → String
  | .noMoreTxsInPool => "no more txs in pool"
  | .gas => "gas"
  | .size => "size"

structure Prepared where
  pool : Pool
  txs : Array SignedTransaction
  limit : Limit
  /-- Taken from the pool and dropped as invalid. -/
  rejected : Array (SignedTransaction × String) := #[]

/-- The loop of `prepare_transactions_extra` (the pool, the gas and size limits, the strict nonce
gap rule), over the decisions of the caller.

* `peekNonce ω t`: the nonce the key of `t` has now, when `t` is a strict-nonce transaction (the
  nonce gap check); `none` lets the transaction through to full validation;
* `ttl t`: whether `t` is still inside its validity period (`validate_tx_ttl`), used to drop a
  transaction that waits for a nonce gap to close;
* `admit ω t`: the verdict on `t` given the state `ω` (every earlier included transaction applied):
  the new state and the gas the transaction burns, or the reason it is discarded. -/
def prepare {ω : Type} (pool : Pool) (init : ω) (gasLimit sizeLimit : Nat)
    (sizeOf : SignedTransaction → Nat) (peekNonce : ω → SignedTransaction → Option Nat)
    (ttl : SignedTransaction → Bool) (admit : ω → SignedTransaction → Except String (ω × Nat)) :
    Prepared :=
  Id.run do
    let mut it := pool.iter
    let mut state := init
    let mut gas := 0
    let mut size := 0
    let mut out : Array SignedTransaction := #[]
    let mut rejected : Array (SignedTransaction × String) := #[]
    let mut limit := Limit.noMoreTxsInPool
    let mut done := false
    for _ in [0:1000000] do
      if done then
        break
      let some (g, it') := it.next | break
      it := it'
      if gas ≥ gasLimit then
        limit := .gas
        it := it.putBack g
        break
      if size ≥ sizeLimit then
        limit := .size
        it := it.putBack g
        break
      let mut g := g
      -- one transaction from this group
      for _ in [0:g.txs.size + 1] do
        let some tx := g.peek | break
        if size + sizeOf tx > sizeLimit then
          limit := .size
          done := true
          break
        if tx.transaction.isStrict then
          if let some current := peekNonce state tx then
            if tx.transaction.nonceValue.toNat > current + 1 then
              if !ttl tx then
                g := (g.next.map (·.2)).getD g
                continue
              break
        let some (tx, g') := g.next | break
        g := g'
        match admit state tx with
        | .ok (state', used) =>
          state := state'
          gas := gas + used
          size := size + sizeOf tx
          out := out.push tx
          break
        | .error why =>
          rejected := rejected.push (tx, why)
      it := it.putBack g
    -- `reintroduce_transactions` of the prepared ones
    let pool := out.foldl (fun p t => (p.insert t).1) it.finish
    return { pool, txs := out, limit, rejected }

end Pool

end Near.Node.Validator
