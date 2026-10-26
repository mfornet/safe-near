import NearNode.Primitives
import NearCrypto.Sha256
import NearRuntime
import ChainReplay.Wire

/-!
# From the chain's data to the runtime's model

The runtime (`NearRuntime`, M3) works on a represented state: accounts, access keys, contract
storage, receipts waiting for data, the delayed queue, yields and global contracts, with counters
for receipt and data ids and a code catalogue. nearcore keeps the same facts as trie entries, and
transactions and receipts as Borsh. This module converts the node's types into the model's, and a
shard's complete trie entries into a model state with the facts that encode it back byte for byte
(`QueueEncoding.Context`). The conversion follows `tools/localnet/lean_input.py`, which M3 validated
on 436 chunks; a feature the model does not represent is an error, never an approximation.
-/

namespace Near.Node.Apply

open Near.Node Near.Node.Borsh

/-- A model failure or an unsupported feature. -/
abbrev Fail :=
  String

/-! ### The conversion state -/

/-- Contract code by label (`base58(sha256(bytes))`), shared by all chunks, and what is worth remembering
about large byte strings from one chunk to the next: converting a contract between `ByteArray` and
`List UInt8` and hashing it each time was a third of the work of a quiet chunk. -/
structure CodeCache where
  byLabel : Std.HashMap String ChainReplay.LoadedCode := {}
  /-- The list of a large byte string, by content. -/
  lists : Std.HashMap ByteArray (List UInt8) := {}
  /-- The label of contract bytes, by content (so that unchanged code is not hashed again). -/
  labels : Std.HashMap ByteArray String := {}
  /-- Prune when `byLabel` has this many entries (twice what it had after the last pruning, at least 32). -/
  pruneAt : Nat := 32

/-- Byte strings from this size on are remembered. -/
def CodeCache.bigSize : Nat :=
  2048

/-- The list of `b`; a large `b` is converted once. -/
def CodeCache.list (c : CodeCache) (b : ByteArray) : List UInt8 × CodeCache :=
  if b.size < CodeCache.bigSize then (b.toList, c)
  else
    match c.lists[b]? with
    | some l => (l, c)
    | none =>
      let l := b.toList
      -- old versions of contracts are forgotten when there are many
      let lists := if c.lists.size ≥ 512 then {} else c.lists
      (l, { c with lists := lists.insert b l })

/-- Forgets the contract code that nothing references: `live` holds the hashes of the values the retained tries reference
(`State` entries with a positive count), and a code is its value, named by its hash. nearcore counts references to contract
code in the trie in the same way (the `State` column stores the code under `sha256(code)` with a count, and garbage
collection removes it when the last state that held it goes). Everything dropped here is a cache of work the node does again
on the next use (`Model.code` decodes the bytes it meets), so pruning between two applications changes no result. -/
def CodeCache.prune (c : CodeCache) (live : Std.HashSet ByteArray)
    (hashOfLabel : String → Option ByteArray) : CodeCache :=
  let byLabel :=
    c.byLabel.fold
      (fun m label _ =>
        match hashOfLabel label with
        | some h => if live.contains h then m else m.erase label
        | none => m.erase label)
      c.byLabel
  let (labels, lists) :=
    c.labels.fold
      (fun (labels, lists) bytes label =>
        if byLabel.contains label then (labels, lists) else (labels.erase bytes, lists.erase bytes))
      (c.labels, c.lists)
  { byLabel, labels, lists, pruneAt := max 32 (2 * byLabel.size) }

/-- The inverse: a list equal to a remembered one gives back its `ByteArray`. -/
def CodeCache.bytesOf (known : Array (ByteArray × List UInt8)) (l : List UInt8) : ByteArray :=
  if l.length < CodeCache.bigSize then ⟨l.toArray⟩
  else
    match known.find? (fun (_, l') => l' == l) with
    | some (b, _) => b
    | none => ⟨l.toArray⟩

/-- The ids handed out and the facts that bind them to native hashes. -/
structure Conv where
  cache : CodeCache := {}
  /-- The labels of the codes this chunk uses, in first-use order. -/
  used : Array String := #[]
  next : Nat := 1
  receiptIds : Std.HashMap ByteArray Nat := {}
  receiptBindings : Array (Nat × ByteArray) := #[]
  dataIds : Std.HashMap ByteArray Nat := {}
  dataBindings : Array (Nat × ByteArray) := #[]
  dataReceivers : Std.HashMap ByteArray String := {}
  formats : Array (Nat × Near.ReceiptEncoding.ActionFormat) := #[]

abbrev M :=
  StateT Conv (Except Fail)

def fail (message : String) : M α :=
  throw message

/-- `Bytes` of a `ByteArray`. -/
def listOf (b : ByteArray) : List UInt8 :=
  b.toList

def keyBytes (k : PublicKey) : List UInt8 :=
  (Codec.encode k).toList

def freshId : M Nat := do
  let s ← get
  set { s with next := s.next + 1 }
  return s.next

/-- The model id of a native receipt id, allocated on first use. -/
def receiptId (native : CryptoHash) : M Nat := do
  match (← get).receiptIds[native.bytes]? with
  | some id =>
    return id
  | none =>
    let id ← freshId
    modify fun s =>
        { s with
          receiptIds := s.receiptIds.insert native.bytes id,
          receiptBindings := s.receiptBindings.push (id, native.bytes) }
    return id

/-- The model id of a native data id, allocated on first use. -/
def dataId (native : CryptoHash) : M Nat := do
  match (← get).dataIds[native.bytes]? with
  | some id =>
    return id
  | none =>
    let id ← freshId
    modify fun s =>
        { s with
          dataIds := s.dataIds.insert native.bytes id,
          dataBindings := s.dataBindings.push (id, native.bytes) }
    return id

def setReceiver (native : CryptoHash) (account : AccountId) : M Unit :=
  modify fun s => { s with dataReceivers := s.dataReceivers.insert native.bytes account.val }

def addFormat (id : Nat) (format : Near.ReceiptEncoding.ActionFormat) : M Unit :=
  modify fun s => { s with formats := s.formats.push (id, format) }

/-- SHA-256 of a byte list with the `NearCrypto` implementation: the digest the runtime's encoders are
given in place of the list-based specification (`Near.Sha256.hash`, which takes seconds for a
megabyte of contract code). -/
def digest (b : List UInt8) : List UInt8 :=
  (NearCrypto.sha256 ⟨b.toArray⟩).toList

/-- The 32 bytes a base58 label stands for, if it is the label of exactly that hash (`Near.StateEncoding.base58`). -/
def hashOfLabel? (label : String) : Option (List UInt8) :=
  let alphabet := "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz".toList
  let n? :=
    label.toList.foldl (fun acc c => acc.bind fun n => (alphabet.idxOf? c).map fun d => n * 58 + d)
      (some 0)
  n?.bind fun n =>
    let bytes := (List.range 32).reverse.map fun i => UInt8.ofNat (n / 256 ^ i % 256)
    if Near.StateEncoding.base58 bytes == label then some bytes else none

/-- `digest`, except that the contract bytes of the catalogue (which the encoders look up
by label) are not hashed again: their label is the SHA-256 of exactly those bytes, computed when the code was
decoded (`code` below). Hashing every contract of the shard twice per chunk was the largest part of
`encode-state`. -/
def digestFor (catalogue : List (String × List UInt8)) (b : List UInt8) : List UInt8 :=
  match catalogue.find? (fun (_, bytes) => bytes == b) with
  | some (label, _) => (hashOfLabel? label).getD (digest b)
  | none => digest b

/-- The catalogue entry of contract bytes, decoded once. A module that does not decode is kept
with its issue, as `ChainReplay.codeOf` does. -/
def code (blob : ByteArray) : M ChainReplay.LoadedCode := do
  let s ← get
  let label :=
    match s.cache.labels[blob]? with
    | some l => l
    | none => Near.StateEncoding.base58 (NearCrypto.sha256 blob).toList
  let (bytes, cache) :=
    match s.cache.byLabel[label]? with
    | some e => (e.bytes, s.cache)
    | none => s.cache.list blob
  let entry : ChainReplay.LoadedCode :=
    match s.cache.byLabel[label]? with
    | some e => e
    | none =>
      match Wasm.Binary.decode blob with
      | .ok module => { bytes, code := { module, size := blob.size, hash := label } }
      | .error e =>
        { bytes,
          code :=
            { module := default, size := blob.size, hash := label,
              decodeIssue :=
                some (.interpreterError s!"deployed bytes do not decode: {e.message}") } }
  set
      { s with
        cache :=
          { cache with
            byLabel := cache.byLabel.insert label entry, labels := cache.labels.insert blob label },
        used := if s.used.contains label then s.used else s.used.push label }
  return entry

/-! ### Keys, access keys, global contracts -/

def accessKeyPermission : AccessKeyPermission → Near.AccessKeyPermission
  | .functionCall p => .functionCall (p.allowance.map (·.val)) p.receiverId p.methodNames.toList
  | .fullAccess => .fullAccess
  | .gasKeyFunctionCall i p =>
    .gasKeyFunctionCall i.balance.val i.numNonces.toNat (p.allowance.map (·.val)) p.receiverId
      p.methodNames.toList
  | .gasKeyFullAccess i => .gasKeyFullAccess i.balance.val i.numNonces.toNat

def accessKey (k : AccessKey) : Near.AccessKey :=
  { nonce := k.nonce.toNat, permission := accessKeyPermission k.permission }

def globalId : GlobalContractIdentifier → Wasm.GlobalContractId
  | .codeHash h => .codeHash h.bytes.toList
  | .accountId a => .accountId a.val.toUTF8.toList

/-! ### Actions, transactions -/

mutual
/-- A base action. Delegate actions are converted by `action`. -/
partial def baseAction : BaseAction → M Near.Action
  | .createAccount => pure .createAccount
  | .deployContract a => do
    pure (.deployContract (← code a.code).code)
  | .functionCall a => pure (.functionCall a.methodName a.args.toList a.gas.toNat a.deposit.val)
  | .transfer a => pure (.transfer a.deposit.val)
  | .stake a => pure (.stake a.stake.val (keyBytes a.publicKey))
  | .addKey a => pure (.addKey (keyBytes a.publicKey) (accessKey a.accessKey))
  | .deleteKey a => pure (.deleteKey (keyBytes a.publicKey))
  | .deleteAccount a => pure (.deleteAccount a.beneficiaryId.val)
  | .deployGlobalContract a => do
    let mode : Near.GlobalDeployMode :=
      match a.deployMode with
      | .codeHash => .codeHash
      | .accountId => .accountId
    pure (.deployGlobalContract (← code a.code).code mode)
  | .useGlobalContract a => pure (.useGlobalContract (globalId a.contractIdentifier))
  | .deterministicStateInit _ => fail "action DeterministicStateInit"
  | .transferToGasKey a => pure (.transferToGasKey (keyBytes a.publicKey) a.deposit.val)
  | .withdrawFromGasKey a => pure (.withdrawFromGasKey (keyBytes a.publicKey) a.amount.val)
partial def action : Action → M Near.Action
  | .base a => baseAction a
  | .delegate a => do
    let d := a.delegateAction
    pure
        (.delegate d.senderId.val d.receiverId.val (← d.actions.toList.mapM baseAction)
          d.nonce.toNat none d.maxBlockHeight.toNat (keyBytes d.publicKey)
          (Codec.encode a.signature).toList false)
  | .delegateV2 a => do
    let .v2 d := a.delegateAction
    let (nonce, index) :=
      match d.nonce with
      | .nonce n => (n.toNat, none)
      | .gasKeyNonce n i => (n.toNat, some i.toNat)
    pure
        (.delegate d.senderId.val d.receiverId.val (← d.actions.toList.mapM baseAction) nonce index
          d.maxBlockHeight.toNat (keyBytes d.publicKey) (Codec.encode a.signature).toList true)
end

/-- A signed transaction as the model's transaction and the block hash it names. -/
def transaction (t : SignedTransaction) : M (Near.Transaction × List UInt8) := do
  match t.transaction with
  | .v0 t =>
    pure
        ({ signerId := t.signerId.val, publicKey := keyBytes t.publicKey, nonce := t.nonce.toNat,
           receiverId := t.receiverId.val, actions := (← t.actions.toList.mapM action) },
          t.blockHash.bytes.toList)
  | .v1 t =>
    let nonce ←
      match t.nonce with
      | .nonce n =>
        pure n.toNat
      | .gasKeyNonce .. =>
        fail "gas-key nonce index"
    pure
        ({ version := 1,
           nonceMode :=
             match t.nonceMode with
             | .monotonic => .monotonic
             | .strict => .strict,
           signerId := t.signerId.val, publicKey := keyBytes t.publicKey, nonce,
           receiverId := t.receiverId.val, actions := (← t.actions.toList.mapM action) },
          t.blockHash.bytes.toList)

/-! ### Receipts -/

/-- The model's action receipt of the fields all action receipt versions share. -/
def actionReceipt (signer : AccountId) (key : PublicKey) (price : Balance)
    (outputs : Array DataReceiver) (inputs : Array CryptoHash) (actions : Array Action)
    (yieldData : Option (List UInt8) := none) (receiver : AccountId) : M Near.ActionReceipt := do
  for i in inputs do
    setReceiver i receiver
  for o in outputs do
    setReceiver o.dataId o.receiverId
  pure
      { signerId := signer.val, signerPublicKey := keyBytes key, gasPrice := price.val,
        inputDataIds :=
          (←
            if yieldData.isSome then
              pure []
            else
              inputs.toList.mapM dataId),
        outputDataReceivers :=
          (←
            outputs.toList.mapM fun o => do
                pure { dataId := ← dataId o.dataId, receiverId := o.receiverId.val }),
        actions := (← actions.toList.mapM action), yieldDataId := yieldData }

/-- A receipt of the node as the model's receipt, and whether it is stored in the V2 format. -/
def receipt (r : Receipt) : M (Near.Receipt × Near.ReceiptEncoding.ActionFormat) := do
  let .v0 r := r
  let (body, format) ←
    match r.receipt with
    | .action a =>
      pure
          (Near.ReceiptEnum.action
              (←
                actionReceipt a.signerId a.signerPublicKey a.gasPrice a.outputDataReceivers
                    a.inputDataIds a.actions none r.receiverId),
            Near.ReceiptEncoding.ActionFormat.legacy)
    | .actionV2 a =>
      if a.refundTo.isSome then
        fail "receipt with an explicit refund_to"
      pure
          (Near.ReceiptEnum.action
              (←
                actionReceipt a.signerId a.signerPublicKey a.gasPrice a.outputDataReceivers
                    a.inputDataIds a.actions none r.receiverId),
            .v2)
    | .promiseYield a =>
      if a.inputDataIds.size != 1 then
        fail "stored yield receipt with an unexpected shape"
      pure
          (.action
              (←
                actionReceipt a.signerId a.signerPublicKey a.gasPrice a.outputDataReceivers
                    a.inputDataIds a.actions (some a.inputDataIds[0]!.bytes.toList) r.receiverId),
            .legacy)
    | .promiseYieldV2 a =>
      if a.refundTo.isSome then
        fail "stored receipt with an explicit refund_to"
      if a.inputDataIds.size != 1 then
        fail "stored yield receipt with an unexpected shape"
      pure
          (.action
              (←
                actionReceipt a.signerId a.signerPublicKey a.gasPrice a.outputDataReceivers
                    a.inputDataIds a.actions (some a.inputDataIds[0]!.bytes.toList) r.receiverId),
            .v2)
    | .data d =>
      setReceiver d.dataId r.receiverId
      pure (.data { dataId := ← dataId d.dataId, data := d.data.map (·.toList) }, .legacy)
    | .promiseResume d =>
      pure
          (.data
              { dataId := 0, data := d.data.map (·.toList),
                resumeDataId := some d.dataId.bytes.toList },
            .legacy)
    | .globalContractDistribution d =>
      let (id, target, delivered, blob, nonce) :=
        match d with
        | .v1 v => (v.id, v.targetShard, v.alreadyDeliveredShards, v.code, 0)
        | .v2 v => (v.id, v.targetShard, v.alreadyDeliveredShards, v.code, v.nonce.toNat)
      pure
          (.globalDistribution
              { id := globalId id, targetShard := target.toNat,
                alreadyDelivered := delivered.toList.map (·.toNat), code := (← code blob).code,
                nonce },
            .legacy)
  let id ← receiptId r.receiptId
  addFormat id format
  pure
      ({ predecessorId := r.predecessorId.val, receiverId := r.receiverId.val, receiptId := id,
         receipt := body },
        format)

end Near.Node.Apply
