import NearNode.Chain.Model

/-!
# A shard's trie entries as the runtime's state

The inverse of `QueueEncoding.encode` plus the shard columns: every entry of a shard's trie is
read through `TrieKey` and the Borsh codecs and becomes a part of the model state, of the
`QueueEncoding.Context` that records the native identity of the model's ids, or of the scheduler
and buffer columns that `ChainReplay.ShardChunk` keeps. Columns the model has no place for are an
error. The order of the entries decides only the numbering of the ids.
-/

namespace Near.Node.Apply

open Near.Node Near.Node.Borsh

/-- A shard's state, decoded. -/
structure Decoded where
  state : Near.ChainState
  /-- The delayed queue header and the way each queued receipt is stored. -/
  delayed : Option Near.QueueEncoding.Delayed
  /-- The value of the bandwidth scheduler state column. -/
  scheduler : Option (List UInt8)
  /-- The entries of the outgoing buffer columns (13, 14, 16, 17). -/
  buffers : List (List UInt8 × List UInt8)

private def decode (α : Type) [Codec α] (what : String) (b : ByteArray) : M α :=
  match Codec.decodeAll (α := α) b with
  | .ok a => pure a
  | .error e => fail s!"{what} does not decode: {repr e}"

private def handleKey : PublicKeyHandle → M (List UInt8)
  | .ed25519 k => pure (0 :: k.toList)
  | .secp256k1 k => pure (1 :: k.toList)
  | .mldsa65 _ => fail "ML-DSA access key"

private def globalCodeId : GlobalContractCodeIdentifier → Wasm.GlobalContractId
  | .codeHash h => .codeHash h.bytes.toList
  | .accountId a => .accountId a.val.toUTF8.toList

private def le (b : ByteArray) : Nat :=
  b.toList.foldr (fun x acc => acc * 256 + x.toNat) 0

/-- Decode the complete entries of a shard (in any order; trie order gives a stable numbering).

With `proved` the entries are what a state witness proves (`Trie::from_recorded_storage`): the nodes and values a
chunk read, without the contract code (`ExcludeContractCodeFromStateWitness`). An account whose code is not among the
entries has it from the cache, by the hash its record names; code that the cache lacks is an error that says which. -/
def decodeState (entries : Array (ByteArray × ByteArray)) (proved : Bool := false) : M Decoded := do
  let mut accounts : Array (String × Account) := #[]
  let mut keys : List ((String × List UInt8) × Near.AccessKey) := []
  let mut gasNonces : List ((String × List UInt8 × Nat) × Nat) := []
  let mut storage : Array (String × Array (List UInt8 × List UInt8)) := #[]
  let mut contracts : Std.HashMap String String := {}
  let mut postponed : List (Nat × Near.Receipt) := []
  let mut counts : List (Nat × Nat) := []
  let mut byData : List (Nat × Nat) := []
  let mut received : List (Nat × Option (List UInt8)) := []
  let mut delayedRows : Array (UInt64 × ByteArray) := #[]
  let mut header : Option ByteArray := none
  let mut scheduler : Option (List UInt8) := none
  let mut buffers : List (List UInt8 × List UInt8) := []
  -- the main columns
  for (k, v) in entries do
    let some key := TrieKey.parse? k | fail s!"unparsable trie key {k.toList}"
    match key with
    | .account a =>
      accounts := accounts.push (a.val, ← decode Account "account" v)
    | .contractCode a =>
      let c ← code v
      contracts := contracts.insert a.val c.code.hash
    | .accessKey a h =>
      let pk ← handleKey h
      keys := keys ++ [((a.val, pk), accessKey (← decode AccessKey "access key" v))]
    | .gasKeyNonce a h i =>
      gasNonces := gasNonces ++ [((a.val, ← handleKey h, i.toNat), le v)]
    | .contractData a name =>
      match storage.findIdx? (·.1 == a.val) with
      | some i =>
        storage := storage.modify i fun (n, rows) => (n, rows.push (name.toList, v.toList))
      | none =>
        storage := storage.push (a.val, #[(name.toList, v.toList)])
    | .postponedReceipt _ _ =>
      let (r, _) ← receipt (← decode Receipt "postponed receipt" v)
      postponed := postponed ++ [(r.receiptId, r)]
    | .postponedReceiptId r d =>
      setReceiver d r
      let id ← dataId d
      byData := byData ++ [(id, ← receiptId (← decode CryptoHash "postponed receipt id" v))]
    | .pendingDataCount _ rid =>
      counts := counts ++ [(← receiptId rid, le v)]
    | .receivedData r d =>
      setReceiver d r
      let data ← decode ReceivedData "received data" v
      received := received ++ [(← dataId d, data.data.map (·.toList))]
    | .delayedReceipt i =>
      delayedRows := delayedRows.push (i, v)
    | .delayedReceiptIndices =>
      header := some v
    | .bandwidthSchedulerState =>
      scheduler := some v.toList
    | .bufferedReceiptIndices | .bufferedReceipt .. | .bufferedReceiptGroupsQueueData _ |
      .bufferedReceiptGroupsQueueItem .. =>
      buffers := buffers ++ [(k.toList, v.toList)]
    | .promiseYieldIndices | .promiseYieldTimeout _ | .promiseYieldReceipt .. |
      .promiseYieldStatus .. | .globalContractCode _ | .globalContractNonce _ =>
      pure ()
    | .yieldIdToDataId .. | .dataIdToYieldId .. =>
      fail "pre-state column yield id mapping"
  -- the yield queue and the global contracts
  let mut globalCode : List (Wasm.GlobalContractId × Near.ContractCode) := []
  let mut globalNonces : List (Wasm.GlobalContractId × Nat) := []
  let mut yieldIndices : Option (Nat × Nat) := none
  let mut yieldTimeouts : List (Nat × Near.YieldTimeout) := []
  let mut yieldReceipts : List ((String × List UInt8) × Near.Receipt) := []
  let mut yieldStatus : List ((String × List UInt8) × Near.YieldStatus) := []
  for (k, v) in entries do
    let some key := TrieKey.parse? k | fail "unparsable trie key"
    match key with
    | .promiseYieldIndices =>
      let i ← decode TrieQueueIndices "yield indices" v
      yieldIndices := some (i.firstIndex.toNat, i.nextAvailableIndex.toNat)
    | .promiseYieldTimeout i =>
      let t ← decode PromiseYieldTimeout "yield timeout" v
      yieldTimeouts :=
        yieldTimeouts ++
          [(i.toNat,
              { account := t.accountId.val, dataId := t.dataId.bytes.toList,
                expiresAt := t.expiresAt.toNat })]
    | .promiseYieldReceipt a d =>
      let (r, _) ← receipt (← decode Receipt "yield receipt" v)
      yieldReceipts := yieldReceipts ++ [((a.val, d.bytes.toList), r)]
    | .promiseYieldStatus a d =>
      let status : Near.YieldStatus := if v.get! 0 == 0 then .yielded else .resumeInitiated
      yieldStatus := yieldStatus ++ [((a.val, d.bytes.toList), status)]
    | .globalContractCode id =>
      globalCode := globalCode ++ [(globalCodeId id, (← code v).code)]
    | .globalContractNonce id =>
      globalNonces := globalNonces ++ [(globalCodeId id, le v)]
    | _ =>
      pure ()
  -- the delayed receipt queue
  let mut delayed : List Near.Receipt := []
  let mut forms : List Near.QueueEncoding.StorageForm := []
  let mut queue : Option Near.QueueEncoding.Delayed := none
  match header with
  | none =>
    unless delayedRows.isEmpty do
      fail "delayed receipts without a queue header"
  | some h =>
    let i ← decode TrieQueueIndices "delayed receipt indices" h
    let sorted := delayedRows.qsort fun a b => a.1 < b.1
    unless
      sorted.map (·.1.toNat) ==
        (Array.range (i.nextAvailableIndex.toNat - i.firstIndex.toNat)).map
          (· + i.firstIndex.toNat) do
      fail "pre-state delayed receipt queue header disagrees with its entries"
    for (_, v) in sorted do
      match ← decode ReceiptOrStateStoredReceipt "delayed receipt" v with
      | .receipt r =>
        delayed := delayed ++ [(← receipt r).1]
        forms := forms ++ [.receipt]
      | .stateStored (.v0 r m) =>
        delayed := delayed ++ [(← receipt r).1]
        forms := forms ++ [.storedV0 m.congestionGas.toNat m.congestionSize.toNat]
      | .stateStored (.v1 r m) =>
        delayed := delayed ++ [(← receipt r).1]
        forms := forms ++ [.storedV1 m.congestionGas.toNat m.congestionSize.toNat]
    queue := some { firstIndex := i.firstIndex.toNat, forms }
  -- accounts with their contracts
  let mut rows : List (String × Near.Account) := []
  for (name, account) in accounts do
    let hash? : Option CryptoHash :=
      match account with
      | .v1 _ _ h _ => if h == CryptoHash.zero then none else some h
      | .v2 _ _ _ (.local h) => some h
      | .v2 .. => none
    let label? := hash?.map fun h => Near.StateEncoding.base58 h.bytes.toList
    unless contracts[name]? == label? do
      match proved, contracts[name]?, label? with
      | true, none, some l =>
        -- the code is not in the witness: the node has it by hash, or must ask for it
        unless (← get).cache.byLabel.contains l do
          fail s!"missing contract code {l}"
        modify fun st => { st with used := if st.used.contains l then st.used else st.used.push l }
      | _, _, _ =>
        fail "account code hash without a matching contract record"
    let cache := (← get).cache
    let model ← accountRow account
    let model :=
      match label? with
      | some l => { model with code := (cache.byLabel[l]?).map (·.code) }
      | none => model
    rows := rows ++ [(name, model)]
  let state : Near.ChainState :=
    { accounts := rows, accessKeys := keys,
      storage := (storage.qsort fun a b => a.1 < b.1).toList.map fun (n, r) => (n, r.toList),
      postponed, pendingDataCount := counts, postponedByData := byData, receivedData := received,
      delayed, globalCode, globalNonces, gasKeyNonces := gasNonces, yieldIndices, yieldTimeouts,
      yieldReceipts, yieldStatus }
  return { state, delayed := queue, scheduler, buffers }
where accountRow (account : Account) : M Near.Account := do
    let base (amount locked : Balance) (usage : StorageUsage) : Near.Account :=
      { amount := amount.val, locked := locked.val, storageUsage := usage.toNat }
    match account with
    | .v1 amount locked _ usage =>
      pure (base amount locked usage)
    | .v2 amount locked usage contract =>
      match contract with
      | .none | .local _ =>
        pure (base amount locked usage |> fun a => { a with versionTwo := true })
      | .global h =>
        pure
            { base amount locked usage with
              global := some (.codeHash h.bytes.toList), versionTwo := true }
      | .globalByAccount id =>
        pure
            { base amount locked usage with
              global := some (.accountId id.val.toUTF8.toList), versionTwo := true }

end Near.Node.Apply
