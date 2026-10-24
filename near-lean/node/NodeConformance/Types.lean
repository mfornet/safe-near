import Std.Data.HashMap
import NodeConformance.Runner
import NodeConformance.Signatures
import NodeConformance.Chain
import NodeConformance.Stateless
import NodeConformance.Epoch
import NodeConformance.Sync
import NearNode.Protocol
import NearNode.Primitives

/-!
`node-conformance-types [DIR [SIGNATURES]]`: check the Borsh codecs of every `near-primitives` type
against the fixtures written by `tools/node-conformance` (default `near-lean/node/fixtures/types`),
and verify with `NearCrypto` the Ed25519, secp256k1 and ML-DSA-65 signatures that the fixtures carry, using the keys in
`SIGNATURES` (default `DIR/../signatures.jsonl`; see `NodeConformance.Signatures`).
-/

open Lean Near.Node Near.Node.Conformance Near.Node.Borsh

@[instance_reducible]
private def bytesMap : Codec (Array (ByteArray × ByteArray)) :=
  .btreeMap compareBytes inferInstance inferInstance

private def hashOf (h : CryptoHash) : List (String × ByteArray) :=
  [("hash", h.bytes)]

/-- Every fixture type with its check. -/
def registry : List (String × Check) :=
  chainRegistry ++ statelessRegistry ++ epochRegistry ++ syncRegistry ++
    [("Bool", check Bool), ("U128", check U128), ("String", check String),
      ("Bytes", check ByteArray), ("OptionU64", check (Option UInt64)),
      ("BytesMap", @check _ bytesMap fun _ => []), ("CryptoHash", check CryptoHash),
      ("AccountId", check AccountId), ("PublicKey", check PublicKey),
      ("Signature", check Signature), ("AccessKey", check AccessKey),
      ("AccessKeyPermission", check AccessKeyPermission),
      ("FunctionCallPermission", check FunctionCallPermission),
      ("AccountContract", check AccountContract),
      ("GlobalContractIdentifier", check GlobalContractIdentifier),
      ("DeterministicAccountStateInit", check DeterministicAccountStateInit),
      ("Account", check Account), ("Action", check Action), ("NonDelegateAction", check BaseAction),
      ("SignedDelegateAction",
        check SignedDelegateAction fun a => hashOf a.delegateAction.signingHash),
      ("VersionedSignedDelegateAction",
        check VersionedSignedDelegateAction fun a => hashOf a.delegateAction.signingHash),
      ("TransactionNonce", check TransactionNonce),
      ("Transaction", check Transaction fun t => hashOf t.hash),
      ("TransactionV0", check TransactionV0), ("TransactionV1", check TransactionV1),
      ("SignedTransaction", check SignedTransaction fun t => hashOf t.hash),
      ("Receipt", check Receipt), ("ReceiptEnum", check ReceiptEnum),
      ("ActionReceipt", check ActionReceipt), ("ActionReceiptV2", check ActionReceiptV2),
      ("DataReceipt", check DataReceipt), ("DataReceiver", check DataReceiver),
      ("GlobalContractDistributionReceipt", check GlobalContractDistributionReceipt),
      ("StateStoredReceipt", check StateStoredReceipt),
      ("ReceiptOrStateStoredReceipt", check ReceiptOrStateStoredReceipt),
      ("TrieQueueIndices", check TrieQueueIndices),
      ("BufferedReceiptIndices", check BufferedReceiptIndices),
      ("PromiseYieldTimeout", check PromiseYieldTimeout), ("ReceivedData", check ReceivedData),
      ("TxExecutionError", check TxExecutionError), ("InvalidTxError", check InvalidTxError),
      ("ActionErrorKind", check ActionErrorKind),
      ("InvalidAccessKeyError", check InvalidAccessKeyError),
      ("ActionsValidationError", check ActionsValidationError),
      ("ReceiptValidationError", check ReceiptValidationError),
      ("StorageError", check StorageError), ("FunctionCallError", check FunctionCallError),
      ("CompilationError", check CompilationError), ("HostError", check HostError),
      ("PrepareError", check PrepareError), ("WasmTrap", check WasmTrap),
      ("MethodResolveError", check MethodResolveError), ("ActionError", check ActionError),
      ("MissingTrieValue", check MissingTrieValue), ("ProfileDataV2", check ProfileDataV2),
      ("ProfileDataV3", check ProfileDataV3), ("ExecutionMetadata", check ExecutionMetadata),
      ("ExecutionStatus", check ExecutionStatus),
      ("PartialExecutionOutcome", check PartialExecutionOutcome),
      ("ExecutionOutcome", check ExecutionOutcome),
      ("ExecutionOutcomeWithId",
        check ExecutionOutcomeWithId fun o =>
          [("hash", o.leafHash.bytes),
            ("hashes", o.toHashes.foldl (fun b h => b.append h.bytes) ByteArray.empty)]),
      ("ExecutionOutcomeWithIdAndProof", check ExecutionOutcomeWithIdAndProof),
      ("ExecutionOutcomeWithProof", check ExecutionOutcomeWithProof),
      ("MerklePathItem", check MerklePathItem)]

/-- Counts per type from the manifest. -/
private def manifestCounts (j : Json) : Except String (List (String × Nat × Nat)) := do
  let types ← (← j.getObjVal? "types").getObj?
  types.toList.mapM fun (k, v) => do
      pure (k, ← v.getObjValAs? Nat "accept", ← v.getObjValAs? Nat "reject")

private def preview (b : ByteArray) : String :=
  let h := toHex b
  if h.length > 96 then (h.take 96).toString ++ s!"... ({b.size} bytes)" else h

/-- Byte strings of up to four bytes over the boundary bytes of UTF-8 on which the reference
validator and Lean's disagree if either is wrong. -/
private def utf8Disagreements : Nat :=
  let alphabet : List UInt8 :=
    [0x00, 0x7F, 0x80, 0x8F, 0x90, 0x9F, 0xA0, 0xBF, 0xC0, 0xC1, 0xC2, 0xDF, 0xE0, 0xED, 0xEF, 0xF0,
      0xF4, 0xF5, 0xFF]
  let rec words : Nat → List (List UInt8)
    | 0 => [[]]
    | n + 1 => [] :: ((words n).flatMap fun w => alphabet.map (· :: w))
  (words 4).foldl (init := 0) fun n w =>
    if Spec.utf8Valid w == (ByteArray.mk w.toArray).validateUTF8 then n else n + 1

def main (args : List String) : IO UInt32 := do
  let dir : System.FilePath := (args.head?.getD "near-lean/node/fixtures/types")
  let manifest ←
    match Json.parse (← IO.FS.readFile (dir / "manifest.json")) with
    | .ok j =>
      pure j
    | .error e =>
      throw (IO.userError s!"manifest.json: {e}")
  let mut failures := 0
  let pv := (manifest.getObjValAs? Nat "protocol_version").toOption
  let rel := (manifest.getObjValAs? String "nearcore_release").toOption
  if pv != some protocolVersion || rel != some nearcoreRelease then
    IO.eprintln
        s!"fixtures are for protocol {pv} / nearcore {rel}, the node implements \
      {protocolVersion} / {nearcoreRelease}"
    failures := failures + 1
  let counts ←
    match manifestCounts manifest with
    | .ok c =>
      pure c
    | .error e =>
      throw (IO.userError s!"manifest.json: {e}")
  for (k, _, _) in counts do
    if (registry.lookup k).isNone then
      IO.eprintln s!"{k}: fixtures exist but the Lean registry has no entry"
      failures := failures + 1
  let sigPath : System.FilePath :=
    args[1]?.map System.FilePath.mk |>.getD (dir / ".." / "signatures.jsonl")
  let records ← loadSidecars sigPath
  let sidecars : Std.HashMap String Sidecar := Std.HashMap.ofList records
  let pool : Std.HashMap ByteArray Recorded :=
    records.foldl (init := {}) fun m (_, side) => side.sigs.foldl (fun m r => m.insert r.sig r) m
  let seen ← IO.mkRef ({} : Seen)
  let mut matched := 0
  let mut recordedTotal := 0
  let mut typedTotal := 0
  let mut secpTotal := 0
  let mut mldsaTotal := 0
  let utf8 := utf8Disagreements
  if utf8 != 0 then
    IO.eprintln s!"Spec.utf8Valid and ByteArray.validateUTF8 disagree on {utf8} short inputs"
    failures := failures + 1
  IO.println s!"fixtures: nearcore {nearcoreRelease}, protocol {protocolVersion}, {dir}"
  let mut totalAccept := 0
  let mut totalReject := 0
  for (name, run) in registry do
    let some (_, wantAccept, wantReject) := counts.find? (·.1 == name)
      |
      IO.eprintln s!"{name}: no fixtures in the manifest";
      failures := failures + 1;
      continue
    let text ← IO.FS.readFile (dir / s!"{name}.jsonl")
    let mut accept := 0
    let mut reject := 0
    let mut bad : Array String := #[]
    let mut badCount := 0
    let mut recorded := 0
    let mut typed := 0
    let mut secp := 0
    let mut mldsa := 0
    let mut index := 0
    for raw in text.splitOn "\n" do
      if raw.isEmpty then
        continue
      index := index + 1
      match parseLine raw with
      | .error e =>
        badCount := badCount + 1
        bad := bad.push s!"  unparsable line: {e}"
      | .ok line =>
        if line.reject then
          reject := reject + 1
        else
          accept := accept + 1
        if let some msg := run line then
          badCount := badCount + 1
          if bad.size < 3 then
            bad := bad.push s!"  {line.name}: {msg}\n    borsh {preview line.borsh}"
        if !line.reject then
          if let some side := sidecars[s!"{name}#{index - 1}"]? then
            matched := matched + 1
            let o ← verifyLine seen pool (signedRegistry.lookup name) line.borsh side
            recorded := recorded + o.recorded
            typed := typed + o.typed
            secp := secp + o.secp
            mldsa := mldsa + o.mldsa
            for f in o.failures do
              badCount := badCount + 1
              if bad.size < 3 then
                bad := bad.push s!"  {line.name}: signature: {f}"
    if accept != wantAccept || reject != wantReject then
      bad :=
        bad.push
          s!"  manifest says {wantAccept} accept / {wantReject} reject, file has \
        {accept} / {reject}"
      badCount := badCount + 1
    totalAccept := totalAccept + accept
    totalReject := totalReject + reject
    recordedTotal := recordedTotal + recorded
    typedTotal := typedTotal + typed
    secpTotal := secpTotal + secp
    mldsaTotal := mldsaTotal + mldsa
    let sigs :=
      if recorded + typed == 0 then ""
      else
        s!", signatures {recorded} recorded and {typed} typed verified ({secp} secp256k1, {mldsa} ML-DSA-65)"
    let status := (if badCount == 0 then "ok" else s!"FAILED ({badCount})") ++ sigs
    IO.println s!"{name}: accept {accept}, reject {reject}: {status}"
    for b in bad do
      IO.println b
    failures := failures + badCount
  if matched != sidecars.size then
    IO.eprintln s!"{sidecars.size} signature records, {matched} matched a fixture line"
    failures := failures + 1
  IO.println
      s!"Ed25519, secp256k1 and ML-DSA-65: {recordedTotal} recorded and {typedTotal} typed signature \
    checks passed, {secpTotal} of them secp256k1 and {mldsaTotal} ML-DSA-65 (verdicts as recorded; \
    {sidecars.size} lines with records)"
  IO.println
      s!"{registry.length} types, {totalAccept} accepted and {totalReject} rejected inputs, \
    {failures} failures"
  return if failures == 0 then 0 else 1
