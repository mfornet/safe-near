import Lean.Data.Json
import Std.Data.HashMap
import Std.Data.HashSet
import NodeConformance.Runner
import NearNode.Primitives
import NearCrypto

/-!
# Ed25519 and secp256k1 signatures in the fixtures

The oracle signs with real ED25519 and SECP256K1 keys, but the Borsh fixtures do not carry the key of an
approval, a block header, an endorsement and so on. `tools/node-conformance` therefore writes
`signatures.jsonl` beside the fixtures: for each accepted line that was built with signatures, the
signatures it made itself (`sigs`: signature, public key, message; 64 and 32 bytes for ED25519, 65 and
64 for SECP256K1) and the keys of the validator signers whose signatures nearcore's constructors
make (`signers`, ED25519). Two checks verify them in Lean with `NearCrypto.ed25519Verify` and
`NearCrypto.secp256k1Verify`, by the lengths of the key and the signature (ML-DSA is skipped):

* **Recorded.** Every recorded signature that occurs in the line's Borsh bytes verifies under its key
  and message.
* **Typed.** For the types in `signedRegistry`, the signatures of the decoded value and the bytes
  each covers are computed from the value (the transaction hash, the block hash, the chunk hash, the
  Borsh of an `inner`, ...) and must verify under the key of the transaction, of the recorded
  signature, or of one of the line's signers. A recorded message must equal the computed one.

Lines without a record (the mutated ones, whose signatures are no longer valid) are not checked. A
value built once and used in several lines (a chunk header in blocks) has its signatures recorded
with the first line; the typed check looks signatures up in the records of all lines.
-/

namespace Near.Node.Conformance

open Lean Borsh

/-- A signature of a decoded value, the bytes it covers and, when the value holds the signer's key,
that key. -/
structure Signed where
  signature : Signature
  message : ByteArray
  key : Option PublicKey := none

/-- A signature the oracle made. -/
structure Recorded where
  sig : ByteArray
  key : ByteArray
  msg : ByteArray

/-- What the oracle recorded for one line. -/
structure Sidecar where
  sigs : List Recorded
  signers : List ByteArray

private def hexField (j : Json) (k : String) : Except String ByteArray := do
  match ofHex (← j.getObjValAs? String k) with
  | some b =>
    pure b
  | none =>
    throw s!"{k} is not hex"

/-- The records of `signatures.jsonl` by `type#line` (names repeat within a file, positions do not). -/
def loadSidecars (path : System.FilePath) : IO (List (String × Sidecar)) := do
  let text ← IO.FS.readFile path
  let mut out := #[]
  for raw in text.splitOn "\n" do
    if raw.isEmpty then
      continue
    let r : Except String (String × Sidecar) := do
      let j ← Json.parse raw
      let key := s!"{← j.getObjValAs? String "type"}#{← j.getObjValAs? Nat "line"}"
      let sigs ←
        (← j.getObjValAs? (Array Json) "sigs").toList.mapM fun s => do
            pure
                { sig := ← hexField s "sig", key := ← hexField s "public",
                  msg := ← hexField s "msg" : Recorded }
      let signers ←
        (← j.getObjValAs? (Array String) "signers").toList.mapM fun s =>
            match ofHex s with
            | some b => pure b
            | none => throw "signer is not hex"
      pure (key, { sigs, signers })
    match r with
    | .ok e =>
      out := out.push e
    | .error e =>
      throw (IO.userError s!"{path}: {e}")
  pure out.toList

/-- Whether `needle` occurs in `hay`. -/
def containsBytes (hay needle : ByteArray) : Bool :=
  if needle.size == 0 || hay.size < needle.size then needle.size == 0
  else
    (List.range (hay.size - needle.size + 1)).any fun i =>
      hay.get! i == needle.get! 0 && (hay.extract i (i + needle.size)) == needle

/-! ### The typed extractors -/

private def txKey : Transaction → PublicKey
  | .v0 t => t.publicKey
  | .v1 t => t.publicKey

private def one (s : Signature) (m : ByteArray) (k : Option PublicKey := none) : List Signed :=
  [⟨s, m, k⟩]

private def headerSigned (h : BlockHeader) : List Signed :=
  one h.signature h.hash.bytes

private def chunkSigned (h : ShardChunkHeader) : List Signed :=
  one h.signature h.chunkHash.hash.bytes

private def blockSigned (b : Block) : List Signed :=
  headerSigned b.header ++ b.chunks.toList.flatMap chunkSigned

private def typed (α : Type) [Codec α] (f : α → List Signed) : ByteArray → Option (List Signed) :=
  fun b => (Codec.decodeAll (α := α) b).toOption.map f

/-- The fixture types whose signatures are recomputed from the decoded value. -/
def signedRegistry : List (String × (ByteArray → Option (List Signed))) :=
  [("SignedTransaction",
      typed SignedTransaction fun t => one t.signature t.hash.bytes (some (txKey t.transaction))),
    ("SignedDelegateAction",
      typed SignedDelegateAction fun a =>
        one a.signature a.delegateAction.signingHash.bytes (some a.delegateAction.publicKey)),
    ("VersionedSignedDelegateAction",
      typed VersionedSignedDelegateAction fun a =>
        match a.delegateAction with
        | .v2 d => one a.signature a.delegateAction.signingHash.bytes (some d.publicKey)),
    ("Approval", typed Approval fun a => one a.signature a.sigData),
    ("ApprovalMessage", typed ApprovalMessage fun m => one m.approval.signature m.approval.sigData),
    ("BlockHeader", typed BlockHeader headerSigned),
    ("BlockHeaderV1", typed BlockHeaderV1 fun h => headerSigned (.v1 h)),
    ("BlockHeaderV2", typed BlockHeaderV2 fun h => headerSigned (.v2 h)),
    ("BlockHeaderV3", typed BlockHeaderV3 fun h => headerSigned (.v3 h)),
    ("BlockHeaderV4", typed BlockHeaderV4 fun h => headerSigned (.v4 h)),
    ("BlockHeaderV5", typed BlockHeaderV5 fun h => headerSigned (.v5 h)),
    ("BlockHeaderV6", typed BlockHeaderV6 fun h => headerSigned (.v6 h)),
    ("BlockHeaderV7", typed BlockHeaderV7 fun h => headerSigned (.v7 h)),
    ("ShardChunkHeader", typed ShardChunkHeader chunkSigned),
    ("ShardChunkHeaderV1", typed ShardChunkHeaderV1 fun h => chunkSigned (.v1 h)),
    ("ShardChunkHeaderV2", typed ShardChunkHeaderV2 fun h => chunkSigned (.v2 h)),
    ("ShardChunkHeaderV3", typed ShardChunkHeaderV3 fun h => chunkSigned (.v3 h)),
    ("Block", typed Block blockSigned), ("BlockV1", typed BlockV1 fun b => blockSigned (.v1 b)),
    ("BlockV2", typed BlockV2 fun b => blockSigned (.v2 b)),
    ("BlockV3", typed BlockV3 fun b => blockSigned (.v3 b)),
    ("BlockV4", typed BlockV4 fun b => blockSigned (.v4 b)),
    ("ChunkEndorsement",
      typed ChunkEndorsement fun
        | e@(.v2 v) =>
          one v.signature e.signingBytes ++ one v.metadataSignature e.metadataSigningBytes),
    ("PartialEncodedStateWitness",
      typed PartialEncodedStateWitness fun w => one w.signature (Codec.encode w.inner)),
    ("PartialEncodedStateWitnessV2",
      typed PartialEncodedStateWitnessV2 fun w => one w.signature (Codec.encode w.inner)),
    ("VersionedPartialEncodedStateWitness",
      typed VersionedPartialEncodedStateWitness fun w =>
        match w with
        | .v1 v => one v.signature w.signingBytes
        | .v2 v => one v.signature w.signingBytes),
    ("ChunkContractAccesses",
      typed ChunkContractAccesses fun a =>
        match a with
        | .v1 v => one v.signature a.signingBytes),
    ("ContractCodeRequest",
      typed ContractCodeRequest fun r =>
        match r with
        | .v1 v => one v.signature r.signingBytes),
    ("ContractCodeResponseV2",
      typed ContractCodeResponseV2 fun r => one r.signature (Codec.encode r.inner)),
    ("ContractCodeResponse",
      typed ContractCodeResponse fun
        | .v1 _ => []
        | .v2 r => one r.signature (Codec.encode r.inner)),
    ("PartialEncodedContractDeploys",
      typed PartialEncodedContractDeploys fun d =>
        match d with
        | .v1 v => one v.signature d.signingBytes),
    ("SpiceChunkContractAccesses",
      typed SpiceChunkContractAccesses fun a => one a.signature (Codec.encode a.inner)),
    ("SpiceContractCodeRequest",
      typed SpiceContractCodeRequest fun r => one r.signature (Codec.encode r.inner)),
    ("SpicePartialData", typed SpicePartialData fun d => one d.signature d.inner.signingBytes),
    ("AnnounceAccount", typed AnnounceAccount fun a => one a.signature a.hash.bytes)]

/-! ### Verification -/

/-- What was checked on one line; `secp` counts the SECP256K1 checks among `recorded` and `typed`. -/
structure Outcome where
  recorded : Nat := 0
  typed : Nat := 0
  secp : Nat := 0
  failures : List String := []

/-- The per-line cache of verified `(signature, key, message)` triples. -/
abbrev Seen :=
  Std.HashSet String

private def tripleKey (sig pk msg : ByteArray) : String :=
  s!"{toHex sig}:{toHex pk}:{toHex msg}"

/-- Verify under the scheme the lengths select: 32-byte key and 64-byte signature for ED25519,
64 and 65 for SECP256K1. -/
def verifyAny (pk msg sig : ByteArray) : Bool :=
  if pk.size == 32 && sig.size == 64 then NearCrypto.ed25519Verify pk msg sig
  else if pk.size == 64 && sig.size == 65 then NearCrypto.secp256k1Verify pk msg sig else false

/-- Verify, remembering the triples that already passed (a block's header occurs in many lines). -/
private def verifyCached (seen : IO.Ref Seen) (pk msg sig : ByteArray) : IO Bool := do
  let k := tripleKey sig pk msg
  if (← seen.get).contains k then
    return true
  let ok := verifyAny pk msg sig
  if ok then
    seen.modify (·.insert k)
  return ok

/-- Check one accepted line against its record. -/
def verifyLine (seen : IO.Ref Seen) (pool : Std.HashMap ByteArray Recorded)
    (extract : Option (ByteArray → Option (List Signed))) (borsh : ByteArray) (side : Sidecar) :
    IO Outcome := do
  let mut out : Outcome := {}
  for r in side.sigs do
    if containsBytes borsh r.sig then
      if ← verifyCached seen r.key r.msg r.sig then
        out :=
          { out with
            recorded := out.recorded + 1
            secp := out.secp + if r.sig.size == 65 then 1 else 0 }
      else
        out :=
          { out with
            failures := s!"recorded signature {toHex r.sig} does not verify" :: out.failures }
  if let some extract := extract then
    match extract borsh with
    | none =>
      out := { out with failures := "the value did not decode" :: out.failures }
    | some signed =>
      for s in signed do
        let sig ←
          match s.signature with
          | .ed25519 sig =>
            pure sig
          | .secp256k1 sig =>
            pure sig
          | .mldsa65 _ =>
            continue
        let isSecp := if sig.size == 65 then 1 else 0
        let tag := toHex sig
        let tag := (tag.take 12).toString
        let keyInValue ←
          match s.key with
          | some (.ed25519 pk) =>
            pure (some pk)
          | some (.secp256k1 pk) =>
            pure (some pk)
          | some (.mldsa65 _) =>
            continue
          | none =>
            pure none
        match keyInValue with
        | some pk =>
          if ← verifyCached seen pk s.message sig then
            out :=
              { out with
                typed := out.typed + 1, secp := out.secp + isSecp }
          else
            out :=
              { out with
                failures :=
                  s!"signature {tag} does not verify under the key in the value" :: out.failures }
        | none =>
          match (side.sigs.find? (·.sig == sig)).orElse fun _ => pool[sig]? with
          | some r =>
            if r.msg != s.message then
              out :=
                { out with
                  failures :=
                    s!"signature {tag}: the oracle signed {toHex r.msg}, the value computes {toHex s.message}" ::
                      out.failures }
            else if ← verifyCached seen r.key s.message sig then
              out :=
                { out with
                  typed := out.typed + 1, secp := out.secp + isSecp }
            else
              out :=
                { out with
                  failures :=
                    s!"signature {tag} does not verify under the recorded key" :: out.failures }
          | none =>
            let mut ok := false
            for pk in side.signers do
              if !ok && (← verifyCached seen pk s.message sig) then
                ok := true
            if ok then
              out :=
                { out with
                  typed := out.typed + 1, secp := out.secp + isSecp }
            else
              out :=
                { out with
                  failures :=
                    s!"signature {tag} verifies under none of {side.signers.length} recorded signers" ::
                      out.failures }
  pure out

end Near.Node.Conformance
