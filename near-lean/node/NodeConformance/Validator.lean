import Lean.Data.Json
import NodeConformance.Runner
import NearNode.Validator.ReedSolomon
import NearNode.Validator.Chunk
import NearNode.Validator.Messages
import NearNode.Validator.Witness
import NearNode.Validator.Block
import NearNode.Zstd

/-!
`node-conformance-validator [DIR]`: the building blocks of a validator against the fixtures that
`tools/node-conformance/src/validator_fixtures.rs` writes with the pinned crates
(default `near-lean/node/fixtures/validator`).

* `gf`, `rs-*`: Reed-Solomon over GF(2^8) (`reed-solomon-erasure` 6.0.0, `near-primitives`
  `reed_solomon.rs`): the field tables, the number of data parts and the part length, the parity
  of random data, reconstruction from every erasure pattern and its errors, and the wrapper that
  encodes and decodes Borsh bytes.
-/

open Lean Near.Node Near.Node.Conformance Near.Node.ReedSolomon Near.Node.Validator Near.Node.Borsh

namespace Near.Node.ValidatorConformance

def lines (path : System.FilePath) : IO (Array Json) := do
  let text ← IO.FS.readFile path
  let mut out := #[]
  for l in text.splitOn "\n" do
    if l.trimAscii.isEmpty then
      continue
    match Json.parse l with
    | .ok j =>
      out := out.push j
    | .error e =>
      throw (IO.userError s!"{path}: {e}")
  pure out

def bytesOf (j : Json) (k : String) : Except String ByteArray := do
  match ofHex (← j.getObjValAs? String k) with
  | some b =>
    pure b
  | none =>
    throw s!"{k} is not hex"

def hexOf (j : Json) : Except String ByteArray := do
  match ofHex (← j.getStr?) with
  | some b =>
    pure b
  | none =>
    throw "not hex"

def hexList (j : Json) (k : String) : Except String (Array ByteArray) := do
  (← (← j.getObjVal? k).getArr?).mapM hexOf

def optHexList (j : Json) (k : String) : Except String (Array (Option ByteArray)) := do
  (← (← j.getObjVal? k).getArr?).mapM fun x =>
      match x with
      | .null => pure none
      | v => do
        pure (some (← hexOf v))

def natOf (j : Json) (k : String) : Except String Nat :=
  j.getObjValAs? Nat k

def strOpt (j : Json) (k : String) : Option String :=
  match j.getObjVal? k with
  | .ok .null => none
  | .ok (.str s) => some s
  | _ => none

structure Tally where
  checks : Nat := 0
  failures : Array String := #[]

def Tally.ok (t : Tally) (good : Bool) (what : String) : Tally :=
  { t with
    checks := t.checks + 1, failures := if good then t.failures else t.failures.push what }

def ofExcept' (r : Except String α) : IO α :=
  IO.ofExcept r

/-! ### Reed-Solomon -/

def gfChecks (dir : System.FilePath) (t : Tally) : IO Tally := do
  let mut t := t
  for row in ← lines (dir / "gf.jsonl") do
    let mulT ← ofExcept' (bytesOf row "mul")
    let divT ← ofExcept' (bytesOf row "div")
    let expT ← ofExcept' (bytesOf row "exp")
    let expMax ← ofExcept' (natOf row "expMax")
    let mut bad := 0
    for a in [0:256] do
      for b in [0:256] do
        let m := Gf.mul a.toUInt8 b.toUInt8
        if m != mulT.get! (a * 256 + b) || m != Gf.mulSpec a.toUInt8 b.toUInt8 then
          bad := bad + 1
        if b ≥ 1 then
          if Gf.div a.toUInt8 b.toUInt8 != divT.get! (a * 255 + (b - 1)) then
            bad := bad + 1
      for n in [0:expMax + 1] do
        if Gf.exp a.toUInt8 n != expT.get! (a * (expMax + 1) + n) then
          bad := bad + 1
    t := t.ok (bad == 0) s!"gf: {bad} of the products, quotients and powers differ"
  pure t

def rsChecks (dir : System.FilePath) (t : Tally) : IO Tally := do
  let mut t := t
  -- number of data parts, part length
  for row in ← lines (dir / "rs-parts.jsonl") do
    let total ← ofExcept' (natOf row "total")
    let want ← ofExcept' (natOf row "dataParts")
    let got := numDataParts total 0.6
    t := t.ok (got == want) s!"rs-parts: total {total}: {got}, nearcore {want}"
  for row in ← lines (dir / "rs-part-length.jsonl") do
    let len ← ofExcept' (natOf row "length")
    let k ← ofExcept' (natOf row "dataParts")
    let want ← ofExcept' (natOf row "partLength")
    t := t.ok (partLength len k == want) s!"rs-part-length {len}/{k}"
  -- construction
  for row in ← lines (dir / "rs-new.jsonl") do
    let d ← ofExcept' (natOf row "data")
    let p ← ofExcept' (natOf row "parity")
    let want := strOpt row "error"
    let got :=
      match Code.new d p with
      | .ok _ => none
      | .error e => some e
    t := t.ok (got == want) s!"rs-new {d}+{p}: {repr got}, nearcore {repr want}"
  -- parity
  let mut n := 0
  for row in ← lines (dir / "rs-encode.jsonl") do
    let d ← ofExcept' (natOf row "data")
    let p ← ofExcept' (natOf row "parity")
    let data ← ofExcept' (hexList row "dataShards")
    let parity ← ofExcept' (hexList row "parityShards")
    match Code.new d p with
    | .error e =>
      t := t.ok false s!"rs-encode {d}+{p}: {e}"
    | .ok c =>
      match c.encode data with
      | .ok got =>
        t := t.ok (got == parity) s!"rs-encode {d}+{p}: parity differs"
      | .error e =>
        t := t.ok false s!"rs-encode {d}+{p}: {e}"
    n := n + 1
  for row in ← lines (dir / "rs-encode-error.jsonl") do
    let d ← ofExcept' (natOf row "data")
    let p ← ofExcept' (natOf row "parity")
    let case ← ofExcept' (row.getObjValAs? String "case")
    let want := strOpt row "error"
    let shards : Array ByteArray :=
      if case == "empty" then (Array.range d).map fun _ => ByteArray.empty
      else #[ByteArray.mk #[1, 2], ByteArray.mk #[3]]
    let got :=
      match Code.new d p with
      | .ok c =>
        match c.encode shards with
        | .ok _ => none
        | .error e => some e
      | .error e => some e
    t := t.ok (got == want) s!"rs-encode-error {case}: {repr got}, nearcore {repr want}"
  -- reconstruction
  let mut recon := 0
  for row in ← lines (dir / "rs-reconstruct.jsonl") do
    let d ← ofExcept' (natOf row "data")
    let p ← ofExcept' (natOf row "parity")
    let shards ← ofExcept' (optHexList row "shards")
    let c ← ofExcept' (Code.new d p)
    match strOpt row "error" with
    | some want =>
      match c.reconstruct shards with
      | .ok _ =>
        t := t.ok false s!"rs-reconstruct {d}+{p}: Lean reconstructs, nearcore says {want}"
      | .error e =>
        t := t.ok (e == want) s!"rs-reconstruct {d}+{p}: error {e}, nearcore {want}"
    | none =>
      let want ← ofExcept' (hexList row "result")
      match c.reconstruct shards with
      | .ok got =>
        t := t.ok (got == want) s!"rs-reconstruct {d}+{p}: shards differ"
      | .error e =>
        t := t.ok false s!"rs-reconstruct {d}+{p}: {e}"
    recon := recon + 1
  -- the wrapper
  let mut wrapped := 0
  for row in ← lines (dir / "rs-bytes.jsonl") do
    let d ← ofExcept' (natOf row "data")
    let p ← ofExcept' (natOf row "parity")
    let borsh ← ofExcept' (bytesOf row "borsh")
    let parts ← ofExcept' (hexList row "parts")
    let len ← ofExcept' (natOf row "encodedLength")
    let c ← ofExcept' (Code.new d p)
    match encodeBytes c borsh with
    | .ok (got, l) =>
      t := t.ok (got == parts && l == len) s!"rs-bytes {d}+{p} ({borsh.size} bytes): parts differ"
    | .error e =>
      t := t.ok false s!"rs-bytes {d}+{p}: {e}"
    wrapped := wrapped + 1
  let mut decoded := 0
  for row in ← lines (dir / "rs-decode.jsonl") do
    let d ← ofExcept' (natOf row "data")
    let p ← ofExcept' (natOf row "parity")
    let parts ← ofExcept' (optHexList row "parts")
    let len ← ofExcept' (natOf row "encodedLength")
    let c ← ofExcept' (Code.new d p)
    -- `reed_solomon_decode::<Vec<u8>>`: the rebuilt bytes must be a whole Borsh `Vec<u8>`
    let ours : Option ByteArray :=
      match decodeBytes c parts len with
      | .ok b =>
        match Borsh.Codec.decodeAll (α := ByteArray) b with
        | .ok v => some (Borsh.Codec.encode v)
        | .error _ => none
      | .error _ => none
    match strOpt row "ok" with
    | some want =>
      t :=
        t.ok (ours.map toHex == some want)
          s!"rs-decode {d}+{p} length {len}: Lean {ours.map toHex}, nearcore ok"
    | none =>
      t := t.ok ours.isNone s!"rs-decode {d}+{p} length {len}: Lean decodes, nearcore refuses"
    decoded := decoded + 1
  IO.println
      s!"reed-solomon: {n} encodings, {recon} reconstructions, {wrapped} wrapped encodings, {decoded} wrapped decodings"
  pure t

/-! ### Chunks -/

def decodeHex (α : Type) [Codec α] (row : Json) (k : String) : IO α := do
  let b ← ofExcept' (bytesOf row k)
  match Codec.decodeAll (α := α) b with
  | .ok v =>
    pure v
  | .error e =>
    throw (IO.userError s!"{k} does not decode: {repr e}")

def hashOf (row : Json) (k : String) : IO CryptoHash := do
  let b ← ofExcept' (bytesOf row k)
  if b.size == 32 then
    pure ⟨b⟩
  else
    throw (IO.userError s!"{k} is not a hash")

def chunkChecks (dir : System.FilePath) (t : Tally) : IO Tally := do
  let mut t := t
  let mut n := 0
  let mut partialsChecked := 0
  for row in ← lines (dir / "chunk.jsonl") do
    let account ← ofExcept' (row.getObjValAs? String "account")
    let secret ← ofExcept' (row.getObjValAs? String "secret")
    let some signer := Signer.ofSecret? account secret | throw (IO.userError "bad signer")
    let protocol ← ofExcept' (natOf row "protocol")
    let d ← ofExcept' (natOf row "data")
    let p ← ofExcept' (natOf row "parity")
    let rs ← ofExcept' (Code.new d p)
    let layout ← decodeHex ShardLayout row "layout"
    let shardId ← ofExcept' (natOf row "shardId")
    let height ← ofExcept' (natOf row "height")
    let inputs : ChunkInputs :=
      { prevBlockHash := ← hashOf row "prevBlockHash",
        prevStateRoot := ← hashOf row "prevStateRoot",
        prevOutcomeRoot := ← hashOf row "prevOutcomeRoot", height := height.toUInt64,
        shardId := shardId.toUInt64, prevGasUsed := ← decodeHex Gas row "prevGasUsed",
        gasLimit := ← decodeHex Gas row "gasLimit",
        prevBalanceBurnt := ← decodeHex Balance row "prevBalanceBurnt",
        prevValidatorProposals := ← decodeHex (Array ValidatorStake) row "validatorProposals",
        transactions := ← decodeHex (Array SignedTransaction) row "transactions",
        outgoingReceipts := ← decodeHex (Array Receipt) row "receipts",
        outgoingReceiptsRoot := ← hashOf row "outgoingReceiptsRoot",
        txRoot := ← hashOf row "txRoot",
        congestionInfo := ← decodeHex CongestionInfo row "congestionInfo",
        bandwidthRequests := ← decodeHex BandwidthRequests row "bandwidthRequests",
        proposedSplit := ← decodeHex (Option TrieSplit) row "proposedSplit" }
    -- the per-shard hashes
    let wantHashes ← ofExcept' (hexList row "receiptsHashes")
    match receiptsHashes layout inputs.outgoingReceipts with
    | .ok hs =>
      t :=
        t.ok (hs.map (·.bytes) == wantHashes)
          s!"chunk {n}: receipt hashes {hs.map (toHex ·.bytes)} vs {wantHashes.map toHex}"
    | .error e =>
      t := t.ok false s!"chunk {n}: receipt hashes: {e}"
    -- the roots the producer computes
    let (txRoot, _) := merklize inputs.transactions
    t := t.ok (txRoot == inputs.txRoot) s!"chunk {n}: tx root"
    match receiptProofs layout inputs.shardId inputs.outgoingReceipts with
    | .error e =>
      t := t.ok false s!"chunk {n}: receipt proofs: {e}"
    | .ok (root, proofs) =>
      t := t.ok (root == inputs.outgoingReceiptsRoot) s!"chunk {n}: outgoing receipts root"
      let want ← decodeHex (Array ReceiptProof) row "receiptProofs"
      t := t.ok (proofs == want) s!"chunk {n}: receipt proofs differ"
      match produceChunk signer protocol rs inputs with
      | .error e =>
        t := t.ok false s!"chunk {n}: {e}"
      | .ok produced =>
        let wantChunk ← ofExcept' (bytesOf row "shardChunk")
        let wantEncoded ← ofExcept' (bytesOf row "encodedChunk")
        let wantPaths ← ofExcept' (bytesOf row "paths")
        t := t.ok (Codec.encode produced.chunk == wantChunk) s!"chunk {n}: shard chunk differs"
        t :=
          t.ok (Codec.encode produced.encoded == wantEncoded) s!"chunk {n}: encoded chunk differs"
        t := t.ok (Codec.encode produced.paths == wantPaths) s!"chunk {n}: merkle paths differ"
        let wantHash ← hashOf row "chunkHash"
        t := t.ok (produced.encoded.chunkHash.hash == wantHash) s!"chunk {n}: chunk hash"
        for pr in (← ofExcept' (row.getObjValAs? (Array Json) "partials")) do
          let ords := (← ofExcept' (pr.getObjValAs? (Array Nat) "ords")).map (·.toUInt64)
          let kept ← ofExcept' (natOf pr "receiptProofs")
          let wantPartial ← ofExcept' (bytesOf pr "partial")
          match
            partialEncodedChunk produced.encoded ords (proofs.extract 0 kept) produced.paths with
          | .ok got =>
            t := t.ok (Codec.encode got == wantPartial) s!"chunk {n}: partial chunk differs"
          | .error e =>
            t := t.ok false s!"chunk {n}: partial chunk: {e}"
          partialsChecked := partialsChecked + 1
    n := n + 1
  IO.println s!"chunks: {n} produced chunks, {partialsChecked} partial chunks"
  pure t

/-! ### Signed messages -/

def signerOf (row : Json) : IO Signer := do
  let account ← ofExcept' (row.getObjValAs? String "account")
  let secret ← ofExcept' (row.getObjValAs? String "secret")
  match Signer.ofSecret? account secret with
  | some s =>
    pure s
  | none =>
    throw (IO.userError "bad signer")

def messageChecks (dir : System.FilePath) (t : Tally) : IO Tally := do
  let mut t := t
  let mut n := 0
  for row in ← lines (dir / "approval.jsonl") do
    let s ← signerOf row
    let a :=
      newApproval s (← hashOf row "parentHash") (← ofExcept' (natOf row "parentHeight")).toUInt64
        (← ofExcept' (natOf row "targetHeight")).toUInt64
    t := t.ok (Codec.encode a == (← ofExcept' (bytesOf row "approval"))) s!"approval {n}"
    n := n + 1
  for row in ← lines (dir / "endorsement.jsonl") do
    let s ← signerOf row
    let e :=
      newChunkEndorsement s (← decodeHex EpochId row "epochId")
        (← decodeHex ShardChunkHeader row "header")
    t := t.ok (Codec.encode e == (← ofExcept' (bytesOf row "endorsement"))) s!"endorsement {n}"
    n := n + 1
  for row in ← lines (dir / "partial-witness.jsonl") do
    let s ← signerOf row
    let w :=
      newPartialWitness s (← decodeHex EpochId row "epochId")
        (← decodeHex ShardChunkHeader row "header") (← ofExcept' (natOf row "partOrd"))
        (← ofExcept' (bytesOf row "part")) (← ofExcept' (natOf row "encodedLength"))
    t :=
      t.ok
        (Codec.encode (VersionedPartialEncodedStateWitness.v1 w) ==
          (← ofExcept' (bytesOf row "witness")))
        s!"partial witness {n}"
    n := n + 1
  let mut parts := 0
  for row in ← lines (dir / "witness-parts.jsonl") do
    let s ← signerOf row
    let validators :=
      (← ofExcept' (row.getObjValAs? (Array String) "validators")).map fun v => (⟨v⟩ : AccountId)
    let bytes ← ofExcept' (bytesOf row "bytes")
    let want ← ofExcept' (hexList row "witnesses")
    match
      witnessParts s (← decodeHex EpochId row "epochId") (← decodeHex ShardChunkHeader row "header")
        ⟨bytes⟩ validators with
    | .ok got =>
      t :=
        t.ok
          (got.map (fun (_, w) => Codec.encode (VersionedPartialEncodedStateWitness.v1 w)) == want)
          s!"witness parts ({validators.size} validators, {bytes.size} bytes) differ"
      parts := parts + got.size
    | .error e =>
      t := t.ok false s!"witness parts: {e}"
  for row in ← lines (dir / "witness-ack.jsonl") do
    let header ← decodeHex ShardChunkHeader row "header"
    t :=
      t.ok
        (Codec.encode (ChunkStateWitnessAck.mk header.chunkHash) ==
          (← ofExcept' (bytesOf row "ack")))
        "witness ack"
  IO.println s!"messages: {n} signed, {parts} witness parts"
  pure t

/-! ### Blocks -/

def blockChecks (dir : System.FilePath) (t : Tally) : IO Tally := do
  let mut t := t
  let mut n := 0
  for row in ← lines (dir / "block.jsonl") do
    let s ← signerOf row
    let rate ← ofExcept' (row.getObjValAs? (Array Nat) "rate")
    let price (k : String) : IO Balance := do
      pure ⟨(← ofExcept' (row.getObjValAs? String k)).toNat!⟩
    let economics : Chain.Config :=
      { epochLength := 0, genesisHeight := 0, minGasPrice := ← price "minGasPrice",
        maxGasPrice := ← price "maxGasPrice", rateNumer := rate[0]!, rateDenom := rate[1]!,
        staticShardLayout := true }
    let inputs : BlockInputs :=
      { protocolVersion := (← ofExcept' (natOf row "protocol")).toUInt32,
        latestProtocolVersion := (← ofExcept' (natOf row "protocol")).toUInt32,
        prev := ← decodeHex BlockHeader row "prev",
        height := (← ofExcept' (natOf row "height")).toUInt64,
        blockOrdinal := (← ofExcept' (natOf row "blockOrdinal")).toUInt64,
        chunks := ← decodeHex (Array ShardChunkHeader) row "chunks",
        chunkEndorsements := ← decodeHex (Array (Array (Option Signature))) row "chunkEndorsements",
        epochId := ← decodeHex EpochId row "epochId",
        nextEpochId := ← decodeHex EpochId row "nextEpochId",
        epochSyncDataHash := ← decodeHex (Option CryptoHash) row "epochSyncDataHash",
        approvals := ← decodeHex (Array (Option Signature)) row "approvals", economics,
        mintedAmount := ← decodeHex (Option Balance) row "mintedAmount",
        nextBpHash := ← hashOf row "nextBpHash", blockMerkleRoot := ← hashOf row "blockMerkleRoot",
        now := (← ofExcept' (natOf row "now")).toUInt64,
        shardSplit := ← decodeHex (Option (ShardId × AccountId)) row "shardSplit" }
    match produceBlock s inputs with
    | .error e =>
      t := t.ok false s!"block {n}: {e}"
    | .ok b =>
      t := t.ok (Codec.encode b == (← ofExcept' (bytesOf row "block"))) s!"block {n}: block differs"
      t := t.ok (b.hash == (← hashOf row "hash")) s!"block {n}: hash differs"
      t := t.ok b.checkValidity.isNone s!"block {n}: the roots and the mask do not check"
    n := n + 1
  IO.println s!"blocks: {n} produced"
  pure t

/-! ### The zstd frames of the node -/

/-- Inputs of the frames: every size around the block boundary and a few patterns. -/
def zstdInputs : Array ByteArray :=
  Id.run do
    let mut out := #[]
    for len in [0, 1, 2, 100, 4095, 131072, 131073] do
      out :=
        out.push
          (ByteArray.mk ((Array.range len).map fun i => ((i * 31 + i / 251 + len) % 256).toUInt8))
    out := out.push (ByteArray.mk (Array.replicate 70000 7))
    return out

def zstdChecks (dir : System.FilePath) (t : Tally) (write : Bool) : IO Tally := do
  let mut t := t
  let mut rows := #[]
  let mut i := 0
  for input in zstdInputs do
    let frame := compressStored input
    rows := rows.push (Json.compress (Json.mkObj [("input", toHex input), ("frame", toHex frame)]))
    match Zstd.decompress frame (input.size + 1) with
    | .ok back =>
      t := t.ok (back == input) s!"zstd {i}: the decoder of the node returns other bytes"
    | .error e =>
      t := t.ok false s!"zstd {i}: the decoder of the node refuses the frame: {e}"
    i := i + 1
  let file := dir / "zstd-stored.jsonl"
  let text := "\n".intercalate rows.toList ++ "\n"
  if write then
    IO.FS.writeFile file text
  else
    t :=
      t.ok ((← IO.FS.readFile file) == text) "zstd-stored.jsonl differs from what the node writes"
  IO.println s!"zstd: {i} frames of raw blocks"
  pure t

end Near.Node.ValidatorConformance

open Near.Node.ValidatorConformance in
def main (args : List String) : IO UInt32 := do
  let dir : System.FilePath :=
    (args.filter (· != "--write-zstd")).headD "near-lean/node/fixtures/validator"
  let mut t : Tally := {}
  t ← gfChecks dir t
  t ← rsChecks dir t
  t ← chunkChecks dir t
  t ← messageChecks dir t
  t ← blockChecks dir t
  t ← zstdChecks dir t (args.contains "--write-zstd")
  IO.println s!"{t.checks} checks, {t.failures.size} failures"
  for f in t.failures.extract 0 30 do
    IO.println s!"  FAIL {f}"
  return if t.failures.isEmpty then 0 else 1
