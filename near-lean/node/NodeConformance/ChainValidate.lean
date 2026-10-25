import Lean.Data.Json
import NodeConformance.Runner
import NearNode.Chain

/-!
`node-chain-validate DIR`: the blocks of a localnet through the Lean validator (M5a).

`DIR` is one unpacked chain of the corpus (`tools/localnet/chain_validate.py` unpacks it):

* `meta.json`: the genesis and economics parameters;
* `epochs.jsonl`: the `EpochInfo` and shard layout of every epoch (given in M5a);
* `blocks.jsonl`: every block from genesis to the head with the values nearcore derived for it;
* `variants.jsonl`: invalid blocks made from valid ones, with the verdict of `Chain` on each.

The blocks go through `acceptBlock` in order. A valid block must be accepted and the values the
validator derives must be nearcore's: the `BlockInfo` (epoch id, first block of the epoch, last
finalized height, ...), the block merkle tree and its root, the block producer, the approvers with
their stakes, the chunk producers and the chunk validator assignments. Each variant is validated
against the chain that precedes its base block and must be rejected with the `Error` variant that
nearcore returned. The exit code is 0 only when everything agrees.
-/

open Lean Near.Node Near.Node.Chain Near.Node.Conformance Near.Node.Borsh

private def field (j : Json) (k : String) : Except String Json :=
  j.getObjVal? k

private def str (j : Json) (k : String) : Except String String :=
  j.getObjValAs? String k

private def nat (j : Json) (k : String) : Except String Nat :=
  j.getObjValAs? Nat k

private def bytes (j : Json) (k : String) : Except String ByteArray := do
  match ofHex (← str j k) with
  | some b =>
    pure b
  | none =>
    throw s!"{k} is not hex"

private def decode (α : Type) [Codec α] (what : String) (b : ByteArray) : Except String α :=
  match Codec.decodeAll (α := α) b with
  | .ok a => pure a
  | .error e => throw s!"{what} does not decode: {repr e}"

private def hashOf (b : ByteArray) : CryptoHash :=
  ⟨b⟩

/-- One line of a JSONL file per call. -/
private def lines (path : System.FilePath) : IO (Array Json) := do
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
  return out

private def orThrow (r : Except String α) : IO α :=
  match r with
  | .ok a => pure a
  | .error e => throw (IO.userError e)

private def parseConfig (manifest : Json) : Except String Config := do
  pure
      { epochLength := (← nat manifest "epochLength").toUInt64,
        genesisHeight := (← nat manifest "genesisHeight").toUInt64,
        minGasPrice := ⟨(← str manifest "minGasPrice").toNat!⟩,
        maxGasPrice := ⟨(← str manifest "maxGasPrice").toNat!⟩,
        rateNumer := ← nat manifest "gasPriceAdjustmentRateNumer",
        rateDenom := ← nat manifest "gasPriceAdjustmentRateDenom",
        staticShardLayout := (manifest.getObjValAs? Bool "shardLayoutStatic").toOption.getD true }

private def parseEpoch (j : Json) : Except String (ByteArray × EpochData) := do
  let id ← bytes j "epochId"
  let info ← decode EpochInfo "EpochInfo" (← bytes j "epochInfo")
  let layout ← decode ShardLayout "ShardLayout" (← bytes j "shardLayout")
  pure (id, { info, layout })

/-- The pairs `[a, b]` of a JSON array. -/
private def pairs (j : Json) : Except String (Array (Json × Json)) := do
  (← j.getArr?).mapM fun p => do
      let a ← p.getArrVal? 0
      let b ← p.getArrVal? 1
      pure (a, b)

private def balance (j : Json) : Except String Balance := do
  pure ⟨(← j.getStr?).toNat!⟩

/-- A checker's tally. -/
private structure Tally where
  blocks : Nat := 0
  accepted : Nat := 0
  derivedChecked : Nat := 0
  variants : Nat := 0
  variantsAgree : Nat := 0
  failures : Array String := #[]

private def Tally.fail (t : Tally) (msg : String) : Tally :=
  { t with failures := t.failures.push msg }

/-- The values nearcore stored or computed for a block, against the validator's. -/
private def checkDerived (st : ChainState) (block : Block) (line : Json) :
    Except String (List String) := do
  let derived ← field line "derived"
  let v ← (block.header.view?).elim (throw "header version") pure
  let hash := block.header.hash
  let mut out : List String := []
  let b ← st.block hash |>.mapError fun e => e.kind
  if Codec.encode (BlockInfo.v4 b.info) != (← bytes derived "blockInfo") then
    out := "BlockInfo differs" :: out
  if Codec.encode b.tree != (← bytes derived "blockMerkleTree") then
    out := "block merkle tree differs" :: out
  if b.tree.root.bytes != (← bytes derived "blockMerkleRoot") then
    out := "block merkle root differs" :: out
  if (← bytes line "hash") != hash.bytes then
    out := "block hash differs" :: out
  -- the epoch of the block
  let epochId ← st.epochIdFromPrevBlock v.prevHash |>.mapError fun e => e.kind
  if epochId.hash.bytes != (← bytes derived "epochId") then
    out := "epoch id differs" :: out
  let nextEpochId ← st.nextEpochIdFromPrevBlock v.prevHash |>.mapError fun e => e.kind
  if nextEpochId.hash.bytes != (← bytes derived "nextEpochId") then
    out := "next epoch id differs" :: out
  let startsEpoch ← st.isNextBlockEpochStart hash |>.mapError fun e => e.kind
  if startsEpoch != (derived.getObjValAs? Bool "nextBlockStartsEpoch").toOption.getD false then
    out := "next block epoch start differs" :: out
  -- the block producer
  match derived.getObjVal? "blockProducer" with
  | .ok (.str expected) =>
    let producer ← st.blockProducer v.epochId v.height |>.mapError fun e => e.kind
    if producer.accountId.val != expected then
      out := s!"block producer {producer.accountId.val} but nearcore {expected}" :: out
  | _ =>
    pure ()
  -- the approvers (of the block after the previous one)
  match derived.getObjVal? "approvers" with
  | .ok (.arr expected) =>
    let approvers ← st.blockApprovers v.prevHash epochId nextEpochId |>.mapError fun e => e.kind
    let got := approvers.map fun a => (a.accountId.val, a.stakeThisEpoch.val, a.stakeNextEpoch.val)
    let want ←
      expected.mapM fun row => do
          pure
              ((← row.getArrVal? 0).getStr?.toOption.getD "",
                (← (row.getArrVal? 1)).getStr?.toOption.getD "0",
                (← (row.getArrVal? 2)).getStr?.toOption.getD "0")
    let want := want.map fun (a, x, y) => (a, x.toNat!, y.toNat!)
    if got != want then
      out := "approvers differ" :: out
  | _ =>
    pure ()
  -- chunk producers and validators of the new chunks
  for (shardJ, account) in ← pairs (← field derived "chunkProducers") do
    let shard ← shardJ.getNat?
    let producer ← st.chunkProducerAfter v.prevHash shard.toUInt64 |>.mapError fun e => e.kind
    if producer.accountId.val != account.getStr?.toOption.getD "" then
      out := s!"chunk producer of shard {shard} differs" :: out
  for (shardJ, rows) in ← pairs (← field derived "chunkValidators") do
    let shard ← shardJ.getNat?
    let some chunk := block.chunks.find? fun c => c.shardId == shard.toUInt64
      | throw "chunk of an assignment"
    let got ←
      st.chunkValidatorAssignments epochId shard.toUInt64 chunk.heightCreated |>.mapError fun e =>
          e.kind
    let want ←
      (← pairs rows).mapM fun (a, s) => do
          pure ((a.getStr?.toOption.getD ""), (s.getStr?.toOption.getD "0").toNat!)
    if got.map (fun (a, s) => (a.val, s.val)) != want then
      out := s!"chunk validators of shard {shard} differ" :: out
  return out.reverse

/-- Whether the verdict of a variant is nearcore's. -/
private def sameVerdict (got : Result Unit) (expected : Json) : Bool × String :=
  let kind := (expected.getObjValAs? String "error").toOption.getD "?"
  let message := (expected.getObjValAs? String "message").toOption.getD ""
  match got with
  | .ok _ => (false, s!"accepted, nearcore: {kind}")
  | .error e =>
    if e.kind != kind then (false, s!"{e.kind} ({e.detail}), nearcore: {kind} {message}")
    else
      if kind == "Other" && !(message.splitOn e.detail).length.beq 1 && e.detail.isEmpty then
        (false, s!"Other: {message}")
      else (true, "")

def main (args : List String) : IO UInt32 := do
  let [dir] := args
    |
    IO.eprintln "usage: node-chain-validate DIR"
    return 2
  let dir : System.FilePath := dir
  let manifest ← orThrow (Json.parse (← IO.FS.readFile (dir / "meta.json")))
  let config ← orThrow (parseConfig manifest)
  let mut epochs : Std.HashMap ByteArray EpochData := {}
  for j in ← lines (dir / "epochs.jsonl") do
    let (id, e) ← orThrow (parseEpoch j)
    epochs := epochs.insert id e
  let blockLines ← lines (dir / "blocks.jsonl")
  let variantLines ← lines (dir / "variants.jsonl")
  -- variants by base height
  let mut byHeight : Std.HashMap Nat (Array Json) := {}
  for v in variantLines do
    let h ← orThrow (nat v "baseHeight")
    byHeight := byHeight.insert h ((byHeight.getD h #[]).push v)
  -- genesis
  let some genesisLine := blockLines[0]?
    |
    IO.eprintln "no blocks";
    return 1
  let genesis ←
    orThrow
        (do
          decode Block "genesis" (← bytes genesisLine "block"))
  let some gv := genesis.header.view?
    |
    IO.eprintln "genesis header version";
    return 1
  let genesisDerived ← orThrow (field genesisLine "derived")
  let genesisInfo ←
    orThrow
        (do
          decode BlockInfo "genesis BlockInfo" (← bytes genesisDerived "blockInfo"))
  let .v4 info := genesisInfo
    |
    IO.eprintln "genesis BlockInfo is not V4";
    return 1
  let genesisTree ←
    orThrow
        (do
          decode PartialMerkleTree "tree" (← bytes genesisDerived "blockMerkleTree"))
  let genesisHash := genesis.header.hash
  let rec0 : BlockRec :=
    { hash := genesisHash, header := genesis.header, view := gv, chunks := genesis.chunks, info,
      tree := genesisTree }
  -- the epoch manager keeps a default `BlockInfo` under the zero hash (the first block of genesis's
  -- epoch, which is itself)
  let zeroInfo ←
    orThrow
        (do
          decode BlockInfo "pre-genesis BlockInfo" (← bytes manifest "zeroHashBlockInfo"))
  let .v4 zeroInfo := zeroInfo
    |
    IO.eprintln "pre-genesis BlockInfo is not V4";
    return 1
  let zeroRec : BlockRec :=
    { hash := CryptoHash.zero, header := default, view := default, chunks := #[], info := zeroInfo,
      tree := default }
  let blocks : Std.HashMap ByteArray BlockRec :=
    (({} : Std.HashMap ByteArray BlockRec).insert CryptoHash.zero.bytes zeroRec).insert
      genesisHash.bytes rec0
  let mut st : ChainState :=
    { config, epochs, blocks, head := genesisHash, headHeight := gv.height, genesisHash,
      genesisChunks := genesis.chunks }
  let mut t : Tally := {}
  let started ← IO.monoMsNow
  for line in blockLines.extract 1 blockLines.size do
    let height ← orThrow (nat line "height")
    -- the variants of this base block, against the chain that precedes it
    for v in byHeight.getD height #[] do
      let name ← orThrow (str v "name")
      let block ←
        orThrow
            (do
              decode Block name (← bytes v "block"))
      let expected ← orThrow (field v "expected")
      let (ok, why) := sameVerdict (validateBlock st block) expected
      t := { t with variants := t.variants + 1 }
      if ok then
        t := { t with variantsAgree := t.variantsAgree + 1 }
      else
        t := t.fail s!"variant {name} at height {height}: {why}"
    let block ←
      orThrow
          (do
            decode Block s!"block {height}" (← bytes line "block"))
    t := { t with blocks := t.blocks + 1 }
    match acceptBlock st block with
    | .error e =>
      t := t.fail s!"block {height} rejected: {e.kind} {e.detail}"
      break
    | .ok st' =>
      st := st'
      t := { t with accepted := t.accepted + 1 }
      match checkDerived st block line with
      | .ok [] =>
        t := { t with derivedChecked := t.derivedChecked + 1 }
      | .ok problems =>
        t := t.fail s!"block {height}: {", ".intercalate problems}"
      | .error e =>
        t := t.fail s!"block {height}: derived check failed: {e}"
  let elapsed := (← IO.monoMsNow) - started
  IO.println
      s!"{manifest.getObjValAs? String "chainId" |>.toOption.getD "?"}: blocks {t.accepted}/{t.blocks} accepted, derived values agree on {t.derivedChecked}, variants {t.variantsAgree}/{t.variants} agree ({elapsed} ms)"
  for f in t.failures.extract 0 40 do
    IO.println s!"  FAIL {f}"
  if t.failures.size > 40 then
    IO.println s!"  ... {t.failures.size - 40} more"
  return if t.failures.isEmpty && t.blocks == t.accepted then 0 else 1
