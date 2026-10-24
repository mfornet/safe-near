import Lean.Data.Json
import NodeConformance.Runner
import NearNode.Chain
import NearNode.Epoch

/-!
`node-chain-apply DIR`: a localnet chain run by the Lean node from genesis (M5b).

`DIR` is one unpacked chain of the corpus (`tools/localnet/chain_apply.py` unpacks it): `meta.json`,
`genesis.json`, `epochs.jsonl`, `blocks.jsonl` and `chunks.jsonl`. Nothing about epochs is given
to the node: the genesis epochs are made from the genesis configuration, every later `EpochInfo`
is computed when the last block of an epoch is accepted (`Epoch.processBlock`), and the
`epochs.jsonl` file is only what the result is compared with, byte for byte.
-/

open Lean Near.Node Near.Node.Chain Near.Node.Epoch Near.Node.Conformance Near.Node.Borsh

namespace ChainApply

def field (j : Json) (k : String) : Except String Json :=
  j.getObjVal? k

def str (j : Json) (k : String) : Except String String :=
  j.getObjValAs? String k

def nat (j : Json) (k : String) : Except String Nat :=
  j.getObjValAs? Nat k

def bytes (j : Json) (k : String) : Except String ByteArray := do
  match ofHex (← str j k) with
  | some b =>
    pure b
  | none =>
    throw s!"{k} is not hex"

def decode (α : Type) [Codec α] (what : String) (b : ByteArray) : Except String α :=
  match Codec.decodeAll (α := α) b with
  | .ok a => pure a
  | .error e => throw s!"{what} does not decode: {repr e}"

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
  return out

def orThrow (r : Except String α) : IO α :=
  match r with
  | .ok a => pure a
  | .error e => throw (IO.userError e)

def parseConfig (manifest : Json) : Except String Config := do
  pure
      { epochLength := (← nat manifest "epochLength").toUInt64,
        genesisHeight := (← nat manifest "genesisHeight").toUInt64,
        minGasPrice := ⟨(← str manifest "minGasPrice").toNat!⟩,
        maxGasPrice := ⟨(← str manifest "maxGasPrice").toNat!⟩,
        rateNumer := ← nat manifest "gasPriceAdjustmentRateNumer",
        rateDenom := ← nat manifest "gasPriceAdjustmentRateDenom",
        staticShardLayout := (manifest.getObjValAs? Bool "shardLayoutStatic").toOption.getD true }

/-- The genesis configuration: the epoch manager's setup and the genesis validators. -/
structure Genesis where
  setup : Setup
  validators : Array ValidatorStake
  records : Array Json
  chainId : String
  totalSupply : Nat

def parseGenesis (j : Json) : Except String Genesis := do
  let layout ← decode ShardLayout "shard layout" (← bytes j "shardLayout")
  let rate ← field j "protocolRewardRate"
  let validators ←
    (← (← field j "validators").getArr?).mapM fun v => do
        let key ← decode PublicKey "validator key" (← bytes v "publicKey")
        pure (ValidatorStake.v1 ⟨⟨← str v "accountId"⟩, key, ⟨(← str v "stake").toNat!⟩⟩)
  let setup : Setup :=
    {
      config :=
        { epochLength := ← nat j "epochLength",
          numBlockProducerSeats := ← nat j "numBlockProducerSeats", shardLayout := layout },
      reward :=
        { protocolRewardRate := ⟨← (← rate.getArrVal? 0).getNat?, ← (← rate.getArrVal? 1).getNat?⟩,
          protocolTreasuryAccount := ⟨← str j "protocolTreasuryAccount"⟩,
          genesisProtocolVersion := (← nat j "protocolVersion").toUInt32 } }
  pure
      { setup, validators, records := (← (← field j "records").getArr?),
        chainId := ← str j "chainId", totalSupply := (← str j "totalSupply").toNat! }

/-- A checker's tally. -/
structure Tally where
  blocks : Nat := 0
  accepted : Nat := 0
  epochs : Nat := 0
  epochsEqual : Nat := 0
  updates : Nat := 0
  updatesEqual : Nat := 0
  failures : Array String := #[]

def Tally.fail (t : Tally) (msg : String) : Tally :=
  { t with failures := t.failures.push msg }

/-- The first fields in which two epoch infos differ. -/
def describeDifference (a b : EpochInfo) : String :=
  let va := a.view
  let vb := b.view
  let checks : List (String × Bool) :=
    [("version", a.version == b.version), ("epochHeight", va.epochHeight == vb.epochHeight),
      ("validators", va.validators == vb.validators),
      ("blockProducers", va.blockProducers == vb.blockProducers),
      ("chunkProducers", va.chunkProducers == vb.chunkProducers),
      ("stakeChange",
        va.stakeChange.map (fun (k, v) => (k.val, v.val)) ==
          vb.stakeChange.map (fun (k, v) => (k.val, v.val))),
      ("validatorReward",
        va.validatorReward.map (fun (k, v) => (k.val, v.val)) ==
          vb.validatorReward.map (fun (k, v) => (k.val, v.val))),
      ("validatorKickout", va.validatorKickout.size == vb.validatorKickout.size),
      ("mintedAmount", a.mintedAmount == b.mintedAmount),
      ("seatPrice", va.seatPrice == vb.seatPrice),
      ("protocolVersion", va.protocolVersion == vb.protocolVersion),
      ("rngSeed", a.rngSeed == b.rngSeed)]
  let bad := checks.filter (!·.2) |>.map (·.1)
  if bad.isEmpty then "samplers or mandates" else ", ".intercalate bad

/-- A JSON object `{account: amount}` as sorted pairs. -/
def amounts (j : Json) : Except String (Array (String × Nat)) := do
  let o ← j.getObj?
  let rows := o.toArray.map fun (k, v) => (k, (v.getStr?.toOption.getD "0").toNat!)
  pure (rows.qsort fun a b => a.1 < b.1)

def sortedAmounts (xs : Array (AccountId × Balance)) : Array (String × Nat) :=
  (xs.map fun (a, b) => (a.val, b.val)).qsort fun a b => a.1 < b.1

/-- Whether the update nearcore applied in a chunk is the one computed from the epochs. -/
def sameUpdate (got : Option AccountsUpdate) (want : Json) : Except String Bool := do
  match got, want with
  | none, .null =>
    pure true
  | some u, .obj _ =>
    pure
        (sortedAmounts u.stakeInfo == (← amounts (← field want "stakeInfo")) &&
          sortedAmounts u.validatorRewards == (← amounts (← field want "validatorRewards")) &&
          sortedAmounts u.lastProposals == (← amounts (← field want "lastProposals")) &&
          (u.protocolTreasury.map (·.val)) ==
            ((← field want "protocolTreasuryAccountId").getStr?.toOption))
  | _, _ =>
    pure false

end ChainApply

open ChainApply

def main (args : List String) : IO UInt32 := do
  let some dir := args.head?
    |
    IO.eprintln "usage: node-chain-apply DIR";
    return 2
  let dir : System.FilePath := dir
  let manifest ← orThrow (Json.parse (← IO.FS.readFile (dir / "meta.json")))
  let config ← orThrow (parseConfig manifest)
  let genesisJson ← orThrow (Json.parse (← IO.FS.readFile (dir / "genesis.json")))
  let genesis ← orThrow (parseGenesis genesisJson)
  let mut given : Std.HashMap ByteArray (ByteArray × ByteArray) := {}
  for j in ← lines (dir / "epochs.jsonl") do
    given :=
      given.insert (← orThrow (bytes j "epochId"))
        (← orThrow (bytes j "epochInfo"), ← orThrow (bytes j "shardLayout"))
  let blockLines ← lines (dir / "blocks.jsonl")
  let some genesisLine := blockLines[0]? |
    IO.eprintln "no blocks";
    return 1
  let genesisBlock ←
    orThrow
        (do
          decode Block "genesis" (← bytes genesisLine "block"))
  let some gv := genesisBlock.header.view? |
    IO.eprintln "genesis header version";
    return 1
  let genesisDerived ← orThrow (field genesisLine "derived")
  let .v4 info ←
    orThrow
        (do
          decode BlockInfo "genesis BlockInfo" (← bytes genesisDerived "blockInfo")) |
    IO.eprintln "genesis BlockInfo is not V4";
    return 1
  let genesisTree ←
    orThrow
        (do
          decode PartialMerkleTree "tree" (← bytes genesisDerived "blockMerkleTree"))
  let genesisHash := genesisBlock.header.hash
  let rec0 : BlockRec :=
    { hash := genesisHash, header := genesisBlock.header, view := gv, chunks := genesisBlock.chunks,
      info, tree := genesisTree }
  let .v4 zeroInfo ←
    orThrow
        (do
          decode BlockInfo "pre-genesis BlockInfo" (← bytes manifest "zeroHashBlockInfo")) |
    IO.eprintln "pre-genesis BlockInfo is not V4";
    return 1
  let zeroRec : BlockRec :=
    { hash := CryptoHash.zero, header := default, view := default, chunks := #[], info := zeroInfo,
      tree := default }
  let blocks : Std.HashMap ByteArray BlockRec :=
    (({} : Std.HashMap ByteArray BlockRec).insert CryptoHash.zero.bytes zeroRec).insert
      genesisHash.bytes rec0
  let mut t : Tally := {}
  -- the genesis epoch, computed from the genesis configuration, under both of its ids
  let genesisEpoch ←
    match genesisEpochInfo genesis.setup genesis.validators with
    | .ok e =>
      pure e
    | .error e =>
      IO.eprintln s!"genesis epoch: {e.kind} {e.detail}";
      return 1
  let mut epochs : Std.HashMap ByteArray EpochData := {}
  epochs := (epochs.insert CryptoHash.zero.bytes genesisEpoch).insert genesisHash.bytes genesisEpoch
  for id in [CryptoHash.zero.bytes, genesisHash.bytes] do
    t := { t with epochs := t.epochs + 1 }
    match given[id]? with
    | some (i, l) =>
      if Codec.encode genesisEpoch.info == i && Codec.encode genesisEpoch.layout == l then
        t := { t with epochsEqual := t.epochsEqual + 1 }
      else
        let theirs ← orThrow (decode EpochInfo "EpochInfo" i)
        t := t.fail s!"genesis epoch differs: {describeDifference genesisEpoch.info theirs}"
    | none =>
      t := t.fail "genesis epoch missing from the corpus"
  let mut st : ChainState :=
    { config, epochs, blocks, head := genesisHash, headHeight := gv.height, genesisHash,
      genesisChunks := genesisBlock.chunks }
  -- the chunks nearcore applied: its `ValidatorAccountsUpdate` is the check of the rewards
  let chunkRows ← lines (dir / "chunks.jsonl")
  let mut rowsAt : Std.HashMap Nat (Array Json) := {}
  for r in chunkRows do
    let h ← orThrow (nat r "height")
    rowsAt := rowsAt.insert h ((rowsAt.getD h #[]).push r)
  let started ← IO.monoMsNow
  let maxHeight := (args.dropWhile (· != "--max-height")).tail.head?.bind String.toNat?
  for line in blockLines.extract 1 blockLines.size do
    let height ← orThrow (nat line "height")
    if let some m := maxHeight then
      if height > m then
        break
    let block ←
      orThrow
          (do
            decode Block s!"block {height}" (← bytes line "block"))
    t := { t with blocks := t.blocks + 1 }
    match processBlock genesis.setup st block with
    | .error e =>
      t := t.fail s!"block {height} rejected: {e.kind} {e.detail}"
      break
    | .ok (st', fin) =>
      st := st'
      t := { t with accepted := t.accepted + 1 }
      for r in rowsAt.getD height #[] do
        let shard := (← orThrow (nat r "shardId")).toUInt64
        let some chunk := block.chunks.find? (·.shardId == shard)
          |
          t := t.fail s!"block {height} has no chunk of shard {shard}";
          continue
        let want ←
          orThrow
              (do
                field (← field r "context") "validatorAccountsUpdate")
        t := { t with updates := t.updates + 1 }
        match
          validatorAccountsUpdate genesis.setup st block.header.prevHash shard
            chunk.prevValidatorProposals with
        | .error e =>
          t := t.fail s!"update at height {height} shard {shard}: {e.kind} {e.detail}"
        | .ok u =>
          if ← orThrow (sameUpdate u want) then
            t := { t with updatesEqual := t.updatesEqual + 1 }
          else
            t := t.fail s!"update at height {height} shard {shard} differs"
      if let some f := fin then
        t := { t with epochs := t.epochs + 1 }
        match given[f.epochId.hash.bytes]? with
        | some (i, l) =>
          if Codec.encode f.data.info == i && Codec.encode f.data.layout == l then
            t := { t with epochsEqual := t.epochsEqual + 1 }
          else
            let theirs ← orThrow (decode EpochInfo "EpochInfo" i)
            t :=
              t.fail
                s!"epoch finalized at height {height} differs: {describeDifference f.data.info theirs}"
        | none =>
          t := t.fail s!"epoch finalized at height {height} is not in the corpus"
  let elapsed := (← IO.monoMsNow) - started
  IO.println
      s!"{genesis.chainId}: epochs {t.epochsEqual}/{t.epochs} equal, validator accounts updates {t.updatesEqual}/{t.updates} equal, blocks {t.accepted}/{t.blocks} accepted ({elapsed} ms)"
  for f in t.failures.extract 0 40 do
    IO.println s!"  FAIL {f}"
  return if t.failures.isEmpty && t.blocks == t.accepted then 0 else 1
