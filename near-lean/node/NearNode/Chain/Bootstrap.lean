import Lean.Data.Json
import NearNode.Chain
import NearNode.Epoch
import NearNode.Chain.Persist
import NearNode.Chain.Apply
import NearNode.Chain.Genesis
import ChainReplay.HostCrypto

/-!
# Starting a chain

What the node starts from, as `node-chain-apply` reads it (M5b): the genesis configuration, the
genesis block with the `BlockInfo` and block merkle tree nearcore derived from it, and the
configuration of the chain. From these the node computes the genesis epochs, the genesis state of
every shard and the chain state that the first block is validated against. Nothing else of the
chain is given.

* `meta.json`: the economics of the chain and the `BlockInfo` of the zero hash;
* `genesis.json`: the genesis configuration without interpretation (validators, shard layout as
  Borsh, account and access key records);
* `blocks.jsonl`: whose first line is the genesis block (`block`, `derived.blockInfo`,
  `derived.blockMerkleTree`).

Computing the genesis block, its `BlockInfo` and tree from `genesis.json` alone is part of the
syncing observer (M7).
-/

namespace Near.Node.Bootstrap

open Lean Near.Node Near.Node.Chain Near.Node.Epoch Near.Node.Apply Near.Node.Borsh

def field (j : Json) (k : String) : Except String Json :=
  j.getObjVal? k

def str (j : Json) (k : String) : Except String String :=
  j.getObjValAs? String k

def nat (j : Json) (k : String) : Except String Nat :=
  j.getObjValAs? Nat k

/-- Lowercase hex to bytes. -/
def hexToBytes (s : String) : Option ByteArray := do
  let cs := s.toList.toArray
  if cs.size % 2 != 0 then
    none
  let nibble (c : Char) : Option UInt8 :=
    if '0' ≤ c && c ≤ '9' then some (c.toNat - 48).toUInt8
    else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 87).toUInt8 else none
  let mut out := ByteArray.empty
  for i in [0:cs.size / 2] do
    out := out.push ((← nibble cs[2 * i]!) <<< 4 ||| (← nibble cs[2 * i + 1]!))
  pure out

def bytes (j : Json) (k : String) : Except String ByteArray := do
  match hexToBytes (← str j k) with
  | some b =>
    pure b
  | none =>
    throw s!"{k} is not hex"

def decode (α : Type) [Codec α] (what : String) (b : ByteArray) : Except String α :=
  match Codec.decodeAll (α := α) b with
  | .ok a => pure a
  | .error e => throw s!"{what} does not decode: {repr e}"

def orThrow (r : Except String α) : IO α :=
  match r with
  | .ok a => pure a
  | .error e => throw (IO.userError e)

/-- The non-empty lines of a JSON lines file. -/
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

/-- The account and access key records of the genesis. -/
def parseRecords (records : Array Json) : Except String (Array GenesisAccount × Array GenesisKey) :=
  do
  let mut accounts : Array GenesisAccount := #[]
  let mut keys : Array GenesisKey := #[]
  for r in records do
    match r.getObjVal? "account" with
    | .ok a =>
      accounts :=
        accounts.push
          { id := ⟨← str a "id"⟩, amount := (← str a "amount").toNat!,
            locked := (← str a "locked").toNat! }
    | .error _ =>
      let k ← field r "accessKey"
      keys :=
        keys.push
          { id := ⟨← str k "id"⟩,
            publicKey := ← decode PublicKey "access key" (← bytes k "publicKey"),
            nonce := ← nat k "nonce" }
  pure (accounts, keys)

/-- A chain at its genesis. -/
structure Boot where
  metaJson : Json
  config : Config
  genesis : Genesis
  genesisBlock : Block
  genesisRec : BlockRec
  zeroRec : BlockRec
  genesisEpoch : EpochData
  /-- The chain state at the genesis block. -/
  state : Near.Node.Chain.ChainState
  /-- The state of every shard at the genesis block. -/
  progress : Progress
  /-- The writes that store the genesis block, epoch and state. -/
  ops : Array Store.Op
  params : Params
  /-- What nearcore derived for the genesis block, to compare. -/
  genesisLine : Json
  genesisHash : CryptoHash

/-- The genesis state of every shard, the genesis epoch and the first chain state. `blocksFile`'s
first line is the genesis block; `configs` holds the runtime configurations (`near-lean/vm/configs`). -/
def Boot.load (metaFile genesisFile blocksFile configs : System.FilePath) : IO Boot := do
  let metaJson ← orThrow (Json.parse (← IO.FS.readFile metaFile))
  let config ← orThrow (parseConfig metaJson)
  let genesisJson ← orThrow (Json.parse (← IO.FS.readFile genesisFile))
  let genesis ← orThrow (parseGenesis genesisJson)
  let first ← do
      let h ← IO.FS.Handle.mk blocksFile .read
      pure (← h.getLine)
  let genesisLine ← orThrow (Json.parse first)
  let genesisBlock ← orThrow (do decode Block "genesis" (← bytes genesisLine "block"))
  let some gv := genesisBlock.header.view? | throw (IO.userError "genesis header version")
  let genesisDerived ← orThrow (field genesisLine "derived")
  let .v4 info ←
    orThrow (do decode BlockInfo "genesis BlockInfo" (← bytes genesisDerived "blockInfo"))
    | throw (IO.userError "genesis BlockInfo is not V4")
  let genesisTree ←
    orThrow (do decode PartialMerkleTree "tree" (← bytes genesisDerived "blockMerkleTree"))
  let genesisHash := genesisBlock.header.hash
  let rec0 : BlockRec :=
    { hash := genesisHash, header := genesisBlock.header, view := gv, chunks := genesisBlock.chunks,
      info, tree := genesisTree }
  let .v4 zeroInfo ←
    orThrow (do decode BlockInfo "pre-genesis BlockInfo" (← bytes metaJson "zeroHashBlockInfo"))
    | throw (IO.userError "pre-genesis BlockInfo is not V4")
  let zeroRec : BlockRec :=
    { hash := CryptoHash.zero, header := default, view := default, chunks := #[], info := zeroInfo,
      tree := default }
  let blocks : Std.HashMap ByteArray BlockRec :=
    (({} : Std.HashMap ByteArray BlockRec).insert CryptoHash.zero.bytes zeroRec).insert
      genesisHash.bytes rec0
  let genesisEpoch ←
    match genesisEpochInfo genesis.setup genesis.validators with
    | .ok e => pure e
    | .error e => throw (IO.userError s!"genesis epoch: {e.kind} {e.detail}")
  let epochs : Std.HashMap ByteArray EpochData :=
    ((({} : Std.HashMap ByteArray EpochData).insert CryptoHash.zero.bytes genesisEpoch).insert
      genesisHash.bytes genesisEpoch)
  let st : Near.Node.Chain.ChainState :=
    { config, epochs, blocks, head := genesisHash, headHeight := gv.height, genesisHash,
      genesisChunks := genesisBlock.chunks }
  let (genesisAccounts, genesisKeys) ← orThrow (parseRecords genesis.records)
  let (roots, genesisTrieOps) ←
    orThrow (genesisTries genesisEpoch.layout genesisAccounts genesisKeys)
  for c in genesisBlock.chunks do
    match roots[c.shardId]? with
    | some root =>
      if root != c.prevStateRoot then
        throw (IO.userError s!"genesis state root of shard {c.shardId} differs from the genesis chunk header")
    | none => throw (IO.userError "genesis shard")
  let protocol := genesis.setup.reward.genesisProtocolVersion.toNat
  let runtimeConfig ← ChainReplay.HostCrypto.loadConfig configs protocol
  let congestion ← Near.Congestion.Config.load configs protocol
  let params : Params :=
    { setup := genesis.setup, cfg := runtimeConfig, congestion, protocol,
      chainId := genesis.chainId }
  let mut progress : Progress := { roots, tables := genesisTrieOps.foldl Store.Tables.apply {} }
  let mut genesisExtras : Array (ByteArray × ChunkExtra) := #[]
  for c in genesisBlock.chunks do
    let some root := roots[c.shardId]? | continue
    let some congestionInfo := congestionOf c | continue
    let extra : ChunkExtra :=
      .v5
        { stateRoot := root, outcomeRoot := CryptoHash.zero, validatorProposals := #[],
          gasUsed := 0, gasLimit := c.gasLimit, balanceBurnt := ⟨0⟩, congestionInfo,
          bandwidthRequests := .v1 ⟨#[]⟩, proposedSplit := none }
    genesisExtras :=
      genesisExtras.push (blockShardKey genesisHash genesisEpoch.layout c.shardId, extra)
    progress :=
      { progress with
        outgoing := progress.outgoing.insert (genesisHash.bytes, c.shardId) #[],
        extras := progress.extras.insert (genesisHash.bytes, c.shardId) extra }
  let ops :=
    Near.Node.Apply.genesisOps genesisBlock rec0 zeroRec
      #[(CryptoHash.zero.bytes, genesisEpoch), (genesisHash.bytes, genesisEpoch)] genesisTrieOps
      genesisExtras
  pure
      { metaJson, config, genesis, genesisBlock, genesisRec := rec0, zeroRec, genesisEpoch, state := st,
        progress, ops, params, genesisLine, genesisHash }

end Near.Node.Bootstrap
