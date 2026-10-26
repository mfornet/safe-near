import Lean.Data.Json
import NearNode.Chain.State
import NearNode.Epoch

/-!
# Which shards a node tracks

`ShardTracker` of nearcore (`chain/epoch-manager/src/shard_tracker.rs`, `TrackedShardsConfig` of
`core/chain-configs/src/client_config.rs`, `Config::tracked_shards_config` of `nearcore/src/config.rs`) at the
pinned revision.

* **`TrackedShardsConfig`** is the `tracked_shards_config` member of `config.json`: `"NoShards"`,
  `"AllShards"`, `{"Shards": ["s0.v3", ...]}` (a `ShardUId` is `"s<shard>.v<version>"` or the map
  `{"version", "shard_id"}`), `{"Accounts": [...]}`, `{"Schedule": [[...], ...]}` and
  `{"ShadowValidator": "account"}`. A `config.json` without it falls back to the deprecated members
  (`tracked_shards`, `tracked_shard_schedule`, `tracked_shadow_validator`, `tracked_accounts`, in that order of
  priority) and, with none of them, to `NoShards`: that is what a validator of nearcore tracks by
  configuration (`neard init` and `neard localnet` write `AllShards`).
* **A validator tracks more than its configuration says**: the shards it is a chunk producer of
  (`cares_about_shard_in_epoch`: the account is in `chunk_producers_settlement` of the shard in that epoch). Every
  answer below is `ShardTracker::cares_about_shard_in_epoch_from_prev_hash` for the node itself (`is_me`).
* **Epochs** are relative to the previous block `prev` of the block in question: the epoch of the block that
  follows it (`Current`), the next one (`Next`) and the one before (`Previous`).
* **Application modes** (`ApplyChunksMode`): `shouldApplyChunk`.
* **State sync** (`get_shards_to_state_sync`, `should_catch_up_shard`): the shards the node will track in the next epoch
  and neither tracks now nor tracked in the epoch before.

The shard layout of the node is static (`Config.staticShardLayout`), so a shard of this epoch is a shard of the next
and `will_shard_layout_change` is false.
-/

namespace Near.Node.Chain

open Near.Node

/-- `TrackedShardsConfig`. A `ShardUId` is its version and shard id. -/
inductive TrackedShardsConfig where
  | noShards
  | allShards
  | shards (uids : Array (UInt32 × UInt32))
  | accounts (accounts : Array AccountId)
  | schedule (sets : Array (Array UInt64))
  | shadowValidator (account : AccountId)
  deriving BEq, Inhabited

namespace TrackedShardsConfig

/-- The text of the configuration, for logs. -/
def describe : TrackedShardsConfig → String
  | .noShards => "NoShards"
  | .allShards => "AllShards"
  | .shards u => s!"Shards({u.toList.map fun (v, s) => s!"s{s}.v{v}"})"
  | .accounts a => s!"Accounts({a.toList.map (·.val)})"
  | .schedule s => s!"Schedule({s.toList.map (·.toList)})"
  | .shadowValidator a => s!"ShadowValidator({a.val})"

/-- `ShardUId::from_str` (`"s<shard>.v<version>"`) or the map `{"version", "shard_id"}`. -/
def shardUIdOfJson (j : Lean.Json) : Except String (UInt32 × UInt32) := do
  match j with
  | .str s =>
    let parts := s.splitOn "."
    unless parts.length == 2 do
      throw s!"shard uid {s}: the shard and the version must be separated by \".\""
    let shardPart := parts[0]!
    let versionPart := parts[1]!
    let some shard := (shardPart.dropPrefix? "s").bind (·.toString.toNat?)
      | throw s!"shard uid {s}: the shard id must be \"s\" and a number"
    let some version := (versionPart.dropPrefix? "v").bind (·.toString.toNat?)
      | throw s!"shard uid {s}: the version must be \"v\" and a number"
    pure (version.toUInt32, shard.toUInt32)
  | .obj _ =>
    let version ← j.getObjValAs? Nat "version"
    let shard ← j.getObjValAs? Nat "shard_id"
    pure (version.toUInt32, shard.toUInt32)
  | _ =>
    throw "a shard uid is a string or a map"

private def stringsOfJson (j : Lean.Json) : Except String (Array String) := do
  (← j.getArr?).mapM fun x => x.getStr?

private def shardIdsOfJson (j : Lean.Json) : Except String (Array UInt64) := do
  (← j.getArr?).mapM fun x => do
      pure (← x.getNat?).toUInt64

/-- The serde form of the enum: a bare string for the unit variants, a one-member map for the others. -/
def ofJson (j : Lean.Json) : Except String TrackedShardsConfig := do
  match j with
  | .str "NoShards" =>
    pure .noShards
  | .str "AllShards" =>
    pure .allShards
  | .str other =>
    throw s!"tracked_shards_config: unknown variant {other}"
  | .obj kvs =>
    match kvs.toList with
    | [("Shards", v)] =>
      pure (.shards (← (← v.getArr?).mapM shardUIdOfJson))
    | [("Accounts", v)] =>
      pure (.accounts ((← stringsOfJson v).map fun a => ⟨a⟩))
    | [("Schedule", v)] =>
      pure (.schedule (← (← v.getArr?).mapM shardIdsOfJson))
    | [("ShadowValidator", v)] =>
      pure (.shadowValidator ⟨← v.getStr?⟩)
    | _ =>
      throw "tracked_shards_config: expected one variant"
  | _ =>
    throw "tracked_shards_config: a string or a map"

/-- `Config::tracked_shards_config` for the members of a `config.json` object: `tracked_shards_config`, else the
deprecated members (`TrackedShardsConfig::from_deprecated_config_values`), else `NoShards`. -/
def ofConfig (cfg : Lean.Json) : Except String TrackedShardsConfig := do
  let member (name : String) : Option Lean.Json :=
    match cfg.getObjVal? name with
    | .ok .null => none
    | .ok v => some v
    | .error _ => none
  if let some v := member "tracked_shards_config" then
    return ← ofJson v
  -- a non-empty `tracked_shards` has always meant all shards, whatever it lists
  if let some v := member "tracked_shards" then
    if !(← v.getArr?).isEmpty then
      return .allShards
  if let some v := member "tracked_shard_schedule" then
    let sets ← (← v.getArr?).mapM shardIdsOfJson
    if !sets.isEmpty then
      return .schedule sets
  if let some v := member "tracked_shadow_validator" then
    return .shadowValidator ⟨← v.getStr?⟩
  if let some v := member "tracked_accounts" then
    return .accounts ((← stringsOfJson v).map fun a => ⟨a⟩)
  return .noShards

/-- The command line value of `--tracked-shards`: the JSON of `tracked_shards_config`, or `all` / `none`. -/
def ofFlag (s : String) : Except String TrackedShardsConfig := do
  match s.trimAscii.toString with
  | "all" | "All" | "AllShards" =>
    pure .allShards
  | "none" | "None" | "NoShards" =>
    pure .noShards
  | text =>
    match Lean.Json.parse text with
    | .ok j =>
      ofJson j
    | .error e =>
      throw s!"--tracked-shards: {e}"

/-- `tracks_all_shards`. -/
def tracksAllShards : TrackedShardsConfig → Bool
  | .allShards => true
  | _ => false

end TrackedShardsConfig

/-- Which epoch of a previous block a question is about (`EpochSelection`). -/
inductive EpochSelection where
  | previous
  | current
  | next
  deriving BEq, Inhabited

/-- `ApplyChunksMode`. -/
inductive ApplyMode where
  /-- The next epoch's shard states are not ready: this epoch's shards, and those of the next epoch the node already
  has the state of. -/
  | notCaughtUp
  /-- This epoch's and the next epoch's. -/
  | isCaughtUp
  /-- The shards being caught up, which `notCaughtUp` did not apply. -/
  | catchingUp
  deriving BEq, Inhabited

/-- A node's shard tracking: the configuration and, for a validator, its account. -/
structure ShardTracker where
  config : TrackedShardsConfig := .noShards
  /-- The validator account (`validator_signer`); none for a node that is not a validator. -/
  me : Option AccountId := none
  deriving Inhabited

/-- `get_prev_epoch_id_from_prev_block`: when the block after `prev` starts an epoch, the epoch of `prev`;
otherwise the epoch before the one `prev` is in. The first epoch is its own predecessor (the first block's
`prev_hash` is the zero hash, whose block info carries the zero epoch id). -/
def ChainState.prevEpochIdFromPrevBlock (st : ChainState) (prev : CryptoHash) : Result EpochId := do
  if ← st.isNextBlockEpochStart prev then
    st.epochIdOf prev
  else
    let b ← st.block prev
    let first ← st.block b.info.epochFirstBlock
    if first.info.prevHash == CryptoHash.zero then
      pure b.info.epochId
    else
      st.epochIdOf first.info.prevHash

/-- `EpochManagerAdapter::cares_about_shard_in_epoch`: the account is one of the chunk producers of the shard in the
epoch. -/
def ChainState.caresAboutShardInEpoch (st : ChainState) (epoch : EpochId) (account : AccountId)
    (shard : ShardId) : Result Bool := do
  let e ← st.epoch epoch
  let some i := e.layout.getShardIndex shard
    | fail "ShardingError" s!"invalid shard id {shard}"
  let producers := (e.info.chunkProducersSettlement[i]?).getD #[]
  pure (producers.any fun id => (e.info.getValidator id).any (·.accountId == account))

namespace ShardTracker

/-- `tracks_shard_at_epoch`: what the configuration alone says. -/
def tracksShardAtEpoch (t : ShardTracker) (st : ChainState) (shard : ShardId) (epoch : EpochId) :
    Result Bool := do
  match t.config with
  | .noShards =>
    pure false
  | .allShards =>
    pure true
  | .shards uids =>
    let e ← st.epoch epoch
    if (e.layout.getShardIndex shard).isNone then
      pure false
    else
      -- a shard of a static layout is a descendant of itself only
      pure (uids.any fun (v, s) => v == e.layout.version && s.toUInt64 == shard)
  | .accounts accounts =>
    let e ← st.epoch epoch
    pure (accounts.any fun a => e.layout.accountIdToShardId a == some shard)
  | .schedule sets =>
    if sets.isEmpty then
      pure false
    else
      let e ← st.epoch epoch
      let index := e.info.view.epochHeight % sets.size
      pure ((sets[index]!).contains shard)
  | .shadowValidator account =>
    st.caresAboutShardInEpoch epoch account shard

/-- `cares_about_shard_in_epoch_from_prev_hash` for the node itself (`is_me`). Errors are `false`, as in nearcore
(`unwrap_or(false)`). -/
def caresAbout (t : ShardTracker) (st : ChainState) (prev : CryptoHash) (shard : ShardId)
    (selection : EpochSelection) : Bool :=
  let epoch : Result EpochId :=
    match selection with
    | .previous => st.prevEpochIdFromPrevBlock prev
    | .current => st.epochIdFromPrevBlock prev
    | .next => st.nextEpochIdFromPrevBlock prev
  let assigned : Bool :=
    match t.me, epoch with
    | some account, .ok id => ((st.caresAboutShardInEpoch id account shard).toOption).getD false
    | _, _ => false
  if assigned then
    -- the node has to track it because of its validation duties
    true
  else
    match t.config with
    | .noShards => false
    | .allShards => true
    | _ =>
      match epoch with
      | .ok id => ((t.tracksShardAtEpoch st shard id).toOption).getD false
      | .error _ => false

/-- `cares_about_shard`: the block after `prev`. -/
def caresAboutShard (t : ShardTracker) (st : ChainState) (prev : CryptoHash) (shard : ShardId) :
    Bool :=
  t.caresAbout st prev shard .current

/-- `will_care_about_shard`: in the epoch after the block after `prev`. -/
def willCareAboutShard (t : ShardTracker) (st : ChainState) (prev : CryptoHash) (shard : ShardId) :
    Bool :=
  t.caresAbout st prev shard .next

/-- `cared_about_shard_in_prev_epoch_from_prev_hash`. -/
def caredAboutShardInPrevEpoch (t : ShardTracker) (st : ChainState) (prev : CryptoHash)
    (shard : ShardId) : Bool :=
  t.caresAbout st prev shard .previous

/-- `cares_about_shard_this_or_next_epoch`. -/
def caresAboutShardThisOrNextEpoch (t : ShardTracker) (st : ChainState) (prev : CryptoHash)
    (shard : ShardId) : Bool :=
  t.caresAboutShard st prev shard || t.willCareAboutShard st prev shard

/-- `should_apply_chunk` from the three answers it is made of. -/
def shouldApplyOf (mode : ApplyMode) (this next prev : Bool) : Bool :=
  match mode with
  | .notCaughtUp => this || (next && prev)
  | .isCaughtUp => this || next
  | .catchingUp => !this && next && !prev

/-- `should_apply_chunk`: whether the chunk of `shard` in the block after `prev` is applied in this mode. A chunk
is applied once: in `notCaughtUp` or `isCaughtUp` when the node already has the state, in `catchingUp` when the
state came from a state sync. -/
def shouldApplyChunk (t : ShardTracker) (st : ChainState) (mode : ApplyMode) (prev : CryptoHash)
    (shard : ShardId) : Bool :=
  shouldApplyOf mode (t.caresAboutShard st prev shard) (t.willCareAboutShard st prev shard)
    (t.caredAboutShardInPrevEpoch st prev shard)

/-- `should_catch_up_shard`: the node will track the shard next epoch, does not now, and did not in the epoch before. -/
def shouldCatchUpShard (t : ShardTracker) (st : ChainState) (prev : CryptoHash) (shard : ShardId) :
    Bool :=
  t.willCareAboutShard st prev shard && !t.caresAboutShard st prev shard &&
    !t.caredAboutShardInPrevEpoch st prev shard

/-- `get_shards_to_state_sync`: the shards of the epoch of the block after `prev` to download the state of. -/
def shardsToStateSync (t : ShardTracker) (st : ChainState) (prev : CryptoHash) :
    Result (Array ShardId) := do
  let epoch ← st.epochIdFromPrevBlock prev
  let e ← st.epoch epoch
  pure (e.layout.shardIds.filter fun s => t.shouldCatchUpShard st prev s)

/-- The shards whose chunks the node applies in `mode` in the block after `prev`, in layout order. -/
def shardsToApply (t : ShardTracker) (st : ChainState) (mode : ApplyMode) (prev : CryptoHash) :
    Result (Array ShardId) := do
  let epoch ← st.epochIdFromPrevBlock prev
  let e ← st.epoch epoch
  pure (e.layout.shardIds.filter fun s => t.shouldApplyChunk st mode prev s)

/-- `Chain::should_produce_state_witness_for_this_or_next_epoch` for the chunks of shards (the shards of the layout the
node tracks this epoch or the next). -/
def shardsThisOrNext (t : ShardTracker) (st : ChainState) (prev : CryptoHash) :
    Result (Array ShardId) := do
  let epoch ← st.epochIdFromPrevBlock prev
  let e ← st.epoch epoch
  pure (e.layout.shardIds.filter fun s => t.caresAboutShardThisOrNextEpoch st prev s)

end ShardTracker

end Near.Node.Chain
