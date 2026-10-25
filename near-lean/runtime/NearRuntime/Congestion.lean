import NearRuntime.Wire
import Lean.Data.Json

/-! # Congestion control

`core/primitives/src/congestion_info.rs` and `core/parameters`' `CongestionControlConfig`: the
congestion info a chunk header carries (`CongestionInfoV1`), the levels derived from it, and what
they decide: how much gas other shards may send, whether a shard accepts transactions, and which
shard may send to a fully congested one. Levels are `f64` in nearcore and `Float` here; every
operation is the same IEEE-754 double operation in the same order.

Admission (`shardAcceptsTransactions`) is not part of `Runtime::apply`: chunk producers and
validators check it in `chain/chain/src/runtime/mod.rs` (`validate_tx`, `prepare_transactions`) before a
transaction reaches a chunk. It lives here because it is the same decision procedure. -/
namespace Near.Congestion

open Lean

/-- `CongestionControlConfig` plus the receipt size limit that bounds forwarding. -/
structure Config where
  maxCongestionIncomingGas : Nat
  maxCongestionOutgoingGas : Nat
  maxCongestionMemoryConsumption : Nat
  maxCongestionMissedChunks : Nat
  maxOutgoingGas : Nat
  minOutgoingGas : Nat
  allowedShardOutgoingGas : Nat
  maxTxGas : Nat
  minTxGas : Nat
  rejectTxCongestionThreshold : Float
  outgoingReceiptsUsualSizeLimit : Nat
  outgoingReceiptsBigSizeLimit : Nat
  /-- `wasm_config.limit_config.max_receipt_size`. -/
  maxReceiptSize : Nat
  /-- `ProtocolFeature::ClampOutgoingGasAdmission` (protocol 85): admission uses at most
  `allowed_shard_outgoing_gas` per receipt. -/
  clampOutgoingGasAdmission : Bool
  deriving Inhabited

namespace Config

private def nat (j : Json) (k : String) : Except String Nat := do
  match (← j.getObjVal? k).getNat? with
  | .ok n => pure n
  | .error _ => throw s!"key {k} is not a natural number"

/-- Read the configuration out of a `runtime_config_v<N>.json` document. -/
def ofJson (j : Json) (protocol : Nat) : Except String Config := do
  let c ← j.getObjVal? "congestion_control_config"
  let limits ← (← j.getObjVal? "wasm_config").getObjVal? "limit_config"
  let threshold ← match (← c.getObjVal? "reject_tx_congestion_threshold") with
    | .num n => pure (Float.ofScientific n.mantissa.toNat (n.exponent != 0) n.exponent)
    | _ => throw "reject_tx_congestion_threshold is not a number"
  return {
    maxCongestionIncomingGas := ← nat c "max_congestion_incoming_gas"
    maxCongestionOutgoingGas := ← nat c "max_congestion_outgoing_gas"
    maxCongestionMemoryConsumption := ← nat c "max_congestion_memory_consumption"
    maxCongestionMissedChunks := ← nat c "max_congestion_missed_chunks"
    maxOutgoingGas := ← nat c "max_outgoing_gas"
    minOutgoingGas := ← nat c "min_outgoing_gas"
    allowedShardOutgoingGas := ← nat c "allowed_shard_outgoing_gas"
    maxTxGas := ← nat c "max_tx_gas"
    minTxGas := ← nat c "min_tx_gas"
    rejectTxCongestionThreshold := threshold
    outgoingReceiptsUsualSizeLimit := ← nat c "outgoing_receipts_usual_size_limit"
    outgoingReceiptsBigSizeLimit := ← nat c "outgoing_receipts_big_size_limit"
    maxReceiptSize := ← nat limits "max_receipt_size"
    clampOutgoingGasAdmission := protocol ≥ 85 }

/-- Load `runtime_config_v<protocol>.json` from `dir` (the files `RuntimeConfig.load` reads). -/
def load (dir : System.FilePath) (protocol : Nat) : IO Config := do
  let path := dir / s!"runtime_config_v{protocol}.json"
  match Json.parse (← IO.FS.readFile path) >>= (ofJson · protocol) with
  | .ok config => pure config
  | .error e => throw (IO.userError s!"{path}: {e}")

end Config

/-- `CongestionInfoV1`. -/
structure Info where
  /-- Gas of the receipts in the delayed queue (`u128`). -/
  delayedGas : Nat := 0
  /-- Gas of the receipts in the outgoing buffers (`u128`). -/
  bufferedGas : Nat := 0
  /-- Borsh size of the receipts in the delayed queue and the buffers (`u64`). -/
  receiptBytes : Nat := 0
  /-- If fully congested, only this shard may send (`u16`). -/
  allowedShard : Nat := 0
  deriving BEq, Repr, Inhabited

namespace Info

/-- Borsh `CongestionInfo`: variant 0 and the four fields. -/
def toBorsh (info : Info) : Bytes :=
  [0] ++ Wire.little 16 info.delayedGas ++ Wire.little 16 info.bufferedGas ++
    Wire.little 8 info.receiptBytes ++ Wire.little 2 info.allowedShard

def ofBorsh : Bytes → Except String Info := Wire.run do
  unless (← Wire.uint 1) == 0 do throw "unknown congestion info version"
  let delayedGas ← Wire.uint 16
  let bufferedGas ← Wire.uint 16
  let receiptBytes ← Wire.uint 8
  return { delayedGas, bufferedGas, receiptBytes, allowedShard := ← Wire.uint 2 }

private def checkedAdd (what : String) (bound total delta : Nat) : Except String Nat :=
  if total + delta < bound then pure (total + delta) else throw s!"{what} overflows"

private def checkedSub (what : String) (total delta : Nat) : Except String Nat :=
  if delta ≤ total then pure (total - delta) else throw s!"{what} underflows"

def addReceiptBytes (info : Info) (bytes : Nat) : Except String Info := do
  return { info with receiptBytes := ← checkedAdd "add_receipt_bytes" (2 ^ 64) info.receiptBytes bytes }

def removeReceiptBytes (info : Info) (bytes : Nat) : Except String Info := do
  return { info with receiptBytes := ← checkedSub "remove_receipt_bytes" info.receiptBytes bytes }

def addDelayedGas (info : Info) (gas : Nat) : Except String Info := do
  return { info with delayedGas := ← checkedAdd "add_delayed_receipt_gas" (2 ^ 128) info.delayedGas gas }

def removeDelayedGas (info : Info) (gas : Nat) : Except String Info := do
  return { info with delayedGas := ← checkedSub "remove_delayed_receipt_gas" info.delayedGas gas }

def addBufferedGas (info : Info) (gas : Nat) : Except String Info := do
  return { info with bufferedGas := ← checkedAdd "add_buffered_receipt_gas" (2 ^ 128) info.bufferedGas gas }

def removeBufferedGas (info : Info) (gas : Nat) : Except String Info := do
  return { info with bufferedGas := ← checkedSub "remove_buffered_receipt_gas" info.bufferedGas gas }

/-- `finalize_allowed_shard`: round robin over the layout's shard order, seeded by
`block_height.wrapping_add(shard_index)`. -/
def finalizeAllowedShard (info : Info) (ownShard : Nat) (allShards : List Nat) (seed : Nat) : Info :=
  { info with allowedShard := match allShards with
      | [] => ownShard
      | _ => allShards.getD (seed % allShards.length) ownShard }

end Info

/-- `u64 as f64`: round to nearest even, as the hardware conversion does. -/
private def toFloat (n : Nat) : Float := (UInt64.ofNat n).toFloat

/-- `clamped_f64_fraction`: `value / max` clamped to `[0, 1]`, exactly `1.0` once `value ≥ max`. -/
def clampedFraction (value max : Nat) : Float :=
  if max ≤ value then 1.0 else toFloat value / toFloat max

/-- `mix`: linear interpolation of two `u64` by `ratio`, rounded half away from zero. -/
def mix (left right : Nat) (ratio : Float) : Nat :=
  let leftPart := toFloat left * (1.0 - ratio)
  let rightPart := toFloat right * ratio
  (leftPart + rightPart).round.toUInt64.toNat

/-- `CongestionControl`: a shard's config, last known info and missed chunks. -/
structure Control where
  config : Config
  info : Info
  missedChunks : Nat

namespace Control

def incoming (c : Control) : Float :=
  clampedFraction c.info.delayedGas c.config.maxCongestionIncomingGas

def outgoing (c : Control) : Float :=
  clampedFraction c.info.bufferedGas c.config.maxCongestionOutgoingGas

def memory (c : Control) : Float :=
  clampedFraction c.info.receiptBytes c.config.maxCongestionMemoryConsumption

def missed (c : Control) : Float :=
  if c.missedChunks ≤ 1 then 0.0 else clampedFraction c.missedChunks c.config.maxCongestionMissedChunks

private def fmax (a b : Float) : Float := if a < b then b else a

/-- `congestion_level`: the largest of the four. -/
def level (c : Control) : Float := fmax (fmax (fmax c.incoming c.outgoing) c.memory) c.missed

/-- `is_fully_congested`: `clamped_f64_fraction` returns exactly `1.0`. -/
def isFullyCongested (level : Float) : Bool := level == 1.0

/-- `outgoing_gas_limit`: how much gas `sender` may send to this shard. -/
def outgoingGasLimit (c : Control) (sender : Nat) : Nat :=
  let level := c.level
  if isFullyCongested level then
    if sender == c.info.allowedShard then c.config.allowedShardOutgoingGas else 0
  else mix c.config.maxOutgoingGas c.config.minOutgoingGas level

/-- `outgoing_size_limit`. -/
def outgoingSizeLimit (c : Control) (sender : Nat) : Nat :=
  if sender == c.info.allowedShard then c.config.outgoingReceiptsBigSizeLimit
  else c.config.outgoingReceiptsUsualSizeLimit

/-- `process_tx_limit`: gas a chunk spends on converting new transactions. -/
def processTxLimit (c : Control) : Nat := mix c.config.maxTxGas c.config.minTxGas c.incoming

/-- Why a shard turns transactions away (`RejectTransactionReason`). -/
inductive Rejection
  | missedChunks (count : Nat)
  | incoming
  | outgoing
  | memory
  deriving BEq, Repr

/-- `shard_accepts_transactions`: `none` accepts; a level at or above
`reject_tx_congestion_threshold` rejects, naming the first of missed chunks, incoming, outgoing and
memory congestion that reaches the level. -/
def shardAcceptsTransactions (c : Control) : Option Rejection :=
  let level := c.level
  if level < c.config.rejectTxCongestionThreshold then none
  else if c.missed ≥ level then some (.missedChunks c.missedChunks)
  else if c.incoming ≥ level then some .incoming
  else if c.outgoing ≥ level then some .outgoing
  else some .memory

end Control

end Near.Congestion
