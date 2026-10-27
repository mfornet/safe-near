import NearInterface.Boundary

/-! Protocol-only arithmetic for the accepted canonical storage-write branch.
No assertion about parsing or pinning a particular protocol JSON is made here. -/
namespace WNear.Skeleton.CanonicalArithmetic
open Wasm Wasm.Near NearInterface

/-- The maximum accepted one-byte-key write fits within the protocol's gas
allowance reserved by the boundary's generic storage-usage room invariant. -/
def GrowthRoom (cfg : RuntimeConfig) : Prop :=
  1 + cfg.wasm.limits.maxLengthStorageValue + cfg.fees.numExtraBytesRecord ≤
    cfg.wasm.limits.maxGasBurnt

/-- Accepted value length and protocol growth room suffice for native u64
write arithmetic. Rejected oversized values require no such call-local bound. -/
theorem GrowthRoom.write_room {cfg : RuntimeConfig} (h : GrowthRoom cfg)
    (usage valueLength : Nat) (hroom : usage + cfg.wasm.limits.maxGasBurnt < 2 ^ 64)
    (hvalue : valueLength ≤ cfg.wasm.limits.maxLengthStorageValue) :
    usage + 1 + valueLength + cfg.fees.numExtraBytesRecord < 2 ^ 64 := by
  unfold GrowthRoom at h
  omega

/-- Derive the canonical walking method's native write-room premise from the
original shared WF and a protocol-only condition, on the accepted-value branch. -/
theorem write_usage_room (ctx : Context) (raw : RawStorage) (hwf : ctx.WF raw)
    (hprotocol : GrowthRoom ctx.protocol)
    (hvalue : ctx.args.length ≤ ctx.protocol.wasm.limits.maxLengthStorageValue) :
    ctx.storageUsage + 1 + ctx.args.length + ctx.protocol.fees.numExtraBytesRecord < 2 ^ 64 :=
  hprotocol.write_room ctx.storageUsage ctx.args.length hwf.usage_room hvalue

end WNear.Skeleton.CanonicalArithmetic
