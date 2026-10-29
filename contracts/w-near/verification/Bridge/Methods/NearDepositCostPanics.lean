import Bridge.Methods.NearDepositCostOps

/-!
# Uniform operation bounds for the initialized deposit panics

The panic hook formats at most 163 bytes. Its allocator walk is bounded by the
free cells plus the number of growths; its host charge remains explicit.
-/

namespace WNear.Binary.NearDepositGas

open Wasm Wasm.Near WasmLogic NearLogic
open WNear.Binary

variable (cfg : WasmConfig)
local notation "c" => cfg.regularOpCost
local notation "L" => cfg.linearOpBaseCost + cfg.linearOpUnitCost

theorem hook_sink_le (F J B k : Nat) (hF : F + J ≤ 32) (hB : B ≤ 163) (hk : k ≤ 163) :
    HookSink.costHS cfg F J B k ≤ 20000 * c + L := by
  have hw := walk_le cfg (F + J) hF
  have hb : MemCpy.cost B ≤ 2940 := le_trans (FtTotalSupplyMethod.memcpy_le B) (by omega)
  have hm : MemCpy.cost k ≤ 2940 := le_trans (FtTotalSupplyMethod.memcpy_le k) (by omega)
  have hbGas := Nat.mul_le_mul_right c hb
  have hmGas := Nat.mul_le_mul_right c hm
  simp only [HookSink.costHS]
  omega

theorem get_sink_le (F B : Nat) (hF : F ≤ 32) (hB : B ≤ 163) :
    GetSink.costG cfg F B ≤ 16000 * c + L := by
  have hw := walk_le cfg F hF
  have hb : MemCpy.cost B ≤ 2940 := le_trans (FtTotalSupplyMethod.memcpy_le B) (by omega)
  have hbGas := Nat.mul_le_mul_right c hb
  simp only [GetSink.costG]
  simp [activationGas, entryLocals, f781, ValType.default]
  omega

/-- Formatting a `begin_panic` payload and its source location. -/
theorem begin_format_le (F B : Nat) (hF : F + 5 ≤ 32) (hB : B ≤ 163) :
    ToStrPay.costTS cfg F 5 B ≤ 400000 * c + 20 * L := by
  have hs := hook_sink_le cfg F 5 B B hF hB hB
  simp only [ToStrPay.costTS, ToStrPay.KB469, ToStrPay.cost469, PanicDisplay.cost885,
    PanicDisplay.KBA, PanicDisplay.KBB, PanicDisplay.KbB, PanicDisplay.cost880,
    FmtU64.cost870, FmtU64.cost936, FmtStrPad.cost856, FmtWriteN.costN, FmtWriteT.costT]
  simp [activationGas, entryLocals, f746, f471, f872, f759, f469, f885, f856, f886, f880, f870, f936,
    ValType.default]
  omega

/-- The complete `begin_panic`, including the exact `panic_utf8` charge. -/
theorem begin_le (F : Nat) (hF : F + 5 ≤ 32) (bs : List UInt8) (hB : bs.length ≤ 163) (h : NearState) :
    PanicBegin.cost664 cfg (ToStrPay.costTS cfg F 5 bs.length) bs h ≤
      410000 * c + 20 * L + panicUtf8Use h bs.length := by
  have hf := begin_format_le cfg F bs.length hF hB
  simp only [PanicBegin.cost664, PanicBegin.cost662, PanicBegin.cost663, PanicWithHook.cost824,
    PanicHook.cost474]
  simp [activationGas, entryLocals, f679, ValType.default]
  omega

/-- Formatting the supply-overflow message and its source location. -/
theorem supply_le (F : Nat) (hF : F + 6 ≤ 32) (bs : List UInt8) (hB : bs.length ≤ 163) (h : NearState) :
    PanicFmtFull.cost879 cfg F 6 21 bs h ≤ 600000 * c + 30 * L + panicUtf8Use h bs.length := by
  have hs := hook_sink_le cfg F 6 bs.length bs.length hF hB hB
  have hg := get_sink_le cfg F 21 (by omega) (by decide)
  simp only [PanicFmtFull.cost879, PanicFmt.cost817, PanicWithHook.cost824, PanicHook.cost474,
    GetFmt.cost826, PanicFmtFull.costKm, PanicMsg.KBX, PanicDisplay.cost880,
    ToStrMsg.costTSM, ToStrMsg.KB469M, ToStrMsg.cost469M, PanicDisplayMsg.cost885M,
    PanicMsg.KBM, PanicMsg.cost887, PanicDisplay.KBB, PanicDisplay.KbB,
    FmtU64.cost870, FmtU64.cost936, FmtStrPad.cost856, FmtWriteN.costN, FmtWriteT.costT]
  simp [activationGas, entryLocals, f826, f872, f799, f880, f856, f746, f471, f759, f469, f885,
    f887, f870, f936, ValType.default]
  omega

end WNear.Binary.NearDepositGas
