import Bridge.Functions.BalanceOf297CopiedBody

/-! Derive input and copied-account allocation room from the initial page budget. -/
namespace WNear.Binary.BalanceOf297AbsentCall
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open WNear.Binary.LookupMapOps (HeapRoomK)
open WNear.Binary.ReadRegister (RegOk)
open WNear.Binary.VecFromElem (roomFor grownLen)
open WNear.Binary.ParseStrSuccess (appendChunks)
open WNear.Binary.ScratchGrow (growthPages)

/-- The initial allowance covers the input allocation and the copied account allocation after
any input allocation growth. The string parser's own `roomRun` remains a separate condition. -/
theorem initial_input_and_copy_room (bs : List UInt8) (a : WNear.AccountId) (q len : Nat)
    (hpos : 0 < bs.length) (hlen : bs.length < 2 ^ 24)
    (hroom : HeapRoomK ((AllocNewCell.cellPages (AllocAlloc.wordsOf (UInt32.ofNat bs.length)) 1).toNat +
      copiedParserPages bs q a + 6) len 2048) :
    RegOk 2048 len (some bs) ∧
      ∀ len', len' = len ∨ len' = grownLen len (UInt32.ofNat bs.length) →
        roomFor (len' + growthPages 0 0 (appendChunks (bs.drop q) []) * 65536)
          2048 (UInt32.ofNat a.val.toUTF8.toList.length) := by
  unfold HeapRoomK at hroom
  obtain ⟨halign, hposlen, hmax, h32⟩ := hroom
  unfold copiedParserPages at hmax h32
  constructor
  · simp only [RegOk]
    refine ⟨hpos, by omega, ?_⟩
    unfold roomFor
    refine ⟨halign, hposlen, ?_, ?_⟩ <;> omega
  · intro len' hstep
    unfold grownLen at hstep
    unfold roomFor
    rcases hstep with rfl | rfl <;> simp_all [Nat.add_mod] <;> omega
end WNear.Binary.BalanceOf297AbsentCall
