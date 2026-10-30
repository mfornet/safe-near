import Bridge.Functions.BalanceOf297AbsentCopy
import Bridge.Functions.ToVec

/-! The actual function-297 call which serializes a zero balance. -/

namespace WNear.Binary.BalanceOf297AbsentCall

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.VecFromElem (stk roomFor grownLen)
open WNear.Binary.FmtGrow (newCap)
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.FmtString (kOf)
open WNear.Binary.FmtU128 (val)
open WNear.Binary.FmtDigits (decDigits)
open WNear.Binary.VecWithCap (okG)
open WNear.Binary.AllocInv (heapInv)
open WNear.Binary.ToVec
open WNear.Binary.U128From (u128Bytes)

/-- Actual instructions setting up and calling the U128 JSON serializer. -/
def formatCode : List Instr :=
  [.local_get 0, .i32_const 88, .i32_binop .add,
   .local_get 0, .i32_const 128, .i32_binop .add, .call 96]

theorem formatCode_eq : (f297.body.drop 113).take 7 = formatCode := by rfl

section Spec
variable {GF : BundledGFunctors} [WasmGS NearState GF]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- The actual call to function 96 serializes the copied zero value. -/
theorem format_zero (cfg : WasmConfig) (lim : ExecLimits) (d inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta)
    (hd : d + 28 < lim.maxCallDepth) (Cg R : Nat) (gt : GlobalType)
    (s x1 : UInt32) (x2 : UInt64) (x3 ptr0 aidx : UInt32)
    (ob : List UInt8) (maxP hl : Nat) (live : List (Nat × Nat))
    (hs : 416 ≤ s.toNat) (hframe : s.toNat + 160 ≤ 2 ^ 32) (hob : ob.length = 16)
    (hr1 : roomFor hl maxP 128)
    (hr2 : ∀ hl1, hl1 = hl ∨ hl1 = grownLen hl 128 → roomFor hl1 maxP (newCap 0 (kOf (val 0 0))))
    (F : Nat) (hF : okG F) (Φ : Post NearState GF) :
    tvCode n maxP inst mi A ∗ A 96 ↪[wf] FuncInst.wasm types[14]! inst f96 ∗
      inst ↪[inst] mi ∗ credits Cg (17 * cfg.regularOpCost + cost96F cfg F 0 0 + R) ∗
      g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 416) 416 ∗
      n ↦[wms][ (s + 88).toNat ] ob ∗ n ↦[wms][ (s + 128).toNat ] u128Bytes 0 0 ∗
      tvData n ta ptr0 (A 759) (A 353) ∗ vt n 1057464 aidx ta (A 578) ∗ heapInv n maxP hl live F ∗
      ▷ (∀ rs, (credits Cg R ∗ ⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 416) 416 ∗
        n ↦[wms][ (s + 128).toNat ] u128Bytes 0 0 ∗ tvData n ta ptr0 (A 759) (A 353) ∗
        vt n 1057464 aidx ta (A 578) ∗
        ∃ q : UInt32, ∃ rest : List UInt8, ⌜rest.length = 128 - ((kOf (val 0 0)).toNat + 2)⌝ ∗
          n ↦[i32][ (s + 88).toNat ] 0 ∗ n ↦[i32][ (s + 88).toNat + 4 ] q ∗
          n ↦[i32][ (s + 88).toNat + 8 ] 128 ∗ n ↦[i32][ (s + 88).toNat + 12 ] (0 + kOf (val 0 0) + 2) ∗
          n ↦[wms][ q.toNat ] (([34] ++ decDigits (val 0 0) ++ [34]) ++ rest) ∗
          ∃ hl', heapInv n maxP hl' ((q.toNat, 128) :: live) (F + 1)) -∗
        Φ.normal rs (frame inst mi s x1 x2 x3)) ⊢
    mwpi cfg lim d (frame inst mi s x1 x2 x3) [] ((f297.body.drop 113).take 7) Φ := by
  iintro ⟨#Hcode, #H96, #Hi, Hc, Hg, Hs, Ho, Hv, HD, Hvt, Hh, HΦ⟩
  have ha96 := hm.funcs 96 (by decide)
  have t14 : types[14]!.params.length = 2 := by rfl
  have hlt := s.toNat_lt
  ihave #S96 := ToVec.f96_spec (GF := GF) cfg lim (d + 1) types[14]! rfl inst mi A n g ta hm (by omega)
    Cg gt s (s + 88) (s + 128) ptr0 aidx ob maxP hl live 0 0 hs hob
    (by simp [UInt32.toNat_add]; omega) (by simp [UInt32.toNat_add]; omega) hr1 hr2 F hF $$ Hcode
  rw [formatCode_eq]
  simp only [formatCode, frame]
  mstep; mstep; mstep; mstep; mstep; mstep
  mcall S96 using [Hg Hs Ho Hv HD Hvt Hh]
  · iframe Hg Hs Ho Hv HD Hvt Hh
  mcredits R
  ispecialize HΦ $$ %rs
  iapply HΦ $$ [Hc HQ]
  iframe Hc HQ

end Spec
end WNear.Binary.BalanceOf297AbsentCall
