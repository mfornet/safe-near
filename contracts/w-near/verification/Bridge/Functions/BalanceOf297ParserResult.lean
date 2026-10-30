import Bridge.Functions.BalanceOf297ParserCompose
import Bridge.Functions.FromSliceSpec
import Bridge.Functions.AllocZeroed

/-! Extract the account and allocator facts needed by the balance handoff. -/
namespace WNear.Binary.BalanceOf297AbsentCall
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open WNear.Binary.AllocInv (heapInv block heapInv_perm)

section Spec
variable {GF : BundledGFunctors} [WasmGS NearState GF]
/-- A public successful parser result supplies a valid owned account and a bounded live block.
The input-vector allocation is moved to the front of the live list for its actual drop. -/
theorem parser_result_resources (n : Nat) (out : UInt32) (a : WNear.AccountId)
    (ip ic : UInt32) (live : List (Nat × Nat)) :
    FromSliceSpec.okAt (GF := GF) n out a ((ip.toNat, ic.toNat) :: live) ⊢
      ∃ (p c : UInt32) (hl F : Nat) (rest : List UInt8),
        ⌜c ≠ 0 ∧ a.val.toUTF8.toList.length = (UInt32.ofNat a.val.utf8ByteSize).toNat ∧
          a.val.toUTF8.toList.length + rest.length = c.toNat ∧
          (UInt32.ofNat a.val.utf8ByteSize).toNat + 4 ≤ 120 ∧ p.toNat + c.toNat ≤ 2 ^ 32⌝ ∗
        n ↦[i32][ out.toNat ] 0 ∗ n ↦[i32][ out.toNat + 4 ] p ∗
        n ↦[i32][ out.toNat + 8 ] c ∗ n ↦[i32][ out.toNat + 12 ] UInt32.ofNat a.val.utf8ByteSize ∗
        n ↦[wms][ p.toNat ] a.val.toUTF8.toList ∗
        n ↦[wms][ p.toNat + a.val.toUTF8.toList.length ] rest ∗
        heapInv n 2048 hl ((ip.toNat, ic.toNat) :: (p.toNat, c.toNat) :: live) F := by
  have hvalid := a.toNear.property
  change validAccountIdBytes a.val.toUTF8.toList = true at hvalid
  simp only [validAccountIdBytes, Bool.and_eq_true, decide_eq_true_eq] at hvalid
  have hsize := Wasm.ByteEncoding.string_utf8_length a.val
  have hL : (UInt32.ofNat a.val.utf8ByteSize).toNat = a.val.toUTF8.toList.length := by
    rw [← hsize]
    simp only [UInt32.toNat_ofNat']
    exact Nat.mod_eq_of_lt (by omega)
  iintro H
  iunfold FromSliceSpec.okAt at H
  icases H with ⟨%p, %c, %hl, %F, %⟨hp, hcap⟩, O0, O4, O8, O12, Hkey, Hrest, Hinv⟩
  iunfold block at Hrest
  icases Hrest with ⟨%rest, %hrest, Hrest⟩
  ihave Hinv := AllocZeroed.heapInv_bound n 2048 hl _ F $$ Hinv
  icases Hinv with ⟨%⟨hbound, hhl⟩, Hinv⟩
  have hpc := hbound p.toNat c.toNat (by simp)
  have hc : c ≠ 0 := by
    intro hc0
    have := congrArg UInt32.toNat hc0
    simp at this
    omega
  ihave Hinv := heapInv_perm n 2048 hl _ _ F (List.Perm.swap _ _ _) $$ Hinv
  iexists p, c, hl, F, rest
  isplitr
  · ipureintro
    refine ⟨hc, hL.symm, ?_, ?_, by omega⟩
    · rw [hrest, hsize]; omega
    · rw [hL]; omega
  rw [hsize]
  iframe O0 O4 O8 O12 Hkey Hrest Hinv
end Spec
end WNear.Binary.BalanceOf297AbsentCall
