import Bridge.Functions.SerdeErrorCode
import Bridge.Functions.DropVec

/-! # Dropping a syntax error with no owned message -/

namespace WNear.Binary.SerdeErrorDrop

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.Interface (IfaceMod)

section Proof
variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The error-code identity function used by the drop glue. -/
theorem f709_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (ht : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (Cg : Nat) (p : UInt32) :
    ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f709 Cg
      (fun args => iprop(⌜args = [.i32 p]⌝)) (fun _ => 10 * cfg.regularOpCost)
      (fun _ rs => iprop(⌜rs = [.i32 p]⌝)) := by
  iapply MFunSpec_intro
  imodintro
  iintro %args %R %ha Hc
  subst ha
  simp only [f709]
  repeat mstep
  isplitl [Hc]
  · iapply BorrowMut.credits_le
    iframe Hc
    ipureintro; omega
  ipureintro; simp [ht]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- Tags above 1 have no owned String; the error drop returns its 20-byte block. -/
theorem f92_syntax (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (ht : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 5 < lim.maxCallDepth) (Cg maxP len : Nat)
    (live : List (Nat × Nat)) (F : Nat) (v p tag : UInt32) (tail : List UInt8)
    (hv : v.toNat + 4 ≤ 2 ^ 32) (hp : p.toNat + 20 ≤ 2 ^ 32)
    (htag : 2 ≤ tag.toNat) (hl : tail.length = 16) (hmem : (p.toNat, 20) ∈ live) :
    DropVec.dropCode inst mi A ∗ A 709 ↪[wf] FuncInst.wasm types[32]! inst f709 ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f92 Cg
        (fun args => iprop(⌜args = [.i32 v]⌝ ∗ n ↦[i32][ v.toNat ] p ∗
          n ↦[i32][ p.toNat ] tag ∗ n ↦[wms][ p.toNat + 4 ] tail ∗ heapInv n maxP len live F))
        (fun _ => 350 * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ n ↦[i32][ v.toNat ] p ∗
          heapInv n maxP len (live.erase (p.toNat, 20)) (F + 1))) := by
  iintro ⟨#HD, #F709⟩
  ihave #HD' := HD
  iunfold DropVec.dropCode at HD'
  icases HD' with ⟨#Hi, _, _, _, _, _, _, #F311, _⟩
  have hn := hm.mem
  have ha709 := hm.funcs 709 (by decide)
  have ha311 := hm.funcs 311 (by decide)
  have t32 : types[32]!.params.length = 1 := rfl
  have t31 : types[31]!.params.length = 3 := rfl
  ihave #S311 := DropVec.f311_drop (GF := GF) cfg lim (d + 1) types[31]! rfl inst mi A n g ta hm
    (by omega) Cg maxP len live F p 20 4 $$ HD
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%ha, Hv, Htag, Htail, Hh⟩
  subst ha
  simp only [f92]
  mstep
  mstep
  mstep
  mstep
  mstep [Hv]
  mstep
  mstep [Htag]
  mstep
  rw [List.getElem?_eq_none (show [0, 1].length ≤ tag.toNat by simp; omega)]
  mctrl_norm
  repeat mpay
  mstep; mstep [Hv]
  mcall (f709_spec (GF := GF) cfg lim (d + 1) types[32]! rfl inst mi Cg p) using []
  · ipureintro; trivial
  icases HQ with ⟨%hrs⟩
  subst hrs
  mstep; mstep
  ihave Htag := VecFromElem.stk_word n p.toNat tag $$ Htag
  iunfold VecFromElem.stk at Htag
  icases Htag with ⟨%tagBytes, %htb, Htag⟩
  ihave Hb := U128From.memBytes_join n p.toNat 4 tagBytes tail htb $$ [Htag Htail]
  · iframe Htag Htail
  ihave Hb : block n p.toNat 20 $$ [Hb]
  · iunfold block
    iexists tagBytes ++ tail
    iframe Hb
    ipureintro; simp [htb, hl]
  mcall S311 using [Hh Hb]
  · iframe Hh Hb
    ipureintro; exact hmem
  icases HQ with ⟨%hrs, Hh⟩
  subst hrs
  repeat mstep
  isplitl [Hc]
  · iapply BorrowMut.credits_le
    iframe Hc
    ipureintro; omega
  iframe Hv Hh
  ipureintro; simp [ht]

end Proof
end WNear.Binary.SerdeErrorDrop
