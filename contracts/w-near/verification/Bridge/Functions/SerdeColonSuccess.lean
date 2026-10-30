import Bridge.Functions.SerdeEndSeq

/-! # Successful colon and closing-bracket checks with the caller's state framed through -/

namespace WNear.Binary.SerdeColonSuccess

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.SerdeRead (rd wsLen optByte)

section Proof
variable {GF : BundledGFunctors} [WasmGS NearState GF]

set_option maxRecDepth 100000 in
/-- The accepted colon path neither allocates nor touches its reserved stack frame. -/
theorem f89_colon (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 2 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp de ptr : UInt32) (bs : List UInt8) (i : Nat)
    (hlen : bs.length < 2 ^ 32) (hptr : ptr.toNat + bs.length ≤ 2 ^ 32)
    (hde : de.toNat + 12 ≤ 2 ^ 32) (hi : i ≤ bs.length)
    (hc : bs[i + wsLen (bs.drop i)]? = some 0x3A) :
    A 332 ↪[wf] FuncInst.wasm types[11]! inst f332 ∗
      A 333 ↪[wf] FuncInst.wasm types[0]! inst f333 ∗
      A 339 ↪[wf] FuncInst.wasm types[11]! inst f339 ∗ inst ↪[inst] mi ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f89 Cg
        (fun args => iprop(⌜args = [.i32 de]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ rd n de ptr bs i))
        (fun _ => (200 + 96 * wsLen (bs.drop i)) * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          rd n de ptr bs (i + wsLen (bs.drop i) + 1))) := by
  iintro ⟨#F332, #F333, #F339, #Hi⟩
  have hn := hm.mem
  have hg := hm.glob
  have ha339 := hm.funcs 339 (by decide)
  have ha333 := hm.funcs 333 (by decide)
  have t11 : types[11]!.params.length = 1 := rfl
  have t0 : types[0]!.params.length = 1 := rfl
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hrd⟩
  subst hargs
  simp only [f89]
  generalize hw : wsLen (bs.drop i) = w at hc
  generalize hj : i + w = j at hc
  have hjl : j < bs.length := by
    by_contra h
    rw [List.getElem?_eq_none (by omega)] at hc
    cases hc
  rw [show (200 + 96 * w) * cfg.regularOpCost + R =
    100 * cfg.regularOpCost + ((100 + 96 * w) * cfg.regularOpCost + R) by simp only [Nat.add_mul]; omega]
  have key := SerdeRead.f339_spec (GF := GF) cfg lim (d + 1) types[11]! rfl inst mi n hn (A 332) (A 333)
    (hm.funcs 332 (by decide)) (hm.funcs 333 (by decide)) (by omega) Cg de ptr bs i hi hlen hptr hde
  rw [hw, hj] at key
  generalize hW : (100 + 96 * w) * cfg.regularOpCost = W at key ⊢
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep; mstep
  mcall key using [Hrd]
  · iframe Hrd
  clear key
  mcredits (70 * cfg.regularOpCost + R)
  icases HQ with ⟨%hrs, Hrd⟩
  subst hrs
  have hok1 : Numeric.bool (optByte bs[j]? &&& 1 == 0) = 1 := by
    simp only [SerdeRead.optByte_ok]; rfl
  mstep; mstep; mstep; mstep
  mstep_taken with exact hok1
  rw [hc]
  mstep; mstep; mstep; mstep; mstep; mstep; mstep
  mstep_taken with decide
  mstep; mstep; mstep; mstep; mstep; mstep
  mstep_not_taken with decide
  mstep
  mcall (SerdeRead.f333_spec cfg lim (d + 1) types[0]! rfl inst mi n hn Cg de ptr bs j hjl hlen hde) using [Hrd]
  · iframe Hrd
  icases HQ with ⟨%hrs, Hrd⟩
  subst hrs
  mstep; mstep; mstep
  (try simp only [Post.mloop]); (try mctrl_norm); (repeat mpay)
  mstep; mstep; mstep; mstep [Hg]
  rw [show sp - 16 + 16 = sp by simp]
  repeat mstep
  isplitl [Hc]
  · iapply BorrowMut.credits_le
    iframe Hc
    ipureintro; omega
  iframe Hg Hrd
  ipureintro; simp [htype]

set_option maxRecDepth 100000 in
/-- The accepted closing-bracket path neither allocates nor touches its reserved stack frame. -/
theorem f91_close (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 2 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp de ptr : UInt32) (bs : List UInt8) (i : Nat)
    (hlen : bs.length < 2 ^ 32) (hptr : ptr.toNat + bs.length ≤ 2 ^ 32)
    (hde : de.toNat + 12 ≤ 2 ^ 32) (hi : i ≤ bs.length)
    (hc : bs[i + wsLen (bs.drop i)]? = some 0x5D) :
    A 332 ↪[wf] FuncInst.wasm types[11]! inst f332 ∗
      A 333 ↪[wf] FuncInst.wasm types[0]! inst f333 ∗
      A 339 ↪[wf] FuncInst.wasm types[11]! inst f339 ∗ inst ↪[inst] mi ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f91 Cg
        (fun args => iprop(⌜args = [.i32 de]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ rd n de ptr bs i))
        (fun _ => (400 + 96 * wsLen (bs.drop i)) * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          rd n de ptr bs (i + wsLen (bs.drop i) + 1))) := by
  iintro ⟨#F332, #F333, #F339, #Hi⟩
  have hn := hm.mem
  have hg := hm.glob
  have ha339 := hm.funcs 339 (by decide)
  have ha333 := hm.funcs 333 (by decide)
  have t11 : types[11]!.params.length = 1 := rfl
  have t0 : types[0]!.params.length = 1 := rfl
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hrd⟩
  subst hargs
  simp only [f91]
  generalize hw : wsLen (bs.drop i) = w at hc
  generalize hj : i + w = j at hc
  have hjl : j < bs.length := by
    by_contra h
    rw [List.getElem?_eq_none (by omega)] at hc
    cases hc
  rw [show (400 + 96 * w) * cfg.regularOpCost + R =
    300 * cfg.regularOpCost + ((100 + 96 * w) * cfg.regularOpCost + R) by simp only [Nat.add_mul]; omega]
  have key := SerdeRead.f339_spec (GF := GF) cfg lim (d + 1) types[11]! rfl inst mi n hn (A 332) (A 333)
    (hm.funcs 332 (by decide)) (hm.funcs 333 (by decide)) (by omega) Cg de ptr bs i hi hlen hptr hde
  rw [hw, hj] at key
  generalize hW : (100 + 96 * w) * cfg.regularOpCost = W at key ⊢
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep; mstep
  mcall key using [Hrd]
  · iframe Hrd
  clear key
  mcredits (270 * cfg.regularOpCost + R)
  icases HQ with ⟨%hrs, Hrd⟩
  subst hrs
  have hok1 : Numeric.bool (optByte bs[j]? &&& 1 == 0) = 1 := by
    simp only [SerdeRead.optByte_ok]; rfl
  mstep; mstep; mstep; mstep
  mstep_taken with exact hok1
  rw [hc]
  mstep; mstep; mstep; mstep; mstep; mstep
  mstep_taken with decide
  mstep; mstep; mstep; mstep; mstep; mstep; mstep
  rw [SerdeRead.optByte_byte]
  mstep; mstep; mstep
  mstep_taken with decide
  mstep
  mcall (SerdeRead.f333_spec cfg lim (d + 1) types[0]! rfl inst mi n hn Cg de ptr bs j hjl hlen hde) using [Hrd]
  · iframe Hrd
  icases HQ with ⟨%hrs, Hrd⟩
  subst hrs
  mstep; mstep
  (try simp only [Post.mloop]); (try mctrl_norm); (repeat mpay)
  mstep; mstep; mstep; mstep [Hg]
  rw [show sp - 32 + 32 = sp by simp]
  repeat mstep
  isplitl [Hc]
  · iapply BorrowMut.credits_le
    iframe Hc
    ipureintro; omega
  iframe Hg Hrd
  ipureintro; simp [htype]

end Proof
end WNear.Binary.SerdeColonSuccess
