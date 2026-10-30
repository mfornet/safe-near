import Bridge.Functions.SerdeIgnValue
import Bridge.Functions.SerdeStructObjKeyState
import Bridge.Functions.SerdeColonSuccess

/-! # Ignored shallow values with reusable scratch and a retained account-id String -/

namespace WNear.Binary.SerdeIgnReuse

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.AllocTwo (code310)
open WNear.Binary.VecFromElem (stk)
open WNear.Binary.SerdeRead (rd wsLen)
open WNear.Binary.SerdeIgnValue (scratchTables)
open WNear.Binary.SerdeStructObjKeyState (Bounds core member)
open WNear.IgnoreShallow (ign1 ign1R)

section Proof
variable {GF : BundledGFunctors} [WasmGS NearState GF]

set_option maxRecDepth 100000 in
/-- The actual colon/ignored-value call preserves scratch's pointer and capacity on a shallow value. -/
theorem f201_shallow (cfg : WasmConfig) (lim : ExecLimits) (d inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 9 < lim.maxCallDepth)
    (Cg : Nat) (gt : GlobalType) (sp acc de ptr ptrS capS : UInt32) (bs : List UInt8)
    (i maxP : Nat) (rest : List UInt8)
    (hlen : bs.length < 2 ^ 32) (hptr : ptr.toNat + bs.length < 2 ^ 32)
    (hde : de.toNat + 24 ≤ 2 ^ 32) (hacc : acc.toNat + 4 ≤ 2 ^ 32) (hsp : 96 ≤ sp.toNat)
    (hi : i ≤ bs.length) (hc : bs[i + wsLen (bs.drop i)]? = some 0x3A)
    (hnb : (0x5C : UInt8) ∉ bs) (hign : ign1 (bs.drop (i + wsLen (bs.drop i) + 1)) = some rest) :
    SerdeEnds.endCode n maxP inst mi A ∗ A 89 ↪[wf] FuncInst.wasm types[32]! inst f89 ∗
      A 81 ↪[wf] FuncInst.wasm types[32]! inst f81 ∗ SerdeIgnValue.code81 inst mi A ⊢
      MFunSpec (GF := GF) cfg lim d types[32]! inst mi f201 Cg
        (fun args => iprop(⌜args = [.i32 acc]⌝ ∗ n ↦[i32][ acc.toNat ] de ∗
          g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 96) 96 ∗
          rd n de ptr bs i ∗ scratchTables n de ptrS capS))
        (fun _ => (240 + 96 * wsLen (bs.drop i)) * cfg.regularOpCost +
          (166 + 470 * (bs.length - rest.length - (i + wsLen (bs.drop i) + 1))) * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ n ↦[i32][ acc.toNat ] de ∗
          g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 96) 96 ∗
          rd n de ptr bs (bs.length - rest.length) ∗ scratchTables n de ptrS capS)) := by
  have hcl := SerdeNextKey.getElem_lt hc
  iintro ⟨#Hend, #F89, #F81, #HC⟩
  ihave #Hend' := Hend
  iunfold SerdeEnds.endCode at Hend'
  icases Hend' with ⟨#Herror, -, -, #F332, #F333, #F339⟩
  iunfold SerdeErrBox.errCode at Herror
  icases Herror with ⟨#H310, -⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold code310 at H310
    icases H310 with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩
    iexact Hi
  have hn := hm.mem
  have ha89 := hm.funcs 89 (by decide)
  have ha81 := hm.funcs 81 (by decide)
  have t32 : types[32]!.params.length = 1 := rfl
  have key89 := SerdeColonSuccess.f89_colon (GF := GF) cfg lim (d + 1) types[32]! rfl inst mi A n g ta hm
    (by omega) Cg gt sp de ptr bs i hlen (by omega) (by omega) hi hc
  have key81 := SerdeIgnValue.f81_shallow_reuse (GF := GF) cfg lim (d + 1) types[32]! rfl inst mi A n g ta hm
    (by omega) Cg gt sp de ptr ptrS capS bs (i + wsLen (bs.drop i) + 1) rest hlen (by omega) hde hsp
    (by omega) hnb hign
  iapply MFunSpec_intro
  imodintro
  iintro %args %R Hpre Hc
  icases Hpre with ⟨%ha, Hacc, Hg, Hs, Hrd, Htables⟩
  subst ha
  simp only [f201]
  rw [show (240 + 96 * wsLen (bs.drop i)) * cfg.regularOpCost =
    40 * cfg.regularOpCost + (200 + 96 * wsLen (bs.drop i)) * cfg.regularOpCost by
      simp only [Nat.add_mul]; omega]
  generalize hK : (166 + 470 * (bs.length - rest.length - (i + wsLen (bs.drop i) + 1))) * cfg.regularOpCost = K
    at key81 ⊢
  generalize hE : (200 + 96 * wsLen (bs.drop i)) * cfg.regularOpCost = E at key89 ⊢
  rw [show 40 * cfg.regularOpCost + E + K + R = 40 * cfg.regularOpCost + (E + (K + R)) by omega]
  mstep; mstep; mstep [Hacc]
  mcall key89 using [Hg Hrd]
  · iframe Hg Hrd
  icases HQ with ⟨%hrs, Hg, Hrd⟩
  subst hrs
  mstep
  mstep_not_taken with decide
  mstep; mstep [Hacc]
  mcall key81 using [Hg Hs Hrd Htables]
  · iframe Hg Hs Hrd Htables
  icases HQ with ⟨%hrs, Hg, Hs, Hrd, Htables⟩
  subst hrs
  mstep
  (try simp only [Post.mloop]); (try mctrl_norm); (repeat mpay)
  repeat mstep
  isplitl [Hc]
  · iapply BorrowMut.credits_le
    iframe Hc
    ipureintro; omega
  iframe Hacc Hg Hs Hrd Htables
  ipureintro; rfl

/-- The established shallow ignored-reader charge, fixed independently of the gas ceiling. -/
def cost81 (cfg : WasmConfig) (bs : List UInt8) (j : Nat) : Nat :=
  match ign1 (bs.drop j) with
  | some rest => (166 + 470 * (bs.length - rest.length - j)) * cfg.regularOpCost
  | none => 0

set_option maxRecDepth 100000 in
/-- Shallow ignored values preserve the object member's heap, scratch capacity and saved String. -/
theorem ignoreHyp (cfg : WasmConfig) (lim : ExecLimits) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat)
    (n g ta Cg maxP : Nat) (hm : IfaceMod mi A n g ta) (gt : GlobalType) (idx de ptr : UInt32)
    (bs : List UInt8) (live : List (Nat × Nat)) (B Bsaved : Bounds)
    (hlen : bs.length < 2 ^ 24) (hptr : ptr.toNat + bs.length < 2 ^ 32) (hde : de.toNat + 24 ≤ 2 ^ 32)
    (hnb : (0x5C : UInt8) ∉ bs)
    (hmono : ∀ i j hl F cap, i ≤ j → B i hl F cap → B j hl F cap)
    (hmonoSaved : ∀ i j hl F cap, i ≤ j → Bsaved i hl F cap → Bsaved j hl F cap)
    (Cd : IProp GF) [Persistent Cd]
    (hcode : Cd ⊢ SerdeEnds.endCode n maxP inst mi A ∗ A 89 ↪[wf] FuncInst.wasm types[32]! inst f89 ∗
      A 81 ↪[wf] FuncInst.wasm types[32]! inst f81 ∗ SerdeIgnValue.code81 inst mi A) :
    SerdeStructObjState.IgnoreHyp (GF := GF) cfg lim inst mi n g Cg gt de ptr bs ign1R (cost81 cfg bs)
      (member n maxP ta (A 578) idx de live B Bsaved) Cd := by
  intro d s i rest seen hd hsp hsend hi hcolon hmodel
  have hsuf := WNear.IgnoreShallow.ign1R_suf hmodel
  have hlenRest := hsuf.length_le
  simp only [List.length_drop] at hlenRest
  have hcursor : i ≤ bs.length - rest.length := by omega
  have hign := hmodel
  unfold ign1R at hign
  simp only [Option.map_eq_some_iff] at hign
  obtain ⟨r', hx, he⟩ := hign
  cases he
  have hK : cost81 cfg bs (i + wsLen (bs.drop i) + 1) =
      (166 + 470 * (bs.length - rest.length - (i + wsLen (bs.drop i) + 1))) * cfg.regularOpCost := by
    simp only [cost81, hx]
  rw [hK]
  have hs32 : (s + 32).toNat = s.toNat + 32 := by simp [UInt32.toNat_add]; omega
  iintro #HCd
  ihave Hcode := hcode $$ HCd
  icases Hcode with ⟨#Hend, #F89, #F81, #C81⟩
  iunfold MFunSpec
  imodintro
  iintro %args %R Hpre Hc
  icases Hpre with ⟨%ha, M32, Hg, H304, Hrd, Hseen⟩
  icases SerdeStructObjKeyState.seen_core n maxP ta (A 578) idx de s live B Bsaved i seen $$ Hseen with
    ⟨%C, %lv, %hC, Hcore, Hsaved⟩
  iunfold core at Hcore
  icases Hcore with ⟨%hl, %F, %ptrS, %capS, %sl, %⟨hb, hcap⟩, Hvt, Htables, Hkey, Hident, Hscratch⟩
  have hb' : C (bs.length - rest.length) hl F capS := by
    rcases hC with rfl | rfl
    · exact hmono i _ hl F capS hcursor hb
    · exact hmonoSaved i _ hl F capS hcursor hb
  iunfold SerdeValueState.scratchPre at Hscratch
  icases Hscratch with ⟨S8, S0, S4, Hsb⟩
  iunfold SerdeValueState.tables at Htables
  icases Htables with ⟨He, Hw, Hhex⟩
  have callIgnore := f201_shallow (GF := GF) cfg lim d inst mi A n g ta hm (by omega) Cg gt
    s (s + 32) de ptr ptrS capS bs i maxP rest (by omega) hptr hde (by rw [hs32]; omega)
    (by omega) hi hcolon hnb hx
  rw [hs32] at callIgnore
  ihave #S := callIgnore $$ [Hend F89 F81 C81]
  · iframe Hend F89 F81 C81
  clear callIgnore
  iunfold MFunSpec at S
  icases VecFromElem.stk_split n (s.toNat - 304) 208 96 $$ H304 with ⟨H208, H96⟩
  rw [show s.toNat - 304 + 208 = s.toNat - 96 by omega]
  iapply mwpInvoke_wand
  isplitl [M32 Hg H96 Hrd S8 S0 S4 He Hw Hident Hc]
  · iapply S $$ %args %R [M32 Hg H96 Hrd S8 S0 S4 He Hw Hident] Hc
    dsimp only
    iframe M32 Hg H96 Hrd
    isplitr
    · ipureintro; exact ha
    iunfold scratchTables
    iframe He Hw S0 S4 Hident
    iexists sl
    iexact S8
  isplit
  · dsimp only
    iintro %rs ⟨Hc, %hrs, M32, Hg, H96, Hrd, Htables⟩
    iunfold scratchTables at Htables
    icases Htables with ⟨⟨%sl', S8⟩, He, Hw, S0, S4, Hident⟩
    iframe Hc M32 Hg Hrd
    isplitr
    · ipureintro; exact hrs
    isplitl [H208 H96]
    · iapply VecFromElem.stk_join n (s.toNat - 304) 208 96
      rw [show s.toNat - 304 + 208 = s.toNat - 96 by omega]
      iframe H208 H96
    iapply Hsaved $$ %(bs.length - rest.length)
    iunfold core
    iexists hl, F, ptrS, capS, sl'
    iframe Hvt Hkey Hident
    isplitr
    · ipureintro; exact ⟨hb', hcap⟩
    isplitl [He Hw Hhex]
    · iunfold SerdeValueState.tables
      iframe He Hw Hhex
    iunfold SerdeValueState.scratchPre
    iframe S8 S0 S4 Hsb
  · iintro Htrap; iexact Htrap

end Proof
end WNear.Binary.SerdeIgnReuse
