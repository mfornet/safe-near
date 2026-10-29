import Bridge.Functions.SerdeValueReuse
import Bridge.Functions.SerdeColonSuccess

/-! # The map's account-id reader with reusable scratch on every successful string path -/

namespace WNear.Binary.SerdeMapValueReuse

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.AllocTwo (code310)
open WNear.Binary.VecFromElem (stk roomFor)
open WNear.Binary.SerdeRead (rd wsLen)
open WNear.Binary.ParseStr (borrowed roomRun code646)
open WNear.Binary.SerdeAccountId (code169)
open WNear.Binary.SerdeDeStrEsc (copiedResult costCopied)
open WNear.Binary.ParseStrSuccess (appendChunks)
open WNear.Binary.ScratchGrow (growthPages)
open WNear.Binary.SerdeValueState (scratchPre)

section Proof
variable {GF : BundledGFunctors} [WasmGS NearState GF]

set_option maxRecDepth 100000 in
/-- 205 consumes the colon and reads any model-decoded valid account id with reusable scratch. -/
theorem f205_model (cfg : WasmConfig) (lim : ExecLimits) (d : Nat)
    (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 34 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp out acc de ptr idx sl ptrS capS : UInt32) (ob bs : List UInt8)
    (value : String) (rest : List UInt8) (i j : Nat) (maxP hl : Nat) (live : List (Nat × Nat)) (F : Nat)
    (hob : ob.length = 16) (hout : out.toNat + 16 ≤ 2 ^ 32)
    (hlen : bs.length < 2 ^ 24) (hptr : ptr.toNat + bs.length < 2 ^ 32)
    (hde : de.toNat + 24 ≤ 2 ^ 32) (hacc : acc.toNat + 4 ≤ 2 ^ 32) (hsp : 288 ≤ sp.toNat)
    (hi : i ≤ bs.length) (hc : bs[i + wsLen (bs.drop i)]? = some 0x3A)
    (hj : j = i + wsLen (bs.drop i) + 1 + wsLen (bs.drop (i + wsLen (bs.drop i) + 1)))
    (hq : bs[j]? = some 0x22) (hcap : capS.toNat < 2 ^ 25)
    (hmodel : NearInterface.Json.stringBody (bs.drop (j + 1)) [] = some (some value, rest))
    (hr : SerdeErrBox.roomFor4 hl maxP 20) (hroom : roomRun maxP hl capS [] (bs.drop (j + 1)))
    (hvalid : validAccountIdBytes value.toUTF8.toList = true)
    (halloc : roomFor (hl + growthPages capS 0 (appendChunks (bs.drop (j + 1)) []) * 65536)
      maxP (UInt32.ofNat value.toUTF8.toList.length)) :
    SerdeEnds.endCode n maxP inst mi A ∗ A 89 ↪[wf] FuncInst.wasm types[32]! inst f89 ∗
      A 169 ↪[wf] FuncInst.wasm types[14]! inst f169 ∗ code169 n maxP inst mi A ∗ code646 n maxP inst mi A ⊢
      MFunSpec (GF := GF) cfg lim d types[14]! inst mi f205 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 acc]⌝ ∗ n ↦[i32][ acc.toNat ] de ∗
          g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 288) 288 ∗ vt n 1057464 idx ta (A 578) ∗
          n ↦[wms][ out.toNat ] ob ∗ rd n de ptr bs i ∗
          scratchPre n maxP hl live F de ptrS capS sl ∗ SerdeValueState.tables n))
        (fun _ => (240 + 96 * wsLen (bs.drop i)) * cfg.regularOpCost +
          SerdeValueReuse.valueCost cfg F capS bs value.toUTF8.toList rest (i + wsLen (bs.drop i) + 1) j)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ n ↦[i32][ acc.toNat ] de ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          stk n (sp.toNat - 288) 288 ∗ vt n 1057464 idx ta (A 578) ∗ SerdeValueState.tables n ∗
          rd n de ptr bs (bs.length - rest.length) ∗ ∃ (p c len : UInt32),
          n ↦[i32][ out.toNat ] 0 ∗ n ↦[i32][ out.toNat + 4 ] p ∗ n ↦[i32][ out.toNat + 8 ] c ∗
          n ↦[i32][ out.toNat + 12 ] len ∗
          SerdeValueReuse.ownedValue n maxP hl live F de capS bs value.toUTF8.toList (j + 1) p c len)) := by
  have hcl := SerdeNextKey.getElem_lt hc
  have hjl := SerdeNextKey.getElem_lt hq
  iintro ⟨#Hend, #F89, #F169, #HC, #HP⟩
  ihave #Hend' := Hend
  iunfold SerdeEnds.endCode at Hend'
  icases Hend' with ⟨#Herror, -, -, #F332, #F333, #F339⟩
  iunfold SerdeErrBox.errCode at Herror
  icases Herror with ⟨#H310, -⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold code310 at H310
    icases H310 with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩
    iexact Hi
  have ha89 := hm.funcs 89 (by decide)
  have ha169 := hm.funcs 169 (by decide)
  have hn := hm.mem
  have t32 : types[32]!.params.length = 1 := rfl
  have t14 : types[14]!.params.length = 2 := rfl
  have key89 := SerdeColonSuccess.f89_colon (GF := GF) cfg lim (d + 1) types[32]! rfl inst mi A n g ta hm
    (by omega) Cg gt sp de ptr bs i (by omega) (by omega) (by omega) hi hc
  have key169 := SerdeValueReuse.f169_model (GF := GF) cfg lim (d + 1) inst mi A n g ta hm
    (by omega) Cg gt sp out de ptr idx ptrS capS sl ob bs value rest (i + wsLen (bs.drop i) + 1) j
    maxP hl F live hob hout hlen hptr hde hsp (by omega) hj hq hcap hmodel hvalid hr hroom halloc
  iapply MFunSpec_intro
  imodintro
  iintro %args %R Hpre Hc
  icases Hpre with ⟨%ha, Hacc, Hg, Hs, Hvt, Ho, Hrd, Hscratch, Htables⟩
  subst ha
  simp only [f205]
  rw [show (240 + 96 * wsLen (bs.drop i)) * cfg.regularOpCost =
    40 * cfg.regularOpCost + (200 + 96 * wsLen (bs.drop i)) * cfg.regularOpCost by
      simp only [Nat.add_mul]; omega]
  generalize hK : SerdeValueReuse.valueCost cfg F capS bs value.toUTF8.toList rest
    (i + wsLen (bs.drop i) + 1) j = K at key169 ⊢
  generalize hE : (200 + 96 * wsLen (bs.drop i)) * cfg.regularOpCost = E at key89 ⊢
  rw [show 40 * cfg.regularOpCost + E + K + R = 40 * cfg.regularOpCost + (E + (K + R)) by omega]
  mstep; mstep; mstep [Hacc]
  mcall key89 using [Hg Hrd]
  · iframe Hg Hrd
  icases HQ with ⟨%hrs, Hg, Hrd⟩
  subst hrs
  mstep; mstep
  mstep_taken with decide
  mstep; mstep; mstep [Hacc]
  mcall key169 using [Hg Hs Hvt Ho Hrd Hscratch Htables]
  · iframe Hg Hs Hvt Ho Hrd Hscratch Htables
  icases HQ with ⟨%hrs, Hg, Hs, Hvt, Htables, Hresult⟩
  subst hrs
  repeat mstep
  repeat mpay
  isplitl [Hc]
  · iapply BorrowMut.credits_le
    iframe Hc
    ipureintro; omega
  isplitr
  · ipureintro; trivial
  iframe Hacc Hg Hs Hvt Htables Hresult

end Proof
end WNear.Binary.SerdeMapValueReuse
