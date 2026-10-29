import Bridge.Functions.SerdeValueReuse

/-! # The array's first element on either successful account-id string path -/

namespace WNear.Binary.SerdeSeqElemReuse

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.VecFromElem (stk roomFor)
open WNear.Binary.SerdeRead (rd wsLen)
open WNear.Binary.ParseStr (borrowed roomRun code646)
open WNear.Binary.SerdeAccountId (code169)
open WNear.Binary.SerdeDeStrEsc (costCopied)
open WNear.Binary.ParseStrSuccess (appendChunks)
open WNear.Binary.ScratchGrow (growthPages)
open WNear.Binary.SerdeValueState (scratchPre valuePost)

/-- A quoted value begins after the whitespace that 214 already consumed. -/
theorem wsLen_quote {bs : List UInt8} {j : Nat} (h : bs[j]? = some 0x22) : wsLen (bs.drop j) = 0 := by
  have hl := SerdeNextKey.getElem_lt h
  rw [List.drop_eq_getElem_cons hl]
  rw [List.getElem?_eq_getElem hl] at h
  simp only [Option.some.injEq] at h
  rw [h]; simp [wsLen]; decide

section Proof
variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- 214 reads any valid account-id string in an array, retaining reusable scratch and the owned String. -/
theorem f214_model (cfg : WasmConfig) (lim : ExecLimits) (d : Nat)
    (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 34 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp out acc de ptr idx sl ptrS capS : UInt32) (ob ob2 bs : List UInt8)
    (value : String) (rest : List UInt8) (i j : Nat) (maxP hl : Nat) (live : List (Nat × Nat)) (F : Nat)
    (hob : ob.length = 16) (hob2 : ob2.length = 16) (hout : out.toNat + 16 ≤ 2 ^ 32)
    (hlen : bs.length < 2 ^ 24) (hptr : ptr.toNat + bs.length < 2 ^ 32)
    (hde : de.toNat + 24 ≤ 2 ^ 32) (hacc : acc.toNat + 8 ≤ 2 ^ 32) (hsp : 304 ≤ sp.toNat)
    (hi : i ≤ bs.length) (hj : j = i + wsLen (bs.drop i)) (hq : bs[j]? = some 0x22)
    (hcap : capS.toNat < 2 ^ 25)
    (hmodel : NearInterface.Json.stringBody (bs.drop (j + 1)) [] = some (some value, rest))
    (hr : SerdeErrBox.roomFor4 hl maxP 20) (hroom : roomRun maxP hl capS [] (bs.drop (j + 1)))
    (hvalid : validAccountIdBytes value.toUTF8.toList = true)
    (halloc : roomFor (hl + growthPages capS 0 (appendChunks (bs.drop (j + 1)) []) * 65536)
      maxP (UInt32.ofNat value.toUTF8.toList.length)) :
    SerdeEnds.endCode n maxP inst mi A ∗ A 169 ↪[wf] FuncInst.wasm types[14]! inst f169 ∗
      code169 n maxP inst mi A ∗ code646 n maxP inst mi A ⊢
      MFunSpec (GF := GF) cfg lim d types[14]! inst mi f214 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 acc]⌝ ∗ n ↦[i32][ acc.toNat ] de ∗
          n ↦[wms][ acc.toNat + 4 ] [1] ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ n ↦[wms][ (sp - 16).toNat ] ob ∗
          n ↦[wms][ out.toNat ] ob2 ∗ rd n de ptr bs i ∗
          iprop(stk n (sp.toNat - 304) 288 ∗ vt n 1057464 idx ta (A 578) ∗
            scratchPre n maxP hl live F de ptrS capS sl ∗ SerdeValueState.tables n)))
        (fun _ => (300 + 96 * wsLen (bs.drop i)) * cfg.regularOpCost +
          SerdeValueReuse.valueCost cfg F capS bs value.toUTF8.toList rest j j)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ n ↦[i32][ acc.toNat ] de ∗ n ↦[wms][ acc.toNat + 4 ] [0] ∗
          g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 16) 16 ∗
          ∃ (p c len : UInt32), ⌜p ≠ 0⌝ ∗ n ↦[i32][ out.toNat ] 0 ∗ n ↦[i32][ out.toNat + 4 ] p ∗
            n ↦[i32][ out.toNat + 8 ] c ∗ n ↦[i32][ out.toNat + 12 ] len ∗
            iprop(stk n (sp.toNat - 304) 288 ∗ vt n 1057464 idx ta (A 578) ∗ SerdeValueState.tables n ∗
              rd n de ptr bs (bs.length - rest.length) ∗
              SerdeValueReuse.ownedValue n maxP hl live F de capS bs value.toUTF8.toList (j + 1) p c len))) := by
  have hjl := SerdeNextKey.getElem_lt hq
  have hw := wsLen_quote hq
  have hs := SerdeValueReuse.spec169_model (GF := GF) cfg lim (d + 1) inst mi A n g ta hm (by omega) Cg gt
    sp de ptr idx ptrS capS sl ob bs value rest j j maxP hl F live hob hlen hptr hde hsp (by omega)
    (by rw [hw]; omega) hq hcap hmodel hvalid hr hroom halloc
  have h214 := SerdeSeqElem.f214_first (GF := GF) cfg lim d types[14]! rfl inst mi A n g ta hm (by omega) Cg gt
    sp out acc de ptr ob ob2 bs i 0x22 maxP hob hob2 hout (by omega) hptr hde hacc (by omega) hi
    (by rw [← hj]; exact hq) (by decide)
    iprop(stk n (sp.toNat - 304) 288 ∗ vt n 1057464 idx ta (A 578) ∗
      scratchPre n maxP hl live F de ptrS capS sl ∗ SerdeValueState.tables n)
    (SerdeValueReuse.valueCost cfg F capS bs value.toUTF8.toList rest j j)
    (fun p c len => iprop(stk n (sp.toNat - 304) 288 ∗ vt n 1057464 idx ta (A 578) ∗ SerdeValueState.tables n ∗
      rd n de ptr bs (bs.length - rest.length) ∗
              SerdeValueReuse.ownedValue n maxP hl live F de capS bs value.toUTF8.toList (j + 1) p c len))
  rw [← hj] at h214
  iintro ⟨#Hend, #H169, #HC, #HP⟩
  ihave #S169 := hs $$ [HC HP]
  · iframe HC HP
  iapply h214 $$ [Hend H169 S169]
  iframe Hend H169 S169

end Proof
end WNear.Binary.SerdeSeqElemReuse
