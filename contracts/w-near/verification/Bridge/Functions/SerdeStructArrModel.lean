import Bridge.Functions.SerdeStructArrState
import Bridge.Functions.SerdeValueReuse

/-! Successful account-id array parsing for both borrowed and copied strings. -/
namespace WNear.Binary.SerdeStructArrModel
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.VecFromElem (stk roomFor)
open WNear.Binary.SerdeRead (rd wsLen)
open WNear.Binary.ParseStr (roomRun code646)
open WNear.Binary.SerdeAccountId (code169)
open WNear.Binary.SerdeValueReuse (ownedValue valueCost)
open WNear.Binary.SerdeValueState (scratchPre)
open WNear.Binary.ParseStrSuccess (appendChunks)
open WNear.Binary.ScratchGrow (growthPages)
section Proof
variable {GF : BundledGFunctors} [WasmGS NearState GF]
theorem f228_arr_model (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 35 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp out de ptr idx x2 x3 x4 x5 sl ptrS capS : UInt32) (ob bs : List UInt8)
    (value : String) (rest : List UInt8) (i j : Nat) (maxP hl : Nat) (live : List (Nat × Nat)) (F : Nat)
    (hob : ob.length = 16) (hout : out.toNat + 16 ≤ 2 ^ 32)
    (hlen : bs.length < 2 ^ 24) (hptr : ptr.toNat + bs.length < 2 ^ 32)
    (hde : de.toNat + 25 ≤ 2 ^ 32) (hsp : 368 ≤ sp.toNat) (hi : i ≤ bs.length)
    (ho : bs[i + wsLen (bs.drop i)]? = some 0x5B)
    (hj : j = i + wsLen (bs.drop i) + 1 + wsLen (bs.drop (i + wsLen (bs.drop i) + 1)))
    (hq : bs[j]? = some 0x22)
    (he : bs[bs.length - rest.length + wsLen (bs.drop (bs.length - rest.length))]? = some 0x5D)
    (hcap : capS.toNat < 2 ^ 25)
    (hmodel : NearInterface.Json.stringBody (bs.drop (j + 1)) [] = some (some value, rest))
    (hr : SerdeErrBox.roomFor4 hl maxP 20) (hroom : roomRun maxP hl capS [] (bs.drop (j + 1)))
    (hvalid : validAccountIdBytes value.toUTF8.toList = true)
    (halloc : roomFor (hl + growthPages capS 0 (appendChunks (bs.drop (j + 1)) []) * 65536)
      maxP (UInt32.ofNat value.toUTF8.toList.length)) :
    SerdeEnds.endCode n maxP inst mi A ∗ A 214 ↪[wf] FuncInst.wasm types[14]! inst f214 ∗
      A 169 ↪[wf] FuncInst.wasm types[14]! inst f169 ∗ A 91 ↪[wf] FuncInst.wasm types[32]! inst f91 ∗
      code169 n maxP inst mi A ∗ code646 n maxP inst mi A ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f228 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 de, .i32 x2, .i32 x3, .i32 x4, .i32 x5]⌝ ∗
          g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 368) 368 ∗ vt n 1057464 idx ta (A 578) ∗
          n ↦[wms][ out.toNat ] ob ∗ rd n de ptr bs i ∗ n ↦[wms][ de.toNat + 24 ] [128] ∗
          iprop(scratchPre n maxP hl live F de ptrS capS sl ∗ SerdeValueState.tables n)))
        (fun _ => (1300 + 96 * (wsLen (bs.drop i) + wsLen (bs.drop (i + wsLen (bs.drop i) + 1)) +
            wsLen (bs.drop (bs.length - rest.length)))) * cfg.regularOpCost +
          valueCost cfg F capS bs value.toUTF8.toList rest j j)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 368) 368 ∗
          vt n 1057464 idx ta (A 578) ∗ n ↦[wms][ de.toNat + 24 ] [128] ∗
          ∃ (p c len : UInt32), ⌜p ≠ 0⌝ ∗ n ↦[i32][ out.toNat ] 0 ∗ n ↦[i32][ out.toNat + 4 ] p ∗
            n ↦[i32][ out.toNat + 8 ] c ∗ n ↦[i32][ out.toNat + 12 ] len ∗
            iprop(SerdeValueState.tables n ∗
              ownedValue n maxP hl live F de capS bs value.toUTF8.toList (j + 1) p c len) ∗
            rd n de ptr bs (bs.length - rest.length + wsLen (bs.drop (bs.length - rest.length)) + 1))) := by
  have hjl := SerdeNextKey.getElem_lt hq
  have hlt := sp.toNat_lt
  have h64 : (sp - 64).toNat = sp.toNat - 64 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have hw : wsLen (bs.drop j) = 0 := by
    rw [List.drop_eq_getElem_cons hjl]
    rw [List.getElem?_eq_getElem hjl] at hq
    simp only [Option.some.injEq] at hq
    rw [hq]; simp [wsLen]; decide
  apply SerdeStructArrState.f228_arr_state cfg lim d type htype inst mi A n g ta hm (by omega) Cg gt
    sp out de ptr idx x2 x3 x4 x5 ob bs i maxP hob hout (by omega) hptr hde hsp hi
    iprop(scratchPre n maxP hl live F de ptrS capS sl ∗ SerdeValueState.tables n)
    (valueCost cfg F capS bs value.toUTF8.toList rest j j)
    (fun p c len => iprop(SerdeValueState.tables n ∗
      ownedValue n maxP hl live F de capS bs value.toUTF8.toList (j + 1) p c len))
    iprop(code169 n maxP inst mi A ∗ code646 n maxP inst mi A) rest
  · refine ⟨ho, ⟨0x22, ?_, by decide⟩, he⟩
    rw [← hj]; exact hq
  · intro ob1 hob1
    rw [← hj]
    have hs := SerdeValueReuse.spec169_model (GF := GF) cfg lim (d + 2) inst mi A n g ta hm (by omega) Cg gt
      (sp - 64) de ptr idx ptrS capS sl ob1 bs value rest j j maxP hl F live hob1 hlen (by omega) (by omega)
      (by omega) (by omega) (by rw [hw]; omega) hq hcap hmodel hvalid hr hroom halloc
    apply hs.trans
    apply SerdeValueState.spec169_post
    intro p c len
    iintro ⟨Hs, Hvt, Htables, Hrd, Hvalue⟩
    iframe Hs Hvt Hrd Htables Hvalue

end Proof
end WNear.Binary.SerdeStructArrModel
