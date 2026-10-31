import Bridge.Functions.SerdeStructArrModel
import Bridge.Functions.SerdeStruct78Esc

/-! Successful account-id array parsing for both borrowed and copied strings. -/
namespace WNear.Binary.SerdeStruct78Model

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.VecFromElem (stk roomFor)
open WNear.Binary.SerdeRead (rd wsLen)
open WNear.Binary.ParseStr (borrowed roomRun code646)
open WNear.Binary.SerdeAccountId (code169)
open WNear.Binary.SerdeValueReuse (ownedValue valueCost)
open WNear.Binary.ParseStrSuccess (appendChunks)
open WNear.Binary.ScratchGrow (growthPages)
open WNear.Binary.SerdeValueState (scratchPre valueStorage)

section Proof
variable {GF : BundledGFunctors} [WasmGS NearState GF]

def costArray (cfg : WasmConfig) (F : Nat) (capS : UInt32) (bs bytes rest : List UInt8) (j : Nat) : Nat :=
  (1300 + 96 * (wsLen bs + wsLen (bs.drop (wsLen bs + 1)) +
    wsLen (bs.drop (bs.length - rest.length)))) * cfg.regularOpCost +
    valueCost cfg F capS bs bytes rest j j

set_option maxRecDepth 100000 in
/-- The 78 wrapper preserves the concrete changing-state array result. -/
theorem f78_arr_model (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 36 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp out de ptr idx sl ptrS capS : UInt32) (ob bs : List UInt8)
    (value : String) (rest : List UInt8) (j : Nat) (maxP hl : Nat) (live : List (Nat × Nat)) (F : Nat)
    (hob : ob.length = 16) (hout : out.toNat + 16 ≤ 2 ^ 32)
    (hlen : bs.length < 2 ^ 24) (hptr : ptr.toNat + bs.length < 2 ^ 32)
    (hde : de.toNat + 25 ≤ 2 ^ 32) (hsp : 368 ≤ sp.toNat)
    (ho : bs[wsLen bs]? = some 0x5B)
    (hj : j = wsLen bs + 1 + wsLen (bs.drop (wsLen bs + 1)))
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
      code169 n maxP inst mi A ∗ code646 n maxP inst mi A ∗
      A 228 ↪[wf] FuncInst.wasm types[36]! inst f228 ∗ inst ↪[inst] mi ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f78 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 de]⌝ ∗
          g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 368) 368 ∗ vt n 1057464 idx ta (A 578) ∗
          n ↦[wms][ out.toNat ] ob ∗ rd n de ptr bs 0 ∗ n ↦[wms][ de.toNat + 24 ] [128] ∗
          iprop(scratchPre n maxP hl live F de ptrS capS sl ∗ SerdeValueState.tables n)))
        (fun _ => 40 * cfg.regularOpCost + costArray cfg F capS bs value.toUTF8.toList rest j)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 368) 368 ∗
          vt n 1057464 idx ta (A 578) ∗ n ↦[wms][ de.toNat + 24 ] [128] ∗
          ∃ (p c len : UInt32), ⌜p ≠ 0⌝ ∗ n ↦[i32][ out.toNat ] 0 ∗ n ↦[i32][ out.toNat + 4 ] p ∗
            n ↦[i32][ out.toNat + 8 ] c ∗ n ↦[i32][ out.toNat + 12 ] len ∗
            iprop(SerdeValueState.tables n ∗
              ownedValue n maxP hl live F de capS bs value.toUTF8.toList (j + 1) p c len) ∗
            rd n de ptr bs (bs.length - rest.length + wsLen (bs.drop (bs.length - rest.length)) + 1))) := by
  have hs := SerdeStructArrModel.f228_arr_model (GF := GF) cfg lim (d + 1) types[36]! rfl inst mi A n g ta hm
    (by omega) Cg gt sp out de ptr idx out out out out sl ptrS capS ob bs value rest 0 j maxP hl live F
    hob hout hlen hptr hde hsp (by omega) (by simpa only [List.drop_zero, Nat.zero_add] using ho)
    (by simpa only [List.drop_zero, Nat.zero_add] using hj) hq he hcap hmodel hr hroom hvalid halloc
  simp only [List.drop_zero, Nat.zero_add] at hs
  iintro ⟨#Hend, #F214, #F169, #F91, #HC, #HP, #F228, #Hi⟩
  have ha228 := hm.funcs 228 (by decide)
  have t36 : types[36]!.params.length = 6 := rfl
  iapply MFunSpec_intro
  imodintro
  iintro %args %R Hpre Hc
  icases Hpre with ⟨%ha, Hg, Hs, Hvt, Ho, Hrd, Hd, Hstate⟩
  subst ha
  simp only [f78, costArray]
  generalize hK : (1300 + 96 * (wsLen bs + wsLen (bs.drop (wsLen bs + 1)) +
      wsLen (bs.drop (bs.length - rest.length)))) * cfg.regularOpCost +
    valueCost cfg F capS bs value.toUTF8.toList rest j j = K at hs ⊢
  ihave #S := hs $$ [Hend F214 F169 F91 HC HP]
  · iframe Hend F214 F169 F91 HC HP
  rw [show 40 * cfg.regularOpCost + K + R = 40 * cfg.regularOpCost + (K + R) by omega]
  mstep; mstep; mstep; mstep; mstep; mstep
  mcall S using [Hg Hs Hvt Ho Hrd Hd Hstate]
  · iframe Hg Hs Hvt Ho Hrd Hd Hstate
  icases HQ with ⟨%hrs, HQ⟩
  subst hrs
  repeat mstep
  isplitl [Hc]
  · iapply BorrowMut.credits_le
    iframe Hc
    ipureintro; omega
  icases HQ with ⟨Hg, Hs, Hvt, Hd, Hresult⟩
  iframe Hg Hs Hvt Hd Hresult
  ipureintro; simp [htype]

theorem costArray_le (cfg : WasmConfig) (F : Nat) (capS : UInt32) (bs : List UInt8)
    (value : String) (rest : List UInt8) (j : Nat) (hq : bs[j]? = some 0x22)
    (hmodel : NearInterface.Json.stringBody (bs.drop (j + 1)) [] = some (some value, rest)) :
    costArray cfg F capS bs value.toUTF8.toList rest j ≤
      SerdeStruct78Esc.costArray cfg F capS bs value.toUTF8.toList rest j := by
  obtain ⟨hok, hu⟩ := SerdeAccountIdEsc.strRun_of_stringBody _ _ _ hmodel
  exact Nat.add_le_add_left (SerdeValueReuse.valueCost_le cfg F capS bs value.toUTF8.toList rest j j
    (SerdeNextKey.getElem_lt hq) hok hu) _

end Proof
end WNear.Binary.SerdeStruct78Model
