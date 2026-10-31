import Bridge.Functions.SerdeObjectKeyPrecise
import Bridge.Functions.SerdeObjectCostComposition

set_option maxRecDepth 100000

namespace WNear.Binary.SerdeStructObjModelState
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.VecFromElem (stk)
open WNear.Binary.SerdeRead (rd wsLen)
open WNear.Binary.SerdeStructObjKeyState (Bounds member PreciseKeyConditions)
open WNear.Binary.SerdeStructObjValueState (ValueConditions)
open WNear.SerdeStructModel
section Proof
variable {GF : BundledGFunctors} [WasmGS NearState GF]
set_option maxRecDepth 100000 in
theorem f228_obj_model_closing_precise (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 42 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp out de ptr idx x2 x3 x4 x5 : UInt32) (ob bs : List UInt8) (i maxP : Nat)
    (live : List (Nat × Nat)) (Cd : IProp GF) [Persistent Cd] (B Bsaved : Bounds) (K646 K169 K81 : Nat → Nat)
    (ign : List UInt8 → Option (Unit × List UInt8)) (hign : Agrees ign valueSkip)
    (hob : ob.length = 16) (hout : out.toNat + 16 ≤ 2 ^ 32) (hlen : bs.length < 2 ^ 24)
    (hptr : ptr.toNat + bs.length < 2 ^ 32) (hde : de.toNat + 25 ≤ 2 ^ 32)
    (hsp : 368 ≤ sp.toNat) (hal : sp.toNat % 8 = 0) (hi : i ≤ bs.length)
    (hkeys : PreciseKeyConditions cfg maxP bs B K646) (hkeysSaved : PreciseKeyConditions cfg maxP bs Bsaved K646)
    (hvalues : ValueConditions cfg maxP bs B Bsaved K169)
    (hclose : ClosingConditions bs B)
    (hcloseSaved : ClosingConditions bs Bsaved)
    (hignore : SerdeStructObjState.IgnoreHyp (GF := GF) cfg lim inst mi n g Cg gt de ptr bs ign K81
      (member n maxP ta (A 578) idx de live B Bsaved) iprop(code n maxP inst mi A ∗ Cd))
    (N : Nat) (a : WNear.AccountId) (rF : List UInt8)
    (hb0 : bs[i + wsLen (bs.drop i)]? = some 0x7B)
    (hloop : objLoop "account_id" (valueAs WNear.account) ign N none
      (bs.drop (i + wsLen (bs.drop i) + 1)) = some (some a, rF)) :
    code n maxP inst mi A ∗ Cd ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f228 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 de, .i32 x2, .i32 x3, .i32 x4, .i32 x5]⌝ ∗
          g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 368) 368 ∗ n ↦[wms][ out.toNat ] ob ∗
          rd n de ptr bs i ∗ n ↦[wms][ de.toNat + 24 ] [128] ∗
          member n maxP ta (A 578) idx de live B Bsaved (i + wsLen (bs.drop i) + 1) none))
        (fun _ => SerdeStructObj.costObj cfg K646 K169 K81 (valueAs WNear.account) ign bs N i)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 368) 368 ∗
          n ↦[wms][ de.toNat + 24 ] [128] ∗ ∃ (p cap : UInt32),
          n ↦[i32][ out.toNat ] 0 ∗ n ↦[i32][ out.toNat + 4 ] p ∗ n ↦[i32][ out.toNat + 8 ] cap ∗
          n ↦[i32][ out.toNat + 12 ] UInt32.ofNat a.val.utf8ByteSize ∗ ⌜p ≠ 0⌝ ∗
          member n maxP ta (A 578) idx de live B Bsaved (bs.length - rF.length) (some (a, p, cap)) ∗
          rd n de ptr bs (bs.length - rF.length))) := by
  have hck : iprop(code n maxP inst mi A ∗ Cd) ⊢
      SerdeNextKey.code193 n maxP inst mi A ∗ ParseStr.code646 n maxP inst mi A := by
    iintro ⟨#Hcode, _⟩
    iapply code_keys n maxP inst mi A
    iexact Hcode
  have hcv : iprop(code n maxP inst mi A ∗ Cd) ⊢
      SerdeEnds.endCode n maxP inst mi A ∗ A 89 ↪[wf] FuncInst.wasm types[32]! inst f89 ∗
      A 169 ↪[wf] FuncInst.wasm types[14]! inst f169 ∗ SerdeAccountId.code169 n maxP inst mi A ∗
      ParseStr.code646 n maxP inst mi A := by
    iintro ⟨#Hcode, _⟩
    iapply code_values n maxP inst mi A
    iexact Hcode
  have hk := SerdeStructObjKeyState.keyHyp_precise (GF := GF) cfg lim inst mi A n g ta Cg maxP hm gt idx de ptr
    bs live B Bsaved K646 hlen hptr (by omega) hkeys hkeysSaved iprop(code n maxP inst mi A ∗ Cd) hck
  have hv := SerdeStructObjValueState.valueHyp (GF := GF) cfg lim inst mi A n g ta Cg maxP hm gt idx de ptr
    bs live B Bsaved K169 hlen hptr (by omega) hvalues iprop(code n maxP inst mi A ∗ Cd) hcv
  obtain ⟨_, hdvs, higns, hstrs, _, _⟩ := SerdeFromTrait.reader_facts
    (dv := valueAs WNear.account) (ign := ign) (fun _ => Or.inl rfl) hign bs
  have result := SerdeStructObjState.f228_obj_state_closing (GF := GF) cfg lim d type htype inst mi A n g ta hm hd Cg gt
    sp out de ptr idx x2 x3 x4 x5 ob bs i maxP hob hout (by omega) hptr hde hsp hal hi
    (valueAs WNear.account) ign K646 K169 K81 (member n maxP ta (A 578) idx de live B Bsaved)
    iprop(code n maxP inst mi A ∗ Cd) hk hv hignore
    (fun i j seen hj hb => member_closing n maxP ta (A 578) idx de live bs B Bsaved hclose hcloseSaved i j seen hj hb)
    hdvs higns hstrs N a rF hb0 hloop
  iintro ⟨#Hcode, #HCd⟩
  iapply result
  iframe Hcode HCd
  iunfold code at Hcode
  icases Hcode with ⟨#C193, -, -, #F205, #F201, #F193, #F89, #F90, #F81, #F169, #F77⟩
  iframe C193 F205 F201 F193 F89 F90 F81 F169 F77
end Proof
end WNear.Binary.SerdeStructObjModelState
namespace WNear.Binary.SerdeIgnObject
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.SerdeIgnExecution
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.VecFromElem (stk)
open WNear.Binary.SerdeRead (rd wsLen)
open WNear.Binary.SerdeStructObjKeyState (Bounds core member PreciseKeyConditions)
open WNear.Binary.SerdeStructObjValueState (ValueConditions)
open WNear.SerdeStructModel



section Proof
variable {GF : BundledGFunctors} [WasmGS NearState GF]

set_option maxRecDepth 100000 in
theorem object_loop_v86_closing_precise (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 42 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp out de ptr idx x2 x3 x4 x5 : UInt32) (ob bs : List UInt8) (i : Nat)
    (live : List (Nat × Nat)) (Cd : IProp GF) [Persistent Cd] (B Bsaved : Bounds) (K646 K169 K81 : Nat → Nat)
    (hob : ob.length = 16) (hout : out.toNat + 16 ≤ 2 ^ 32) (hlen : bs.length ≤ 4194304)
    (hptr : ptr.toNat + bs.length < 2 ^ 32) (hde : de.toNat + 25 ≤ 2 ^ 32)
    (hsp : 368 ≤ sp.toNat) (hal : sp.toNat % 8 = 0) (hi : i ≤ bs.length)
    (hkeys : PreciseKeyConditions cfg 2048 bs B K646) (hkeysSaved : PreciseKeyConditions cfg 2048 bs Bsaved K646)
    (hvalues : ValueConditions cfg 2048 bs B Bsaved K169)
    (hclose : SerdeStructObjModelState.ClosingConditions bs B)
    (hcloseSaved : SerdeStructObjModelState.ClosingConditions bs Bsaved)
    (hignored : ReachableIgnoreConditions cfg bs K81 B)
    (hignoredSaved : ReachableIgnoreConditions cfg bs K81 Bsaved)
    (N : Nat) (a : WNear.AccountId) (rF : List UInt8)
    (hb0 : bs[i + wsLen (bs.drop i)]? = some 0x7B)
    (hloop : objLoop "account_id" (valueAs WNear.account) ignored N none
      (bs.drop (i + wsLen (bs.drop i) + 1)) = some (some a, rF)) :
    SerdeStructObjModelState.code n 2048 inst mi A ∗ (SerdeIgnMember.code n 2048 inst mi A ∗ Cd) ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f228 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 de, .i32 x2, .i32 x3, .i32 x4, .i32 x5]⌝ ∗
          g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 368) 368 ∗ n ↦[wms][ out.toNat ] ob ∗
          rd n de ptr bs i ∗ n ↦[wms][ de.toNat + 24 ] [128] ∗
          member n 2048 ta (A 578) idx de live B Bsaved (i + wsLen (bs.drop i) + 1) none))
        (fun _ => SerdeStructObj.costObj cfg K646 K169 K81 (valueAs WNear.account) ignored bs N i)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 368) 368 ∗
          n ↦[wms][ de.toNat + 24 ] [128] ∗ ∃ (p cap : UInt32),
          n ↦[i32][ out.toNat ] 0 ∗ n ↦[i32][ out.toNat + 4 ] p ∗ n ↦[i32][ out.toNat + 8 ] cap ∗
          n ↦[i32][ out.toNat + 12 ] UInt32.ofNat a.val.utf8ByteSize ∗ ⌜p ≠ 0⌝ ∗
          member n 2048 ta (A 578) idx de live B Bsaved (bs.length - rF.length) (some (a, p, cap)) ∗
          rd n de ptr bs (bs.length - rF.length))) := by
  have hcode : iprop(SerdeStructObjModelState.code n 2048 inst mi A ∗ (SerdeIgnMember.code n 2048 inst mi A ∗ Cd)) ⊢
      SerdeEnds.endCode n 2048 inst mi A ∗ A 89 ↪[wf] FuncInst.wasm types[32]! inst f89 ∗
        A 81 ↪[wf] FuncInst.wasm types[32]! inst f81 ∗ SerdeIgnMember.code n 2048 inst mi A := by
    iintro ⟨#Hobj, #Hmember, _⟩
    iunfold SerdeStructObjModelState.code at Hobj
    icases Hobj with ⟨#C193, -, -, -, -, -, #F89, -, #F81, -⟩
    iunfold SerdeNextKey.code193 at C193
    icases C193 with ⟨#Cend, -⟩
    iframe Cend F89 F81 Hmember
  have hignore := ignoreHyp_v86 cfg lim inst mi A n g ta Cg hm gt idx de ptr bs live B Bsaved K81 hlen hptr (by omega)
    hignored hignoredSaved iprop(SerdeStructObjModelState.code n 2048 inst mi A ∗ (SerdeIgnMember.code n 2048 inst mi A ∗ Cd)) hcode
  exact SerdeStructObjModelState.f228_obj_model_closing_precise cfg lim d type htype inst mi A n g ta hm hd Cg gt sp out de ptr idx x2 x3 x4 x5
    ob bs i 2048 live iprop(SerdeIgnMember.code n 2048 inst mi A ∗ Cd) B Bsaved K646 K169 K81 ignored ignored_agrees
    hob hout (by omega) hptr hde hsp hal hi hkeys hkeysSaved hvalues hclose hcloseSaved hignore N a rF hb0 hloop
end Proof
end WNear.Binary.SerdeIgnObject
