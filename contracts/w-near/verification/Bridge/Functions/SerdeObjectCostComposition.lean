import Bridge.Functions.SerdeIgnObjectV86
import Bridge.Functions.SerdeObjectKeyCoverage

namespace WNear.Binary.SerdeIgnObject
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.SerdeIgnExecution
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.VecFromElem (stk)
open WNear.Binary.SerdeRead (rd wsLen)
open WNear.Binary.SerdeStructObjKeyState (Bounds core member KeyConditions)
open WNear.Binary.SerdeStructObjValueState (ValueConditions)
open WNear.SerdeStructModel



section Proof
variable {GF : BundledGFunctors} [WasmGS NearState GF]

set_option maxRecDepth 100000 in
theorem object_loop_v86_closing (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 42 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp out de ptr idx x2 x3 x4 x5 : UInt32) (ob bs : List UInt8) (i : Nat)
    (live : List (Nat × Nat)) (Cd : IProp GF) [Persistent Cd] (B Bsaved : Bounds) (K646 K169 K81 : Nat → Nat)
    (hob : ob.length = 16) (hout : out.toNat + 16 ≤ 2 ^ 32) (hlen : bs.length ≤ 4194304)
    (hptr : ptr.toNat + bs.length < 2 ^ 32) (hde : de.toNat + 25 ≤ 2 ^ 32)
    (hsp : 368 ≤ sp.toNat) (hal : sp.toNat % 8 = 0) (hi : i ≤ bs.length)
    (hkeys : KeyConditions cfg 2048 bs B K646) (hkeysSaved : KeyConditions cfg 2048 bs Bsaved K646)
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
  exact SerdeStructObjModelState.f228_obj_model_closing cfg lim d type htype inst mi A n g ta hm hd Cg gt sp out de ptr idx x2 x3 x4 x5
    ob bs i 2048 live iprop(SerdeIgnMember.code n 2048 inst mi A ∗ Cd) B Bsaved K646 K169 K81 ignored ignored_agrees
    hob hout (by omega) hptr hde hsp hal hi hkeys hkeysSaved hvalues hclose hcloseSaved hignore N a rF hb0 hloop



set_option maxRecDepth 100000 in
theorem object_loop_v86_key_cost (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 42 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp out de ptr idx x2 x3 x4 x5 : UInt32) (ob bs : List UInt8) (i : Nat)
    (live : List (Nat × Nat)) (Cd : IProp GF) [Persistent Cd] (B Bsaved : Bounds) (K646 K169 K81 : Nat → Nat)
    (hob : ob.length = 16) (hout : out.toNat + 16 ≤ 2 ^ 32) (hlen : bs.length ≤ 4194304)
    (hptr : ptr.toNat + bs.length < 2 ^ 32) (hde : de.toNat + 25 ≤ 2 ^ 32)
    (hsp : 368 ≤ sp.toNat) (hal : sp.toNat % 8 = 0) (hi : i ≤ bs.length)
    (hkeys : KeyConditions cfg 2048 bs B K646) (hkeysSaved : KeyConditions cfg 2048 bs Bsaved K646)
    (hvalues : ValueConditions cfg 2048 bs B Bsaved K169)
    (hclose : SerdeStructObjModelState.ClosingConditions bs B)
    (hcloseSaved : SerdeStructObjModelState.ClosingConditions bs Bsaved)
    (hignored : ReachableIgnoreConditions cfg bs K81 B)
    (hignoredSaved : ReachableIgnoreConditions cfg bs K81 Bsaved)
    (N : Nat) (a : WNear.AccountId) (rF : List UInt8)
    (hb0 : bs[i + wsLen (bs.drop i)]? = some 0x7B)
    (hloop : objLoop "account_id" (valueAs WNear.account) ignored N none
      (bs.drop (i + wsLen (bs.drop i) + 1)) = some (some a, rF)) :
    ∃ keys, SerdeObjectCoverage.KeyWalk bs (i + wsLen (bs.drop i) + 1) true keys (bs.length - rF.length) ∧
      (∀ sample ∈ keys, NearInterface.Json.stringBody (bs.drop sample.1) [] = some (some sample.2.1, sample.2.2)) ∧
      SerdeKeyEsc.consumed bs keys + 2 * keys.length ≤ bs.length - rF.length - (i + wsLen (bs.drop i) + 1) ∧
      (    SerdeStructObjModelState.code n 2048 inst mi A ∗ (SerdeIgnMember.code n 2048 inst mi A ∗ Cd) ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f228 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 de, .i32 x2, .i32 x3, .i32 x4, .i32 x5]⌝ ∗
          g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 368) 368 ∗ n ↦[wms][ out.toNat ] ob ∗
          rd n de ptr bs i ∗ n ↦[wms][ de.toNat + 24 ] [128] ∗
          member n 2048 ta (A 578) idx de live B Bsaved (i + wsLen (bs.drop i) + 1) none))
        (fun _ => SerdeObjectCoverage.keyCharge K646 keys + SerdeStructObj.costObj cfg (fun _ => 0) K169 K81 (valueAs WNear.account) ignored bs N i)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 368) 368 ∗
          n ↦[wms][ de.toNat + 24 ] [128] ∗ ∃ (p cap : UInt32),
          n ↦[i32][ out.toNat ] 0 ∗ n ↦[i32][ out.toNat + 4 ] p ∗ n ↦[i32][ out.toNat + 8 ] cap ∗
          n ↦[i32][ out.toNat + 12 ] UInt32.ofNat a.val.utf8ByteSize ∗ ⌜p ≠ 0⌝ ∗
          member n 2048 ta (A 578) idx de live B Bsaved (bs.length - rF.length) (some (a, p, cap)) ∗
          rd n de ptr bs (bs.length - rF.length)))) := by
  obtain ⟨keys, hw, hmKeys, hcover, he⟩ := SerdeObjectCoverage.object_key_cost cfg K646 K169 K81 bs i N a rF hb0 hloop
  refine ⟨keys, hw, hmKeys, hcover, ?_⟩
  have result := object_loop_v86_closing (GF := GF) cfg lim d type htype inst mi A n g ta hm hd Cg gt
    sp out de ptr idx x2 x3 x4 x5 ob bs i live Cd B Bsaved K646 K169 K81 hob hout hlen hptr hde hsp hal hi
    hkeys hkeysSaved hvalues hclose hcloseSaved hignored hignoredSaved N a rF hb0 hloop
  simpa only [he] using result

end Proof
end WNear.Binary.SerdeIgnObject
