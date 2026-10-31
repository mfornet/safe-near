import Bridge.Functions.SerdeBundledKeyState
import Bridge.Functions.SerdePrefixObject

set_option maxRecDepth 100000

namespace WNear.Binary.SerdeStructObjPhaseReaders
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.VecFromElem (stk roomFor)
open WNear.Binary.SerdeRead (rd wsLen)
open WNear.Binary.ParseStr (strRun borrowed roomRun)
open WNear.Binary.ParseStrSuccess (appendChunks)
open WNear.Binary.ScratchGrow (endState endFreeBound growthPages)
open WNear.Binary.SerdeValueState (scratchPre)

open WNear.Binary.SerdeStructObjKeyState (Bounds core key_exact scratch_alignment)
open WNear.Binary.SerdeStructObjPhase (Phase)

open NearInterface.Json WNear.JsonFuel WNear.SerdeStructModel
open WNear.Binary.SerdeStructObjModelState (code code_keys code_values)
open WNear.Binary.SerdeIgnObject (ignored ignored_agrees)
section Resource
variable {GF : BundledGFunctors} [WasmGS NearState GF]

set_option maxRecDepth 100000
theorem f228_obj_model_closing_bundled (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 42 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp out de ptr idx x2 x3 x4 x5 : UInt32) (ob bs : List UInt8) (i maxP : Nat)
    (live : List (Nat × Nat)) (Cd : IProp GF) [Persistent Cd] (B Bsaved : PhaseBounds) (K646 K169 K81 : Nat → Nat)
    (ign : List UInt8 → Option (Unit × List UInt8)) (hign : Agrees ign valueSkip)
    (hob : ob.length = 16) (hout : out.toNat + 16 ≤ 2 ^ 32) (hlen : bs.length < 2 ^ 24)
    (hptr : ptr.toNat + bs.length < 2 ^ 32) (hde : de.toNat + 25 ≤ 2 ^ 32)
    (hsp : 368 ≤ sp.toNat) (hal : sp.toNat % 8 = 0) (hi : i ≤ bs.length)
    (hkeys : BundledKeyConditions cfg maxP bs B K646) (hkeysSaved : BundledKeyConditions cfg maxP bs Bsaved K646)
    (hvalues : ValueConditions cfg maxP bs B Bsaved K169)
    (hclose : ClosingConditions bs B)
    (hcloseSaved : ClosingConditions bs Bsaved)
    (hignore : SerdeStructObjPhase.IgnoreHyp (GF := GF) cfg lim inst mi n g Cg gt de ptr bs ign K81
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
          member n maxP ta (A 578) idx de live B Bsaved (.member true) (i + wsLen (bs.drop i) + 1) none))
        (fun _ => SerdeStructObj.costObj cfg K646 K169 K81 (valueAs WNear.account) ign bs N i)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 368) 368 ∗
          n ↦[wms][ de.toNat + 24 ] [128] ∗ ∃ (p cap : UInt32),
          n ↦[i32][ out.toNat ] 0 ∗ n ↦[i32][ out.toNat + 4 ] p ∗ n ↦[i32][ out.toNat + 8 ] cap ∗
          n ↦[i32][ out.toNat + 12 ] UInt32.ofNat a.val.utf8ByteSize ∗ ⌜p ≠ 0⌝ ∗
          member n maxP ta (A 578) idx de live B Bsaved .done (bs.length - rF.length) (some (a, p, cap)) ∗
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
  have hk := keyHyp_bundled (GF := GF) cfg lim inst mi A n g ta Cg maxP hm gt idx de ptr
    bs live B Bsaved K646 hlen hptr (by omega) hkeys hkeysSaved iprop(code n maxP inst mi A ∗ Cd) hck
  have hv := valueHyp (GF := GF) cfg lim inst mi A n g ta Cg maxP hm gt idx de ptr
    bs live B Bsaved K169 hlen hptr (by omega) hvalues iprop(code n maxP inst mi A ∗ Cd) hcv
  obtain ⟨_, hdvs, higns, hstrs, _, _⟩ := SerdeFromTrait.reader_facts
    (dv := valueAs WNear.account) (ign := ign) (fun _ => Or.inl rfl) hign bs
  have result := SerdeStructObjPhase.f228_obj_state_closing (GF := GF) cfg lim d type htype inst mi A n g ta hm hd Cg gt
    sp out de ptr idx x2 x3 x4 x5 ob bs i maxP hob hout (by omega) hptr hde hsp hal hi
    (valueAs WNear.account) ign K646 K169 K81 (member n maxP ta (A 578) idx de live B Bsaved)
    iprop(code n maxP inst mi A ∗ Cd) hk hv hignore
    (fun first i j seen hj hb => member_closing n maxP ta (A 578) idx de live bs B Bsaved hclose hcloseSaved first i j seen hj hb)
    hdvs higns hstrs N a rF hb0 hloop
  iintro ⟨#Hcode, #HCd⟩
  iapply result
  iframe Hcode HCd
  iunfold code at Hcode
  icases Hcode with ⟨#C193, -, -, #F205, #F201, #F193, #F89, #F90, #F81, #F169, #F77⟩
  iframe C193 F205 F201 F193 F89 F90 F81 F169 F77
set_option maxRecDepth 100000 in
theorem object_loop_v86_closing_bundled (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 42 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp out de ptr idx x2 x3 x4 x5 : UInt32) (ob bs : List UInt8) (i : Nat)
    (live : List (Nat × Nat)) (Cd : IProp GF) [Persistent Cd] (B Bsaved : PhaseBounds) (K646 K169 K81 : Nat → Nat)
    (hob : ob.length = 16) (hout : out.toNat + 16 ≤ 2 ^ 32) (hlen : bs.length ≤ 4194304)
    (hptr : ptr.toNat + bs.length < 2 ^ 32) (hde : de.toNat + 25 ≤ 2 ^ 32)
    (hsp : 368 ≤ sp.toNat) (hal : sp.toNat % 8 = 0) (hi : i ≤ bs.length)
    (hkeys : BundledKeyConditions cfg 2048 bs B K646) (hkeysSaved : BundledKeyConditions cfg 2048 bs Bsaved K646)
    (hvalues : ValueConditions cfg 2048 bs B Bsaved K169)
    (hclose : ClosingConditions bs B)
    (hcloseSaved : ClosingConditions bs Bsaved)
    (hignored : IgnoreConditions cfg bs K81 B)
    (hignoredSaved : IgnoreConditions cfg bs K81 Bsaved)
    (N : Nat) (a : WNear.AccountId) (rF : List UInt8)
    (hb0 : bs[i + wsLen (bs.drop i)]? = some 0x7B)
    (hloop : objLoop "account_id" (valueAs WNear.account) ignored N none
      (bs.drop (i + wsLen (bs.drop i) + 1)) = some (some a, rF)) :
    SerdeStructObjModelState.code n 2048 inst mi A ∗ (SerdeIgnMember.code n 2048 inst mi A ∗ Cd) ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f228 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 de, .i32 x2, .i32 x3, .i32 x4, .i32 x5]⌝ ∗
          g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 368) 368 ∗ n ↦[wms][ out.toNat ] ob ∗
          rd n de ptr bs i ∗ n ↦[wms][ de.toNat + 24 ] [128] ∗
          member n 2048 ta (A 578) idx de live B Bsaved (.member true) (i + wsLen (bs.drop i) + 1) none))
        (fun _ => SerdeStructObj.costObj cfg K646 K169 K81 (valueAs WNear.account) ignored bs N i)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 368) 368 ∗
          n ↦[wms][ de.toNat + 24 ] [128] ∗ ∃ (p cap : UInt32),
          n ↦[i32][ out.toNat ] 0 ∗ n ↦[i32][ out.toNat + 4 ] p ∗ n ↦[i32][ out.toNat + 8 ] cap ∗
          n ↦[i32][ out.toNat + 12 ] UInt32.ofNat a.val.utf8ByteSize ∗ ⌜p ≠ 0⌝ ∗
          member n 2048 ta (A 578) idx de live B Bsaved .done (bs.length - rF.length) (some (a, p, cap)) ∗
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
  exact f228_obj_model_closing_bundled cfg lim d type htype inst mi A n g ta hm hd Cg gt sp out de ptr idx x2 x3 x4 x5
    ob bs i 2048 live iprop(SerdeIgnMember.code n 2048 inst mi A ∗ Cd) B Bsaved K646 K169 K81 ignored ignored_agrees
    hob hout (by omega) hptr hde hsp hal hi hkeys hkeysSaved hvalues hclose hcloseSaved hignore N a rF hb0 hloop
end Resource
end WNear.Binary.SerdeStructObjPhaseReaders
namespace WNear.Binary.SerdeObjectPrefix
open Wasm Wasm.Near NearInterface.Json
open WNear.Binary.ScratchMixedTrace
open WNear.Binary.SerdeObjectMixedTrace
open WNear.Binary.SerdeStructObjPhase (Phase)
open WNear.Binary.SerdeStructObjPhaseReaders (PhaseBounds)


open WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.SerdeStructModel
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.VecFromElem (stk)
open WNear.Binary.SerdeRead (rd wsLen)
open WNear.Binary.SerdeStructObjPhaseReaders (member)
open WNear.Binary.SerdeIgnObject (ignored)
section Resource
variable {GF : BundledGFunctors} [WasmGS NearState GF]

theorem object_loop_bundled (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 42 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp out de ptr idx x2 x3 x4 x5 : UInt32) (ob bs : List UInt8) (i : Nat)
    (live : List (Nat × Nat)) (Cd : IProp GF) [Persistent Cd] (baseHL baseF : Nat) (K646 K169 K81 : Nat → Nat)
    (hob : ob.length = 16) (hout : out.toNat + 16 ≤ 2 ^ 32) (hlen : bs.length ≤ 4194304)
    (hptr : ptr.toNat + bs.length < 2 ^ 32) (hde : de.toNat + 25 ≤ 2 ^ 32)
    (hsp : 368 ≤ sp.toNat) (hal : sp.toNat % 8 = 0) (hi : i ≤ bs.length)
    (hsetup : LedgerSetup baseHL baseF)
    (hkeys : BundledKeyGasCharges cfg bs (Bound bs (i + wsLen (bs.drop i) + 1) baseHL baseF false) K646) (hkeysSaved : BundledKeyGasCharges cfg bs (Bound bs (i + wsLen (bs.drop i) + 1) baseHL baseF true) K646)
    (hvalues : ValueGasCharges cfg bs (Bound bs (i + wsLen (bs.drop i) + 1) baseHL baseF false) K169)
    (hignored : IgnoreGasCharges cfg bs (Bound bs (i + wsLen (bs.drop i) + 1) baseHL baseF false) K81) (hignoredSaved : IgnoreGasCharges cfg bs (Bound bs (i + wsLen (bs.drop i) + 1) baseHL baseF true) K81)
    (N : Nat) (a : WNear.AccountId) (rF : List UInt8)
    (hb0 : bs[i + wsLen (bs.drop i)]? = some 0x7B)
    (hloop : objLoop "account_id" (valueAs WNear.account) ignored N none
      (bs.drop (i + wsLen (bs.drop i) + 1)) = some (some a, rF)) :
    SerdeStructObjModelState.code n 2048 inst mi A ∗ (SerdeIgnMember.code n 2048 inst mi A ∗ Cd) ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f228 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 de, .i32 x2, .i32 x3, .i32 x4, .i32 x5]⌝ ∗
          g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 368) 368 ∗ n ↦[wms][ out.toNat ] ob ∗
          rd n de ptr bs i ∗ n ↦[wms][ de.toNat + 24 ] [128] ∗
          member n 2048 ta (A 578) idx de live (Bound bs (i + wsLen (bs.drop i) + 1) baseHL baseF false) (Bound bs (i + wsLen (bs.drop i) + 1) baseHL baseF true) (.member true) (i + wsLen (bs.drop i) + 1) none))
        (fun _ => SerdeStructObj.costObj cfg K646 K169 K81 (valueAs WNear.account) ignored bs N i)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 368) 368 ∗
          n ↦[wms][ de.toNat + 24 ] [128] ∗ ∃ (p cap : UInt32),
          n ↦[i32][ out.toNat ] 0 ∗ n ↦[i32][ out.toNat + 4 ] p ∗ n ↦[i32][ out.toNat + 8 ] cap ∗
          n ↦[i32][ out.toNat + 12 ] UInt32.ofNat a.val.utf8ByteSize ∗ ⌜p ≠ 0⌝ ∗
          member n 2048 ta (A 578) idx de live (Bound bs (i + wsLen (bs.drop i) + 1) baseHL baseF false) (Bound bs (i + wsLen (bs.drop i) + 1) baseHL baseF true) .done (bs.length - rF.length) (some (a, p, cap)) ∗
          rd n de ptr bs (bs.length - rF.length))) := by
  exact SerdeStructObjPhaseReaders.object_loop_v86_closing_bundled cfg lim d type htype inst mi A n g ta hm hd Cg gt
    sp out de ptr idx x2 x3 x4 x5 ob bs i live Cd (Bound bs (i + wsLen (bs.drop i) + 1) baseHL baseF false) (Bound bs (i + wsLen (bs.drop i) + 1) baseHL baseF true) K646 K169 K81
    hob hout hlen hptr hde hsp hal hi
    (Bound.bundled_key_conditions cfg bs (i + wsLen (bs.drop i) + 1) baseHL baseF false K646 hlen hsetup.1 hkeys)
    (Bound.bundled_key_conditions cfg bs (i + wsLen (bs.drop i) + 1) baseHL baseF true K646 hlen hsetup.1 hkeysSaved)
    (Bound.value_conditions cfg bs (i + wsLen (bs.drop i) + 1) baseHL baseF K169 hlen hsetup.1 hsetup.2 hvalues)
    (Bound.closing bs (i + wsLen (bs.drop i) + 1) baseHL baseF false)
    (Bound.closing bs (i + wsLen (bs.drop i) + 1) baseHL baseF true)
    (Bound.ignore_conditions cfg bs (i + wsLen (bs.drop i) + 1) baseHL baseF false K81 hlen hsetup.1 hignored)
    (Bound.ignore_conditions cfg bs (i + wsLen (bs.drop i) + 1) baseHL baseF true K81 hlen hsetup.1 hignoredSaved)
    N a rF hb0 hloop

theorem f78_bundled_cost (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 43 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp out de ptr idx : UInt32) (ob bs : List UInt8) (i : Nat)
    (live : List (Nat × Nat)) (Cd : IProp GF) [Persistent Cd] (baseHL baseF : Nat) (ptrS sl : UInt32) (K646 K169 K81 : Nat → Nat)
    (hob : ob.length = 16) (hout : out.toNat + 16 ≤ 2 ^ 32) (hlen : bs.length ≤ 4194304)
    (hptr : ptr.toNat + bs.length < 2 ^ 32) (hde : de.toNat + 25 ≤ 2 ^ 32)
    (hsp : 368 ≤ sp.toNat) (hal : sp.toNat % 8 = 0) (hi : i ≤ bs.length)
    (hsetup : LedgerSetup baseHL baseF)
    (hkeys : BundledKeyGasCharges cfg bs (Bound bs (i + wsLen (bs.drop i) + 1) baseHL baseF false) K646) (hkeysSaved : BundledKeyGasCharges cfg bs (Bound bs (i + wsLen (bs.drop i) + 1) baseHL baseF true) K646)
    (hvalues : ValueGasCharges cfg bs (Bound bs (i + wsLen (bs.drop i) + 1) baseHL baseF false) K169)
    (hignored : IgnoreGasCharges cfg bs (Bound bs (i + wsLen (bs.drop i) + 1) baseHL baseF false) K81) (hignoredSaved : IgnoreGasCharges cfg bs (Bound bs (i + wsLen (bs.drop i) + 1) baseHL baseF true) K81)
    (N : Nat) (a : WNear.AccountId) (rF : List UInt8)
    (hb0 : bs[i + wsLen (bs.drop i)]? = some 0x7B)
    (hloop : objLoop "account_id" (valueAs WNear.account) ignored N none
      (bs.drop (i + wsLen (bs.drop i) + 1)) = some (some a, rF)) :
    SerdeStructObjModelState.code n 2048 inst mi A ∗ (SerdeIgnMember.code n 2048 inst mi A ∗ Cd) ∗
      A 228 ↪[wf] FuncInst.wasm types[36]! inst f228 ∗ inst ↪[inst] mi ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f78 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 de]⌝ ∗
          g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 368) 368 ∗ n ↦[wms][ out.toNat ] ob ∗
          rd n de ptr bs i ∗ n ↦[wms][ de.toNat + 24 ] [128] ∗
          (AllocFirstFit.vt n 1057464 idx ta (A 578) ∗ SerdeValueState.tables n ∗
            n ↦[wms][ 1051092 ] WNear.BalanceOfArgs.keyBytes ∗ n ↦[wms][ 1048576 ] SerdeIdent.identBytes ∗
            SerdeValueState.scratchPre n 2048 baseHL live baseF de ptrS 0 sl)))
        (fun _ => 40 * cfg.regularOpCost + SerdeStructObj.costObj cfg K646 K169 K81 (valueAs WNear.account) ignored bs N i)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 368) 368 ∗
          n ↦[wms][ de.toNat + 24 ] [128] ∗ ∃ (p cap : UInt32),
          n ↦[i32][ out.toNat ] 0 ∗ n ↦[i32][ out.toNat + 4 ] p ∗ n ↦[i32][ out.toNat + 8 ] cap ∗
          n ↦[i32][ out.toNat + 12 ] UInt32.ofNat a.val.utf8ByteSize ∗ ⌜p ≠ 0⌝ ∗
          SerdeStructObjKeyState.member n 2048 ta (A 578) idx de live (Ledger bs baseHL baseF false) (Ledger bs baseHL baseF true) (bs.length - rF.length) (some (a, p, cap)) ∗
          rd n de ptr bs (bs.length - rF.length))) := by
  have hs := object_loop_bundled (GF := GF) cfg lim (d + 1) types[36]! rfl inst mi A n g ta hm
    (by omega) Cg gt sp out de ptr idx out out out out ob bs i live Cd baseHL baseF K646 K169 K81
    hob hout hlen hptr hde hsp hal hi hsetup hkeys hkeysSaved hvalues hignored hignoredSaved N a rF hb0 hloop
  iintro ⟨#HC, #HI, #F228, #Hi⟩
  ihave #S := hs $$ [HC HI]
  · iframe HC HI
  iapply f78_of_object_spec cfg lim d type htype inst mi A n g ta hm (by omega)
  iframe F228 Hi
  iapply (SerdeValueState.spec_repack ?hP ?hQ) $$ S
  case hP =>
    intro args
    iintro ⟨%ha, Hg, Hst, Ho, Hrd, Hdepth, Hvt, Htables, Hkey, Hident, Hscratch⟩
    isplitr
    · ipureintro; exact ha
    iframe Hg Hst Ho Hrd Hdepth
    iapply member_initial n 2048 ta (A 578) idx de ptrS sl live bs baseHL baseF (i + wsLen (bs.drop i) + 1)
    iframe Hvt Htables Hkey Hident Hscratch
  case hQ =>
    intro args rs
    iintro ⟨%hrs, Hg, Hst, Hdepth, %p, %cap, O0, O4, O8, O12, %hp, Hmember, Hrd⟩
    iframe Hg Hst Hdepth O0 O4 O8 O12 Hrd
    isplitr
    · ipureintro; exact hrs
    isplitr
    · ipureintro; exact hp
    iapply member_forget n 2048 ta (A 578) idx de live bs (i + wsLen (bs.drop i) + 1) baseHL baseF .done (bs.length - rF.length) (some (a, p, cap))
    iexact Hmember

end Resource
end WNear.Binary.SerdeObjectPrefix
