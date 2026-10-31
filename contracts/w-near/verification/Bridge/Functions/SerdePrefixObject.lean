import Bridge.Functions.SerdePrefixBounds
import Bridge.Functions.SerdeObjectLedgerWrapper

set_option maxRecDepth 100000

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

theorem object_loop_prefix (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 42 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp out de ptr idx x2 x3 x4 x5 : UInt32) (ob bs : List UInt8) (i : Nat)
    (live : List (Nat × Nat)) (Cd : IProp GF) [Persistent Cd] (baseHL baseF : Nat) (K646 K169 K81 : Nat → Nat)
    (hob : ob.length = 16) (hout : out.toNat + 16 ≤ 2 ^ 32) (hlen : bs.length ≤ 4194304)
    (hptr : ptr.toNat + bs.length < 2 ^ 32) (hde : de.toNat + 25 ≤ 2 ^ 32)
    (hsp : 368 ≤ sp.toNat) (hal : sp.toNat % 8 = 0) (hi : i ≤ bs.length)
    (hsetup : LedgerSetup baseHL baseF)
    (hkeys : KeyGasCharges cfg bs (Bound bs (i + wsLen (bs.drop i) + 1) baseHL baseF false) K646) (hkeysSaved : KeyGasCharges cfg bs (Bound bs (i + wsLen (bs.drop i) + 1) baseHL baseF true) K646)
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
  exact SerdeStructObjPhaseReaders.object_loop_v86_closing cfg lim d type htype inst mi A n g ta hm hd Cg gt
    sp out de ptr idx x2 x3 x4 x5 ob bs i live Cd (Bound bs (i + wsLen (bs.drop i) + 1) baseHL baseF false) (Bound bs (i + wsLen (bs.drop i) + 1) baseHL baseF true) K646 K169 K81
    hob hout hlen hptr hde hsp hal hi
    (Bound.key_conditions cfg bs (i + wsLen (bs.drop i) + 1) baseHL baseF false K646 hlen hsetup.1 hkeys)
    (Bound.key_conditions cfg bs (i + wsLen (bs.drop i) + 1) baseHL baseF true K646 hlen hsetup.1 hkeysSaved)
    (Bound.value_conditions cfg bs (i + wsLen (bs.drop i) + 1) baseHL baseF K169 hlen hsetup.1 hsetup.2 hvalues)
    (Bound.closing bs (i + wsLen (bs.drop i) + 1) baseHL baseF false)
    (Bound.closing bs (i + wsLen (bs.drop i) + 1) baseHL baseF true)
    (Bound.ignore_conditions cfg bs (i + wsLen (bs.drop i) + 1) baseHL baseF false K81 hlen hsetup.1 hignored)
    (Bound.ignore_conditions cfg bs (i + wsLen (bs.drop i) + 1) baseHL baseF true K81 hlen hsetup.1 hignoredSaved)
    N a rF hb0 hloop

theorem core_forget (n maxP ta alloc : Nat) (idx de : UInt32) (live : List (Nat × Nat))
    (bs : List UInt8) (start baseHL baseF : Nat) (saved : Bool) (phase : Phase) (i : Nat) :
    SerdeStructObjKeyState.core (GF := GF) n maxP ta alloc idx de live (Bound bs start baseHL baseF saved phase) i ⊢
      SerdeStructObjKeyState.core n maxP ta alloc idx de live (Ledger bs baseHL baseF saved) i := by
  iintro H
  iunfold SerdeStructObjKeyState.core at H
  icases H with ⟨%hl, %F, %p, %cap, %sl, %⟨hb, hc⟩, Hvt, Htables, Hkey, Hident, Hscratch⟩
  iunfold SerdeStructObjKeyState.core
  iexists hl, F, p, cap, sl
  iframe Hvt Htables Hkey Hident Hscratch
  ipureintro
  exact ⟨hb.forget, hc⟩

theorem member_forget (n maxP ta alloc : Nat) (idx de : UInt32) (live : List (Nat × Nat))
    (bs : List UInt8) (start baseHL baseF : Nat) (phase : Phase) (i : Nat)
    (seen : Option (WNear.AccountId × UInt32 × UInt32)) :
    member (GF := GF) n maxP ta alloc idx de live (Bound bs start baseHL baseF false)
      (Bound bs start baseHL baseF true) phase i seen ⊢
    SerdeStructObjKeyState.member n maxP ta alloc idx de live (Ledger bs baseHL baseF false)
      (Ledger bs baseHL baseF true) i seen := by
  cases seen with
  | none => exact core_forget n maxP ta alloc idx de live bs start baseHL baseF false phase i
  | some v =>
    obtain ⟨a, p, cap⟩ := v
    iintro H
    iunfold member at H
    icases H with ⟨%hv, Hb, Hcore⟩
    iunfold SerdeStructObjKeyState.member
    dsimp only
    iframe Hb
    isplitr
    · ipureintro; exact hv
    iapply core_forget n maxP ta alloc idx de ((p.toNat, cap.toNat) :: live) bs start baseHL baseF true phase i
    iexact Hcore

theorem member_initial (n maxP ta alloc : Nat) (idx de ptrS sl : UInt32) (live : List (Nat × Nat))
    (bs : List UInt8) (baseHL baseF start : Nat) :
    AllocFirstFit.vt (GF := GF) n 1057464 idx ta alloc ∗ SerdeValueState.tables n ∗
      n ↦[wms][ 1051092 ] WNear.BalanceOfArgs.keyBytes ∗ n ↦[wms][ 1048576 ] SerdeIdent.identBytes ∗
      SerdeValueState.scratchPre n maxP baseHL live baseF de ptrS 0 sl ⊢
    member n maxP ta alloc idx de live (Bound bs start baseHL baseF false)
      (Bound bs start baseHL baseF true) (.member true) start none := by
  iintro ⟨Hvt, Htables, Hkey, Hident, Hscratch⟩
  iunfold member
  iunfold SerdeStructObjKeyState.core
  iexists baseHL, baseF, ptrS, 0, sl
  iframe Hvt Htables Hkey Hident Hscratch
  ipureintro
  exact ⟨Bound.initial bs start baseHL baseF, by decide⟩

theorem f78_prefix_cost (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 43 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp out de ptr idx : UInt32) (ob bs : List UInt8) (i : Nat)
    (live : List (Nat × Nat)) (Cd : IProp GF) [Persistent Cd] (baseHL baseF : Nat) (ptrS sl : UInt32) (K646 K169 K81 : Nat → Nat)
    (hob : ob.length = 16) (hout : out.toNat + 16 ≤ 2 ^ 32) (hlen : bs.length ≤ 4194304)
    (hptr : ptr.toNat + bs.length < 2 ^ 32) (hde : de.toNat + 25 ≤ 2 ^ 32)
    (hsp : 368 ≤ sp.toNat) (hal : sp.toNat % 8 = 0) (hi : i ≤ bs.length)
    (hsetup : LedgerSetup baseHL baseF)
    (hkeys : KeyGasCharges cfg bs (Bound bs (i + wsLen (bs.drop i) + 1) baseHL baseF false) K646) (hkeysSaved : KeyGasCharges cfg bs (Bound bs (i + wsLen (bs.drop i) + 1) baseHL baseF true) K646)
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
  have hs := object_loop_prefix (GF := GF) cfg lim (d + 1) types[36]! rfl inst mi A n g ta hm
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
