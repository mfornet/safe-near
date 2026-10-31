import Bridge.Functions.SerdeObjectLedger
import Bridge.Functions.SerdeObjectCostComposition

namespace WNear.Binary.SerdeObjectMixedTrace
open Wasm Wasm.Near
open WNear.SerdeStructModel
open WNear.Binary.SerdeRead (wsLen)

/-- The initial allocator/heap resource instance still required from the actual input pipeline. -/
def LedgerSetup (baseHL baseF : Nat) : Prop := baseHL + 18230154 ≤ 100663296 ∧ 1 ≤ baseF

open WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.VecFromElem (stk)
open WNear.Binary.SerdeRead (rd)
open WNear.Binary.SerdeStructObjKeyState (member)
open WNear.Binary.SerdeIgnObject (ignored)
section Resource
variable {GF : BundledGFunctors} [WasmGS NearState GF]

theorem object_loop_ledger (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 42 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp out de ptr idx x2 x3 x4 x5 : UInt32) (ob bs : List UInt8) (i : Nat)
    (live : List (Nat × Nat)) (Cd : IProp GF) [Persistent Cd] (baseHL baseF : Nat) (K646 K169 K81 : Nat → Nat)
    (hob : ob.length = 16) (hout : out.toNat + 16 ≤ 2 ^ 32) (hlen : bs.length ≤ 4194304)
    (hptr : ptr.toNat + bs.length < 2 ^ 32) (hde : de.toNat + 25 ≤ 2 ^ 32)
    (hsp : 368 ≤ sp.toNat) (hal : sp.toNat % 8 = 0) (hi : i ≤ bs.length)
    (hsetup : LedgerSetup baseHL baseF)
    (hkeys : KeyRoomCharges cfg 2048 bs (Ledger bs baseHL baseF false) K646) (hkeysSaved : KeyRoomCharges cfg 2048 bs (Ledger bs baseHL baseF true) K646)
    (hvalues : ValueRoomCharges cfg 2048 bs (Ledger bs baseHL baseF false) K169)
    (hignored : IgnoreCharges cfg bs K81 (Ledger bs baseHL baseF false))
    (hignoredSaved : IgnoreCharges cfg bs K81 (Ledger bs baseHL baseF true))
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
          member n 2048 ta (A 578) idx de live (Ledger bs baseHL baseF false) (Ledger bs baseHL baseF true) (i + wsLen (bs.drop i) + 1) none))
        (fun _ => SerdeObjectCoverage.keyCharge K646 keys + SerdeStructObj.costObj cfg (fun _ => 0) K169 K81 (valueAs WNear.account) ignored bs N i)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 368) 368 ∗
          n ↦[wms][ de.toNat + 24 ] [128] ∗ ∃ (p cap : UInt32),
          n ↦[i32][ out.toNat ] 0 ∗ n ↦[i32][ out.toNat + 4 ] p ∗ n ↦[i32][ out.toNat + 8 ] cap ∗
          n ↦[i32][ out.toNat + 12 ] UInt32.ofNat a.val.utf8ByteSize ∗ ⌜p ≠ 0⌝ ∗
          member n 2048 ta (A 578) idx de live (Ledger bs baseHL baseF false) (Ledger bs baseHL baseF true) (bs.length - rF.length) (some (a, p, cap)) ∗
          rd n de ptr bs (bs.length - rF.length)))) := by
  exact SerdeIgnObject.object_loop_v86_key_cost cfg lim d type htype inst mi A n g ta hm hd Cg gt
    sp out de ptr idx x2 x3 x4 x5 ob bs i live Cd (Ledger bs baseHL baseF false) (Ledger bs baseHL baseF true)
    K646 K169 K81 hob hout hlen hptr hde hsp hal hi
    (Ledger.key_conditions cfg bs baseHL baseF false K646 hkeys)
    (Ledger.key_conditions cfg bs baseHL baseF true K646 hkeysSaved)
    (Ledger.value_conditions cfg bs baseHL baseF K169 hsetup.2 hvalues)
    (Ledger.closing bs baseHL baseF false) (Ledger.closing bs baseHL baseF true)
    (Ledger.ignore_conditions cfg bs baseHL baseF false K81 hlen hsetup.1 hignored)
    (Ledger.ignore_conditions cfg bs baseHL baseF true K81 hlen hsetup.1 hignoredSaved)
    N a rF hb0 hloop

/-- Actual empty scratch resources establish the initial ledger member state. -/
theorem member_initial (n maxP ta alloc : Nat) (idx de ptrS sl : UInt32) (live : List (Nat × Nat))
    (bs : List UInt8) (baseHL baseF i : Nat) :
    AllocFirstFit.vt (GF := GF) n 1057464 idx ta alloc ∗ SerdeValueState.tables n ∗
      n ↦[wms][ 1051092 ] WNear.BalanceOfArgs.keyBytes ∗ n ↦[wms][ 1048576 ] SerdeIdent.identBytes ∗
      SerdeValueState.scratchPre n maxP baseHL live baseF de ptrS 0 sl ⊢
    member n maxP ta alloc idx de live (Ledger bs baseHL baseF false) (Ledger bs baseHL baseF true) i none := by
  iintro ⟨Hvt, Htables, Hkey, Hident, Hscratch⟩
  iunfold member
  iunfold SerdeStructObjKeyState.core
  iexists baseHL, baseF, ptrS, 0, sl
  iframe Hvt Htables Hkey Hident Hscratch
  ipureintro
  exact ⟨Ledger.initial bs baseHL baseF i, by decide⟩

set_option maxRecDepth 100000 in
theorem object_loop_ledger_initial (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 42 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp out de ptr idx x2 x3 x4 x5 : UInt32) (ob bs : List UInt8) (i : Nat)
    (live : List (Nat × Nat)) (Cd : IProp GF) [Persistent Cd] (baseHL baseF : Nat) (ptrS sl : UInt32) (K646 K169 K81 : Nat → Nat)
    (hob : ob.length = 16) (hout : out.toNat + 16 ≤ 2 ^ 32) (hlen : bs.length ≤ 4194304)
    (hptr : ptr.toNat + bs.length < 2 ^ 32) (hde : de.toNat + 25 ≤ 2 ^ 32)
    (hsp : 368 ≤ sp.toNat) (hal : sp.toNat % 8 = 0) (hi : i ≤ bs.length)
    (hsetup : LedgerSetup baseHL baseF)
    (hkeys : KeyRoomCharges cfg 2048 bs (Ledger bs baseHL baseF false) K646) (hkeysSaved : KeyRoomCharges cfg 2048 bs (Ledger bs baseHL baseF true) K646)
    (hvalues : ValueRoomCharges cfg 2048 bs (Ledger bs baseHL baseF false) K169)
    (hignored : IgnoreCharges cfg bs K81 (Ledger bs baseHL baseF false))
    (hignoredSaved : IgnoreCharges cfg bs K81 (Ledger bs baseHL baseF true))
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
          (AllocFirstFit.vt n 1057464 idx ta (A 578) ∗ SerdeValueState.tables n ∗
            n ↦[wms][ 1051092 ] WNear.BalanceOfArgs.keyBytes ∗ n ↦[wms][ 1048576 ] SerdeIdent.identBytes ∗
            SerdeValueState.scratchPre n 2048 baseHL live baseF de ptrS 0 sl)))
        (fun _ => SerdeObjectCoverage.keyCharge K646 keys + SerdeStructObj.costObj cfg (fun _ => 0) K169 K81 (valueAs WNear.account) ignored bs N i)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 368) 368 ∗
          n ↦[wms][ de.toNat + 24 ] [128] ∗ ∃ (p cap : UInt32),
          n ↦[i32][ out.toNat ] 0 ∗ n ↦[i32][ out.toNat + 4 ] p ∗ n ↦[i32][ out.toNat + 8 ] cap ∗
          n ↦[i32][ out.toNat + 12 ] UInt32.ofNat a.val.utf8ByteSize ∗ ⌜p ≠ 0⌝ ∗
          member n 2048 ta (A 578) idx de live (Ledger bs baseHL baseF false) (Ledger bs baseHL baseF true) (bs.length - rF.length) (some (a, p, cap)) ∗
          rd n de ptr bs (bs.length - rF.length)))) := by
  obtain ⟨keys, hw, hmKeys, hcover, hreader⟩ := object_loop_ledger (GF := GF) cfg lim d type htype inst mi A n g ta hm hd Cg gt
    sp out de ptr idx x2 x3 x4 x5 ob bs i live Cd baseHL baseF K646 K169 K81 hob hout hlen hptr hde hsp hal hi hsetup
    hkeys hkeysSaved hvalues hignored hignoredSaved N a rF hb0 hloop
  refine ⟨keys, hw, hmKeys, hcover, hreader.trans ?_⟩
  apply SerdeValueState.spec_repack
  · intro args
    iintro ⟨%ha, Hg, Hst, Ho, Hrd, Hdepth, Hvt, Htables, Hkey, Hident, Hscratch⟩
    isplitr
    · ipureintro; exact ha
    iframe Hg Hst Ho Hrd Hdepth
    iapply member_initial n 2048 ta (A 578) idx de ptrS sl live bs baseHL baseF (i + wsLen (bs.drop i) + 1)
    iframe Hvt Htables Hkey Hident Hscratch
  · intro args rs
    iintro H
    iexact H

end Resource

end WNear.Binary.SerdeObjectMixedTrace
