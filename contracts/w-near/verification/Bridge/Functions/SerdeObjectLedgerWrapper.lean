import Bridge.Functions.SerdeObjectLedgerComposition

namespace WNear.Binary.SerdeObjectMixedTrace
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.Interface (IfaceMod)
open WNear.SerdeStructModel
open WNear.Binary.SerdeRead (rd wsLen)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_intro stk_word stk_addr)
open WNear.Binary.SerdeStructObjKeyState (member)
open WNear.Binary.SerdeIgnObject (ignored)
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.ArgsLeaves (sliceRead deserializer)
open WNear.Binary.SerdeFromTrait (code66 frame66 i64_one)
open WNear.Binary.SerdeValueState (scratchPre)
section Resource
variable {GF : BundledGFunctors} [WasmGS NearState GF]
/-- The real f78 wrapper composes any complete successful object contract. -/
theorem f78_of_object_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 1 < lim.maxCallDepth) (Cg K : Nat) (out de : UInt32) (P Q : IProp GF) :
    MFunSpec cfg lim (d + 1) types[36]! inst mi f228 Cg
      (fun args => iprop(⌜args = [.i32 out, .i32 de, .i32 out, .i32 out, .i32 out, .i32 out]⌝ ∗ P))
      (fun _ => K) (fun _ rs => iprop(⌜rs = []⌝ ∗ Q)) ∗
      A 228 ↪[wf] FuncInst.wasm types[36]! inst f228 ∗ inst ↪[inst] mi ⊢
    MFunSpec cfg lim d type inst mi f78 Cg
      (fun args => iprop(⌜args = [.i32 out, .i32 de]⌝ ∗ P))
      (fun _ => 40 * cfg.regularOpCost + K) (fun _ rs => iprop(⌜rs = []⌝ ∗ Q)) := by
  iintro ⟨#S, #F228, #Hi⟩
  have ha228 := hm.funcs 228 (by decide)
  have t36 : types[36]!.params.length = 6 := rfl
  iapply MFunSpec_intro
  imodintro
  iintro %args %R ⟨%ha, HP⟩ Hc
  subst ha
  simp only [f78]
  rw [show 40 * cfg.regularOpCost + K + R = 40 * cfg.regularOpCost + (K + R) by omega]
  mstep; mstep; mstep; mstep; mstep; mstep
  mcall S using [HP]
  · isplitr
    · ipureintro; trivial
    · iexact HP
  icases HQ with ⟨%hrs, HQ⟩
  subst hrs
  repeat mstep
  isplitl [Hc]
  · iapply BorrowMut.credits_le
    iframe Hc
    ipureintro; omega
  iframe HQ
  ipureintro; simp [htype]

set_option maxRecDepth 100000 in
theorem f78_ledger_initial (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 43 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp out de ptr idx : UInt32) (ob bs : List UInt8) (i : Nat)
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
      (    SerdeStructObjModelState.code n 2048 inst mi A ∗ (SerdeIgnMember.code n 2048 inst mi A ∗ Cd) ∗
      A 228 ↪[wf] FuncInst.wasm types[36]! inst f228 ∗ inst ↪[inst] mi ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f78 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 de]⌝ ∗
          g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 368) 368 ∗ n ↦[wms][ out.toNat ] ob ∗
          rd n de ptr bs i ∗ n ↦[wms][ de.toNat + 24 ] [128] ∗
          (AllocFirstFit.vt n 1057464 idx ta (A 578) ∗ SerdeValueState.tables n ∗
            n ↦[wms][ 1051092 ] WNear.BalanceOfArgs.keyBytes ∗ n ↦[wms][ 1048576 ] SerdeIdent.identBytes ∗
            SerdeValueState.scratchPre n 2048 baseHL live baseF de ptrS 0 sl)))
        (fun _ => 40 * cfg.regularOpCost + (SerdeObjectCoverage.keyCharge K646 keys + SerdeStructObj.costObj cfg (fun _ => 0) K169 K81 (valueAs WNear.account) ignored bs N i))
        (fun _ rs => iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 368) 368 ∗
          n ↦[wms][ de.toNat + 24 ] [128] ∗ ∃ (p cap : UInt32),
          n ↦[i32][ out.toNat ] 0 ∗ n ↦[i32][ out.toNat + 4 ] p ∗ n ↦[i32][ out.toNat + 8 ] cap ∗
          n ↦[i32][ out.toNat + 12 ] UInt32.ofNat a.val.utf8ByteSize ∗ ⌜p ≠ 0⌝ ∗
          member n 2048 ta (A 578) idx de live (Ledger bs baseHL baseF false) (Ledger bs baseHL baseF true) (bs.length - rF.length) (some (a, p, cap)) ∗
          rd n de ptr bs (bs.length - rF.length)))) := by
  obtain ⟨keys, hw, hk, hc, hs⟩ := object_loop_ledger_initial (GF := GF) cfg lim (d + 1) types[36]! rfl inst mi A n g ta hm
    (by omega) Cg gt sp out de ptr idx out out out out ob bs i live Cd baseHL baseF ptrS sl K646 K169 K81
    hob hout hlen hptr hde hsp hal hi hsetup hkeys hkeysSaved hvalues hignored hignoredSaved N a rF hb0 hloop
  refine ⟨keys, hw, hk, hc, ?_⟩
  iintro ⟨#HC, #HI, #F228, #Hi⟩
  ihave #S := hs $$ [HC HI]
  · iframe HC HI
  iapply f78_of_object_spec cfg lim d type htype inst mi A n g ta hm (by omega)
  iframe S F228 Hi

theorem f78_ledger_initial_cost (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 43 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp out de ptr idx : UInt32) (ob bs : List UInt8) (i : Nat)
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
          member n 2048 ta (A 578) idx de live (Ledger bs baseHL baseF false) (Ledger bs baseHL baseF true) (bs.length - rF.length) (some (a, p, cap)) ∗
          rd n de ptr bs (bs.length - rF.length))) := by
  have hs := SerdeIgnObject.object_loop_v86_closing (GF := GF) cfg lim (d + 1) types[36]! rfl inst mi A n g ta hm
    (by omega) Cg gt sp out de ptr idx out out out out ob bs i live Cd
    (Ledger bs baseHL baseF false) (Ledger bs baseHL baseF true) K646 K169 K81
    hob hout hlen hptr hde hsp hal hi
    (Ledger.key_conditions cfg bs baseHL baseF false K646 hkeys)
    (Ledger.key_conditions cfg bs baseHL baseF true K646 hkeysSaved)
    (Ledger.value_conditions cfg bs baseHL baseF K169 hsetup.2 hvalues)
    (Ledger.closing bs baseHL baseF false) (Ledger.closing bs baseHL baseF true)
    (Ledger.ignore_conditions cfg bs baseHL baseF false K81 hlen hsetup.1 hignored)
    (Ledger.ignore_conditions cfg bs baseHL baseF true K81 hlen hsetup.1 hignoredSaved)
    N a rF hb0 hloop
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
    iintro H
    iexact H


end Resource
end WNear.Binary.SerdeObjectMixedTrace
