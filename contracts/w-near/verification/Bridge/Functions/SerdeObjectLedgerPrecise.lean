import Bridge.Functions.SerdeObjectClosingPrecise
import Bridge.Functions.SerdeObjectLedgerRoom
import Bridge.Functions.SerdeObjectLedgerWrapper

set_option maxRecDepth 100000

namespace WNear.Binary.SerdeObjectMixedTrace
open Wasm Wasm.Near WNear.Binary
open WNear.Binary.SerdeStructObjKeyState (Bounds)
open WNear.Binary.ParseStrSuccess (appendChunks)
open WNear.Binary.ScratchMixedTrace
def PreciseKeyGasCharges (cfg : WasmConfig) (bs : List UInt8) (B : WNear.Binary.SerdeStructObjKeyState.Bounds) (K : Nat → Nat) : Prop :=
  ∀ (first : Bool) (i q : Nat) (key : String) (rest : List UInt8) (hl F : Nat) (cap : UInt32),
    i ≤ bs.length → SerdeNextKey.keyQ first bs i = some q →
    NearInterface.Json.stringBody (bs.drop q) [] = some (some key, rest) → B i hl F cap → cap.toNat < 2 ^ 25 → hl % 65536 = 0 → 0 < hl →
    SerdeKeyReuse.preciseCost cfg F cap bs key.toUTF8.toList rest q ≤ K q



theorem Ledger.precise_key_conditions (cfg : WasmConfig) (bs : List UInt8) (baseHL baseF : Nat) (saved : Bool)
    (K : Nat → Nat) (hlen : bs.length ≤ 4194304) (hbase : baseHL + 18230154 ≤ 100663296)
    (hgas : PreciseKeyGasCharges cfg bs (Ledger bs baseHL baseF saved) K) :
    SerdeStructObjKeyState.PreciseKeyConditions cfg 2048 bs (Ledger bs baseHL baseF saved) K := by
  intro first i q key rest hl F cap hi hq hs hb hcap halign hpositive
  refine ⟨Ledger.key_room bs baseHL baseF i hl F q saved cap key rest hlen hbase hb halign hpositive hs,
    hgas first i q key rest hl F cap hi hq hs hb hcap halign hpositive, ?_⟩
  intro hl' hlo hhi
  exact Ledger.segment bs baseHL baseF i (bs.length - rest.length) hl F hl' saved saved cap
    (.append (appendChunks (bs.drop q) [])) 0 (by omega) (.string q key rest hs) hb hlo
    (by simpa only [Segment.pages, Nat.add_zero, Nat.mul_comm] using hhi)

end WNear.Binary.SerdeObjectMixedTrace
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
set_option maxRecDepth 100000 in
theorem f78_ledger_precise_cost (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 43 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp out de ptr idx : UInt32) (ob bs : List UInt8) (i : Nat)
    (live : List (Nat × Nat)) (Cd : IProp GF) [Persistent Cd] (baseHL baseF : Nat) (ptrS sl : UInt32) (K646 K169 K81 : Nat → Nat)
    (hob : ob.length = 16) (hout : out.toNat + 16 ≤ 2 ^ 32) (hlen : bs.length ≤ 4194304)
    (hptr : ptr.toNat + bs.length < 2 ^ 32) (hde : de.toNat + 25 ≤ 2 ^ 32)
    (hsp : 368 ≤ sp.toNat) (hal : sp.toNat % 8 = 0) (hi : i ≤ bs.length)
    (hsetup : LedgerSetup baseHL baseF)
    (hkeys : PreciseKeyGasCharges cfg bs (Ledger bs baseHL baseF false) K646) (hkeysSaved : PreciseKeyGasCharges cfg bs (Ledger bs baseHL baseF true) K646)
    (hvalues : ValueGasCharges cfg bs (Ledger bs baseHL baseF false) K169)
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
  have hs := SerdeIgnObject.object_loop_v86_closing_precise (GF := GF) cfg lim (d + 1) types[36]! rfl inst mi A n g ta hm
    (by omega) Cg gt sp out de ptr idx out out out out ob bs i live Cd
    (Ledger bs baseHL baseF false) (Ledger bs baseHL baseF true) K646 K169 K81
    hob hout hlen hptr hde hsp hal hi
    (Ledger.precise_key_conditions cfg bs baseHL baseF false K646 hlen hsetup.1 hkeys)
    (Ledger.precise_key_conditions cfg bs baseHL baseF true K646 hlen hsetup.1 hkeysSaved)
    (Ledger.value_conditions cfg bs baseHL baseF K169 hsetup.2
      (Ledger.value_charges cfg bs baseHL baseF K169 hlen hsetup.1 hvalues))
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
namespace WNear.Binary.SerdeObjectMixedTrace
open Wasm Wasm.Near WNear.Binary

theorem precise_gas_of_legacy (cfg : WasmConfig) (bs : List UInt8) (B : WNear.Binary.SerdeStructObjKeyState.Bounds) (K : Nat → Nat)
    (hlen : bs.length < 2 ^ 24) (hc : KeyGasCharges cfg bs B K) :
    PreciseKeyGasCharges cfg bs B K := by
  intro first i q key rest hl F cap hi hq hm hb hcap hal hp
  exact (SerdeKeyReuse.preciseCost_le_keyCost cfg F cap bs q key rest hlen hcap hm).trans
    (hc first i q key rest hl F cap hi hq hm hb hcap hal hp)

end WNear.Binary.SerdeObjectMixedTrace
