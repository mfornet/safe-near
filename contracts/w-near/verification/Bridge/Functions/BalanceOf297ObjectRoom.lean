import Bridge.Functions.SerdeObjectParserNoEsc
import Bridge.Functions.BalanceOf297CopiedRoom

/-! Escape-free object refinement: checked parser, linear resources and caller composition.
The completed receipt case is limited explicitly to 4 MiB and shallow ignored values. -/

namespace WNear.Binary.BalanceOf297AbsentCall
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.LookupMapOps (HeapRoomK)
variable {GF : BundledGFunctors} [WasmGS NearState GF]
theorem object_result_room (n hl F : Nat) (live : List (Nat × Nat)) (out p c L : UInt32)
    (a : WNear.AccountId)
    (hroom : HeapRoomK 7 hl 2048) :
    n ↦[i32][ out.toNat ] 0 ∗ n ↦[i32][ out.toNat + 4 ] p ∗ n ↦[i32][ out.toNat + 8 ] c ∗
      n ↦[i32][ out.toNat + 12 ] L ∗ SerdeObjectNoEsc.cleanObject (GF := GF) n 2048 hl live F a.val.toUTF8.toList p c L ⊢
    ∃ hl', ⌜HeapRoomK 6 hl' 2048⌝ ∗ okAtFixed n out a live hl' (max F 1 + 1) := by
  have hvalid := a.toNear.property
  change validAccountIdBytes a.val.toUTF8.toList = true at hvalid
  simp only [validAccountIdBytes, Bool.and_eq_true, decide_eq_true_eq] at hvalid
  have hsize := Wasm.ByteEncoding.string_utf8_length a.val
  have hm : (UInt32.ofNat a.val.toUTF8.toList.length).toNat = a.val.toUTF8.toList.length := by
    change a.val.toUTF8.toList.length % 2 ^ 32 = a.val.toUTF8.toList.length
    exact Nat.mod_eq_of_lt (by omega)
  iintro ⟨O0, O4, O8, O12, Hclean⟩
  iunfold SerdeObjectNoEsc.cleanObject at Hclean
  icases Hclean with ⟨%⟨hc, hL, hp⟩, Hb, %hl', %⟨hlow, hhigh⟩, Hheap⟩
  subst hc hL
  ihave Hheap := heap_alignment n 2048 hl' _ _ $$ Hheap
  icases Hheap with ⟨%hal, Hheap⟩
  have hr : HeapRoomK 6 hl' 2048 := by
    obtain ⟨ha, hp0, hmax, h32⟩ := hroom
    unfold HeapRoomK at *
    refine ⟨hal, by omega, by omega, by omega⟩
  iexists hl'
  isplitr
  · ipureintro; exact hr
  iunfold okAtFixed
  rw [← hsize]
  iexists p, UInt32.ofNat a.val.toUTF8.toList.length
  isplitr
  · ipureintro; exact ⟨hp, by rw [hm]⟩
  iframe O0 O4 O8 O12 Hb Hheap
  rw [hm, Nat.sub_self]
  iunfold block
  iexists ([] : List UInt8)
  isplitr
  · ipureintro; rfl
  iapply ScratchGrow.memBytes_nil

end WNear.Binary.BalanceOf297AbsentCall

namespace WNear.Binary.SerdeObjectNoEsc
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.VecFromElem (stk)
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.SerdeRead (wsLen)
open WNear.Binary.SerdeFromTrait (code66)
open WNear.SerdeStructModel
variable {GF : BundledGFunctors} [WasmGS NearState GF]
theorem f65_obj_room (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 45 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp out ptr idx : UInt32) (ob bs : List UInt8) (a : WNear.AccountId)
    (rest : List UInt8) (N k : Nat) (mlen F : Nat) (live : List (Nat × Nat))
    (hob : ob.length = 16) (hout : out.toNat + 16 ≤ 2 ^ 32)
    (hlen : bs.length < 2 ^ 24) (hptr : ptr.toNat + bs.length < 2 ^ 32) (hsp : 448 ≤ sp.toNat)
    (hal : sp.toNat % 8 = 0) (hnb : (0x5C : UInt8) ∉ bs)
    (hL : mlen = InitialState.memLen ∨ mlen = VecFromElem.grownLen InitialState.memLen (UInt32.ofNat bs.length))
    (ho : bs[wsLen bs]? = some 0x7B)
    (hloop : objLoop "account_id" (valueAs WNear.account) WNear.IgnoreShallow.ign1R N none
      (bs.drop (wsLen bs + 1)) = some (some a, rest))
    (hk : k = bs.length - rest.length) (hend : k + wsLen (bs.drop k) = bs.length) :
    code66 n 2048 inst mi A ∗ SerdeAccountId.code169 n 2048 inst mi A ∗
      ParseStr.code646 n 2048 inst mi A ∗ DropVec.dropCode inst mi A ∗ SerdeIgnValue.code81 inst mi A ∗
      A 644 ↪[wf] FuncInst.wasm types[31]! inst f644 ∗ A 66 ↪[wf] FuncInst.wasm types[14]! inst f66 ∗
      inst ↪[inst] mi ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f65 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 ptr, .i32 (UInt32.ofNat bs.length)]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          stk n (sp.toNat - 448) 448 ∗ vt n 1057464 idx ta (A 578) ∗ heapInv n 2048 mlen live F ∗
          n ↦[wms][ out.toNat ] ob ∗ n ↦[wms][ ptr.toNat ] bs ∗
          n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width ∗
          n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗
    n ↦[wms][ 1051092 ] WNear.BalanceOfArgs.keyBytes ∗ n ↦[wms][ 1048576 ] SerdeIdent.identBytes))
        (fun _ => 45 * cfg.regularOpCost + ((700 + 96 * wsLen (bs.drop k)) * cfg.regularOpCost +
          SerdeStructObj.costObj cfg (SerdeKeyNoEsc.K646 cfg bs) (SerdeAcctHyp.K169 cfg bs F) (SerdeIgnReuse.cost81 cfg bs) (valueAs WNear.account) WNear.IgnoreShallow.ign1R bs N 0))
        (fun _ rs => iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 448) 448 ∗
          vt n 1057464 idx ta (A 578) ∗ n ↦[wms][ ptr.toNat ] bs ∗
          n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width ∗
          n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗
    n ↦[wms][ 1051092 ] WNear.BalanceOfArgs.keyBytes ∗ n ↦[wms][ 1048576 ] SerdeIdent.identBytes ∗ ∃ hl', ⌜LookupMapOps.HeapRoomK 6 hl' 2048⌝ ∗
          BalanceOf297AbsentCall.okAtFixed n out a live hl' (max F 1 + 1))) := by
  apply (f65_obj_model cfg lim d type htype inst mi A n g ta hm hd Cg gt
    sp out ptr idx ob bs a rest N k mlen F live hob hout hlen hptr hsp hal hnb hL ho hloop hk hend).trans
  apply ParseStrSuccess.spec_post
  intro args rs
  iintro ⟨%hrs, Hg, Hs, Hvt, Hbs, He, Hw, Hhex, Hkey, Hident, %p, %cap, %len, O0, O4, O8, O12, Hclean⟩
  iframe Hg Hs Hvt Hbs He Hw Hhex Hkey Hident
  isplitr
  · ipureintro; exact hrs
  iapply BalanceOf297AbsentCall.object_result_room n mlen F live out p cap len a
    (ParseStrRoom.heap_room_mono (initial_room bs mlen hlen hL) (by omega))
  iframe O0 O4 O8 O12 Hclean

end WNear.Binary.SerdeObjectNoEsc
