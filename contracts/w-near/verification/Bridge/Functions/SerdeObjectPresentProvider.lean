import Bridge.Functions.BalanceOf297PresentParser

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
open WNear.Binary.LookupMapOps (HeapRoomK)
section Resource
variable {GF : BundledGFunctors} [WasmGS NearState GF]
theorem ledger_result_room_present (n hl F : Nat) (live : List (Nat × Nat)) (out p c L : UInt32)
    (a : WNear.AccountId)
    (hsetup : LedgerSetup hl F) :
    n ↦[i32][ out.toNat ] 0 ∗ n ↦[i32][ out.toNat + 4 ] p ∗ n ↦[i32][ out.toNat + 8 ] c ∗
      n ↦[i32][ out.toNat + 12 ] L ∗ cleanLedgerObject (GF := GF) n hl F live a.val.toUTF8.toList p c L ⊢
    ∃ hl', ⌜HeapRoomK 7 hl' 2048⌝ ∗ BalanceOf297AbsentCall.okAtFixed n out a live hl' (F + 43) := by
  have hvalid := a.toNear.property
  change validAccountIdBytes a.val.toUTF8.toList = true at hvalid
  simp only [validAccountIdBytes, Bool.and_eq_true, decide_eq_true_eq] at hvalid
  have hsize := Wasm.ByteEncoding.string_utf8_length a.val
  have hm : (UInt32.ofNat a.val.toUTF8.toList.length).toNat = a.val.toUTF8.toList.length := by
    change a.val.toUTF8.toList.length % 2 ^ 32 = a.val.toUTF8.toList.length
    exact Nat.mod_eq_of_lt (by omega)
  iintro ⟨O0, O4, O8, O12, Hclean⟩
  iunfold cleanLedgerObject at Hclean
  icases Hclean with ⟨%⟨hc, hL, hp⟩, Hb, %hl', %⟨hlow, hhigh⟩, Hheap⟩
  subst hc hL
  iunfold heapInv at Hheap
  icases Hheap with ⟨%M, %⟨hw, hml⟩, Hhead, Hlen, Hlimit, Hcells⟩
  have hal : hl' % 65536 = 0 := hml ▸ hw.len_al
  have hpos : 0 < hl' := by have := hw.mem0_pos; have := hw.mem0_le; omega
  have hr : LookupMapOps.HeapRoomK 7 hl' 2048 := by
    have hb := hsetup.1
    exact ⟨hal, hpos, by omega, by omega⟩
  ihave Hheap : heapInv n 2048 hl' ((p.toNat, (UInt32.ofNat a.val.toUTF8.toList.length).toNat) :: live) (F + 43)
      $$ [Hhead Hlen Hlimit Hcells]
  · iunfold heapInv
    iexists M
    iframe Hhead Hlen Hlimit Hcells
    ipureintro; exact ⟨hw, hml⟩
  iexists hl'
  isplitr
  · ipureintro; exact hr
  iunfold BalanceOf297AbsentCall.okAtFixed
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


theorem f65_ledger_room_present (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 45 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp out ptr idx : UInt32) (ob bs : List UInt8) (a : WNear.AccountId)
    (rest : List UInt8) (N k : Nat) (mlen F : Nat) (live : List (Nat × Nat))
    (hob : ob.length = 16) (hout : out.toNat + 16 ≤ 2 ^ 32)
    (hlen : bs.length ≤ 4194304) (hptr : ptr.toNat + bs.length < 2 ^ 32) (hsp : 448 ≤ sp.toNat)
    (hal : sp.toNat % 8 = 0) (K646 K169 K81 : Nat → Nat)
    (hsetup : LedgerSetup mlen F)
    (hkeys : KeyRoomCharges cfg 2048 bs (Ledger bs mlen F false) K646)
    (hkeysSaved : KeyRoomCharges cfg 2048 bs (Ledger bs mlen F true) K646)
    (hvalues : ValueRoomCharges cfg 2048 bs (Ledger bs mlen F false) K169)
    (hignored : IgnoreCharges cfg bs K81 (Ledger bs mlen F false))
    (hignoredSaved : IgnoreCharges cfg bs K81 (Ledger bs mlen F true))
    (ho : bs[wsLen bs]? = some 0x7B)
    (hloop : objLoop "account_id" (valueAs WNear.account) SerdeIgnObject.ignored N none
      (bs.drop (wsLen bs + 1)) = some (some a, rest))
    (hk : k = bs.length - rest.length) (hend : k + wsLen (bs.drop k) = bs.length) :
    code66 n 2048 inst mi A ∗ SerdeAccountId.code169 n 2048 inst mi A ∗
      ParseStr.code646 n 2048 inst mi A ∗ DropVec.dropCode inst mi A ∗ SerdeIgnMember.code n 2048 inst mi A ∗
      A 644 ↪[wf] FuncInst.wasm types[31]! inst f644 ∗ A 66 ↪[wf] FuncInst.wasm types[14]! inst f66 ∗
      inst ↪[inst] mi ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f65 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 ptr, .i32 (UInt32.ofNat bs.length)]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          stk n (sp.toNat - 448) 448 ∗ vt n 1057464 idx ta (A 578) ∗ heapInv n 2048 mlen live F ∗
          n ↦[wms][ out.toNat ] ob ∗ n ↦[wms][ ptr.toNat ] bs ∗
          n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width ∗
          n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗
    n ↦[wms][ 1051092 ] WNear.BalanceOfArgs.keyBytes ∗ n ↦[wms][ 1048576 ] SerdeIdent.identBytes))
        (fun _ => 45 * cfg.regularOpCost + ((975 + 96 * wsLen (bs.drop k)) * cfg.regularOpCost +
          SerdeStructObj.costObj cfg (K646) (K169) (K81) (valueAs WNear.account) SerdeIgnObject.ignored bs N 0))
        (fun _ rs => iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 448) 448 ∗
          vt n 1057464 idx ta (A 578) ∗ n ↦[wms][ ptr.toNat ] bs ∗
          n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width ∗
          n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗
    n ↦[wms][ 1051092 ] WNear.BalanceOfArgs.keyBytes ∗ n ↦[wms][ 1048576 ] SerdeIdent.identBytes ∗ ∃ hl', ⌜LookupMapOps.HeapRoomK 7 hl' 2048⌝ ∗
          BalanceOf297AbsentCall.okAtFixed n out a live hl' (F + 43))) := by
  apply (f65_ledger_object cfg lim d type htype inst mi A n g ta hm hd Cg gt
    sp out ptr idx ob bs a rest N k mlen F live hob hout hlen hptr hsp hal K646 K169 K81
    hsetup hkeys hkeysSaved hvalues hignored hignoredSaved ho hloop hk hend).trans
  apply ParseStrSuccess.spec_post
  intro args rs
  iintro ⟨%hrs, Hg, Hs, Hvt, Hbs, He, Hw, Hhex, Hkey, Hident, %p, %cap, %len, O0, O4, O8, O12, Hclean⟩
  iframe Hg Hs Hvt Hbs He Hw Hhex Hkey Hident
  isplitr
  · ipureintro; exact hrs
  iapply ledger_result_room_present n mlen F live out p cap len a hsetup
  iframe O0 O4 O8 O12 Hclean

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
theorem ledger_parser_contract_present (cfg : WasmConfig) (lim : ExecLimits) (d inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta Cg : Nat) (hm : IfaceMod mi A n g ta) (gt : GlobalType)
    (sp out ptr idx : UInt32) (ob bs rest : List UInt8) (a : WNear.AccountId) (N mlen F : Nat)
    (live : List (Nat × Nat)) (hd : d + 45 < lim.maxCallDepth)
    (hob : ob.length = 16) (hout : out.toNat + 16 ≤ 2 ^ 32) (hlen : bs.length ≤ 4194304)
    (hptr : ptr.toNat + bs.length < 2 ^ 32) (hsp : 448 ≤ sp.toNat) (hal : sp.toNat % 8 = 0)
    (K646 K169 K81 : Nat → Nat)
    (hsetup : LedgerSetup mlen F)
    (hkeys : KeyRoomCharges cfg 2048 bs (Ledger bs mlen F false) K646)
    (hkeysSaved : KeyRoomCharges cfg 2048 bs (Ledger bs mlen F true) K646)
    (hvalues : ValueRoomCharges cfg 2048 bs (Ledger bs mlen F false) K169)
    (hignored : IgnoreCharges cfg bs K81 (Ledger bs mlen F false))
    (hignoredSaved : IgnoreCharges cfg bs K81 (Ledger bs mlen F true))
    (ho : bs[wsLen bs]? = some 0x7B)
    (hloop : objLoop "account_id" (valueAs WNear.account) SerdeIgnObject.ignored N none
      (bs.drop (wsLen bs + 1)) = some (some a, rest))
    (hend : bs.length - rest.length + wsLen (bs.drop (bs.length - rest.length)) = bs.length) :
    BalanceOf297PresentCall.PresentParserCallContract (GF := GF) cfg lim d inst mi A n g ta Cg gt sp out ptr idx
      ob bs a mlen live F (ledgerParserCost cfg K646 K169 K81 bs rest N) (F + 43)
      (ledgerParserCode n inst mi A) (ledgerParserStatics n) := by
  unfold BalanceOf297PresentCall.PresentParserCallContract
  have hs := f65_ledger_room_present (GF := GF) cfg lim d types[31]! rfl inst mi A n g ta hm hd Cg gt
    sp out ptr idx ob bs a rest N (bs.length - rest.length) mlen F live hob hout hlen hptr hsp hal K646 K169 K81 hsetup hkeys hkeysSaved hvalues hignored hignoredSaved ho hloop rfl hend
  unfold ledgerParserCode
  simp only [ledgerParserCost, Nat.add_assoc]
  apply hs.trans
  apply SerdeValueState.spec_repack
  · intro args
    iintro ⟨%ha, Hg, Hs, Hvt, Hheap, Ho, Hbs, He, Hw, Hhex, HFr⟩
    iunfold ledgerParserStatics at HFr
    icases HFr with ⟨Hkey, Hident⟩
    iframe Hg Hs Hvt Hheap Ho Hbs He Hw Hhex Hkey Hident
    ipureintro; exact ha
  · intro args rs
    iintro ⟨%hrs, Hg, Hs, Hvt, Hbs, He, Hw, Hhex, Hkey, Hident, Hresult⟩
    iunfold ledgerParserStatics
    iframe Hg Hs Hvt Hbs He Hw Hhex Hkey Hident Hresult
    ipureintro; exact hrs

end Resource
end WNear.Binary.SerdeObjectMixedTrace
