import Bridge.Methods.FtBalanceOfPresentObject

namespace WNear.Binary.BalanceOf297PresentCall
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open WNear.Binary.AllocInv (heapInv block)
open WNear.Binary.LookupMapOps (HeapRoomK)
open WNear.Binary.ParseStrSuccess (appendChunks)
open WNear.Binary.ScratchGrow (endFreeBound growthPages)
open WNear.Binary.SerdeScratchValueDrop (cleanValue)
open WNear.Binary.BalanceOf297AbsentCall (copiedParserPages copiedParserFree heap_alignment okAtFixed)
section Spec
variable {GF : BundledGFunctors} [WasmGS NearState GF]
/-- Parser growth plus six reserved pages gives the exact result heap the required balance room. -/
theorem copied_result_room_present (n hl F : Nat) (live : List (Nat × Nat)) (out p c L : UInt32)
    (bs : List UInt8) (q : Nat) (a : WNear.AccountId)
    (hroom : HeapRoomK (copiedParserPages bs q a + 7) hl 2048) :
    n ↦[i32][ out.toNat ] 0 ∗ n ↦[i32][ out.toNat + 4 ] p ∗ n ↦[i32][ out.toNat + 8 ] c ∗
      n ↦[i32][ out.toNat + 12 ] L ∗ cleanValue (GF := GF) n 2048 hl live F 0 bs
        a.val.toUTF8.toList q p c L ⊢
    ∃ hl', ⌜HeapRoomK 7 hl' 2048⌝ ∗ okAtFixed n out a live hl' (copiedParserFree bs q F) := by
  have hvalid := a.toNear.property
  change validAccountIdBytes a.val.toUTF8.toList = true at hvalid
  simp only [validAccountIdBytes, Bool.and_eq_true, decide_eq_true_eq] at hvalid
  have hsize := Wasm.ByteEncoding.string_utf8_length a.val
  have hm : (UInt32.ofNat a.val.toUTF8.toList.length).toNat = a.val.toUTF8.toList.length := by
    change a.val.toUTF8.toList.length % 2 ^ 32 = a.val.toUTF8.toList.length
    exact Nat.mod_eq_of_lt (by omega)
  iintro ⟨O0, O4, O8, O12, Hclean⟩
  iunfold cleanValue at Hclean
  icases Hclean with ⟨%⟨hc, hL, hp⟩, Hb, %hl', %F', %⟨hlow, hhigh, hF⟩, Hheap⟩
  subst hc hL F'
  ihave Hheap := heap_alignment n 2048 hl' _ _ $$ Hheap
  icases Hheap with ⟨%hal, Hheap⟩
  have hr : HeapRoomK 7 hl' 2048 := by
    obtain ⟨ha, hp0, hmax, h32⟩ := hroom
    unfold HeapRoomK at *
    unfold copiedParserPages at hmax h32
    refine ⟨hal, by omega, by omega, by omega⟩
  iexists hl'
  isplitr
  · ipureintro; exact hr
  iunfold okAtFixed
  rw [← hsize]
  iexists p, UInt32.ofNat a.val.toUTF8.toList.length
  isplitr
  · ipureintro; exact ⟨hp, by rw [hm]⟩
  unfold copiedParserFree
  iframe O0 O4 O8 O12 Hb Hheap
  rw [hm, Nat.sub_self]
  iunfold block
  iexists ([] : List UInt8)
  isplitr
  · ipureintro; rfl
  iapply ScratchGrow.memBytes_nil
end Spec
end WNear.Binary.BalanceOf297PresentCall

/-! Array parser resources for either successful string path. -/
namespace WNear.Binary.BalanceOf297PresentCall
open WNear.Binary.BalanceOf297AbsentCall (copiedParserPages copiedParserFree okAtFixed)
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.VecFromElem (stk roomFor)
open WNear.Binary.SerdeRead (wsLen)
open WNear.Binary.ParseStr (borrowed roomRun)
open WNear.Binary.ParseStrSuccess (appendChunks)
open WNear.Binary.ScratchGrow (growthPages)
open WNear.Binary.SerdeFromTrait (code66)
open WNear.Binary.SerdeStruct78Esc (costArray)
open WNear.Binary.LookupMapOps (HeapRoomK)
open WNear.Binary.FromSliceModel (f65_arr_model_bound)
section Spec
variable {GF : BundledGFunctors} [WasmGS NearState GF]
set_option maxRecDepth 100000 in
theorem f65_arr_model_room_present (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 38 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp out ptr idx : UInt32) (ob bs : List UInt8) (a : WNear.AccountId)
    (rest : List UInt8) (j k : Nat) (mlen F : Nat) (live : List (Nat × Nat))
    (hob : ob.length = 16) (hout : out.toNat + 16 ≤ 2 ^ 32)
    (hlen : bs.length < 2 ^ 24) (hptr : ptr.toNat + bs.length < 2 ^ 32) (hsp : 448 ≤ sp.toNat)
    (ho : bs[wsLen bs]? = some 0x5B)
    (hj : j = wsLen bs + 1 + wsLen (bs.drop (wsLen bs + 1))) (hq : bs[j]? = some 0x22)
    (he : bs[bs.length - rest.length + wsLen (bs.drop (bs.length - rest.length))]? = some 0x5D)
    (hk : k = bs.length - rest.length + wsLen (bs.drop (bs.length - rest.length)) + 1)
    (hend : k + wsLen (bs.drop k) = bs.length)
    (hmodel : NearInterface.Json.stringBody (bs.drop (j + 1)) [] = some (some a.val, rest))
    (hroom : roomRun 2048 mlen 0 [] (bs.drop (j + 1)))
    (halloc : roomFor (mlen + growthPages 0 0 (appendChunks (bs.drop (j + 1)) []) * 65536)
      2048 (UInt32.ofNat a.val.toUTF8.toList.length))
    (hroom7 : HeapRoomK (copiedParserPages bs (j + 1) a + 7) mlen 2048) :
    code66 n 2048 inst mi A ∗ SerdeAccountId.code169 n 2048 inst mi A ∗
      ParseStr.code646 n 2048 inst mi A ∗ DropVec.dropCode inst mi A ∗
      A 644 ↪[wf] FuncInst.wasm types[31]! inst f644 ∗ A 66 ↪[wf] FuncInst.wasm types[14]! inst f66 ∗
      inst ↪[inst] mi ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f65 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 ptr, .i32 (UInt32.ofNat bs.length)]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          stk n (sp.toNat - 448) 448 ∗ vt n 1057464 idx ta (A 578) ∗ heapInv n 2048 mlen live F ∗
          n ↦[wms][ out.toNat ] ob ∗ n ↦[wms][ ptr.toNat ] bs ∗
          n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width ∗
          n ↦[wms][ 1062712 ] SerdeEsc.hexTable))
        (fun _ => 45 * cfg.regularOpCost + ((700 + 96 * wsLen (bs.drop k)) * cfg.regularOpCost +
          costArray cfg F 0 bs a.val.toUTF8.toList rest j))
        (fun _ rs => iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 448) 448 ∗
          vt n 1057464 idx ta (A 578) ∗ n ↦[wms][ ptr.toNat ] bs ∗
          n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width ∗
          n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗
          ∃ hl', ⌜HeapRoomK 7 hl' 2048⌝ ∗ okAtFixed n out a live hl' (copiedParserFree bs (j + 1) F))) := by
  have hErr : SerdeErrBox.roomFor4 mlen 2048 20 := by
    have h20 : (AllocNewCell.cellPages (AllocAlloc.wordsOf 20) 4).toNat = 1 := by decide +kernel
    obtain ⟨ha, hp, hm, hb⟩ := hroom7
    unfold SerdeErrBox.roomFor4
    rw [h20]
    exact ⟨ha, hp, by omega, by omega⟩
  apply (f65_arr_model_bound cfg lim d type htype inst mi A n g ta hm hd Cg gt
    sp out ptr idx ob bs a.val rest j k 2048 mlen F live hob hout hlen hptr hsp ho hj hq he hk hend
    hmodel hErr hroom a.toNear.property halloc).trans
  apply ParseStrSuccess.spec_post
  intro args rs
  iintro ⟨%hrs, Hg, Hs, Hvt, Hbs, He, Hw, Hhex, %p, %c, %len, O0, O4, O8, O12, Hclean⟩
  iframe Hg Hs Hvt Hbs He Hw Hhex
  isplitr
  · ipureintro; exact hrs
  iapply copied_result_room_present n mlen F live out p c len bs (j + 1) a hroom7
  iframe O0 O4 O8 O12 Hclean


end Spec
end WNear.Binary.BalanceOf297PresentCall

namespace WNear.Binary.BalanceOf297PresentCall
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary.BalanceOf297AbsentCall (copiedParserPages copiedParserFree okAtFixed)
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.VecFromElem (stk roomFor)
open WNear.Binary.SerdeRead (wsLen)
open WNear.Binary.ParseStr (borrowed roomRun)
open WNear.Binary.ParseStrSuccess (appendChunks)
open WNear.Binary.ScratchGrow (growthPages)
open WNear.Binary.SerdeFromTrait (code66)
open WNear.Binary.SerdeStruct78Esc (costArray)
open WNear.Binary.LookupMapOps (HeapRoomK)
open WNear.Binary.FromSliceModel (f65_arr_model_bound)
section Spec
variable {GF : BundledGFunctors} [WasmGS NearState GF]
set_option maxRecDepth 100000 in
theorem array_present_parser_contract (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 38 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp out ptr idx : UInt32) (ob bs : List UInt8) (a : WNear.AccountId)
    (rest : List UInt8) (j k : Nat) (mlen F : Nat) (live : List (Nat × Nat))
    (hob : ob.length = 16) (hout : out.toNat + 16 ≤ 2 ^ 32)
    (hlen : bs.length < 2 ^ 24) (hptr : ptr.toNat + bs.length < 2 ^ 32) (hsp : 448 ≤ sp.toNat)
    (ho : bs[wsLen bs]? = some 0x5B)
    (hj : j = wsLen bs + 1 + wsLen (bs.drop (wsLen bs + 1))) (hq : bs[j]? = some 0x22)
    (he : bs[bs.length - rest.length + wsLen (bs.drop (bs.length - rest.length))]? = some 0x5D)
    (hk : k = bs.length - rest.length + wsLen (bs.drop (bs.length - rest.length)) + 1)
    (hend : k + wsLen (bs.drop k) = bs.length)
    (hmodel : NearInterface.Json.stringBody (bs.drop (j + 1)) [] = some (some a.val, rest))
    (hroom : roomRun 2048 mlen 0 [] (bs.drop (j + 1)))
    (halloc : roomFor (mlen + growthPages 0 0 (appendChunks (bs.drop (j + 1)) []) * 65536)
      2048 (UInt32.ofNat a.val.toUTF8.toList.length))
    (hroom7 : HeapRoomK (copiedParserPages bs (j + 1) a + 7) mlen 2048) :
    PresentParserCallContract (GF := GF) cfg lim d inst mi A n g ta Cg gt sp out ptr idx ob bs a mlen live F
      (45 * cfg.regularOpCost + ((700 + 96 * wsLen (bs.drop k)) * cfg.regularOpCost +
        costArray cfg F 0 bs a.val.toUTF8.toList rest j)) (copiedParserFree bs (j + 1) F)
      (SerdeObjectNoEsc.parserCode n inst mi A) (SerdeObjectNoEsc.parserStatics n) := by
  unfold PresentParserCallContract
  have hs := f65_arr_model_room_present (GF := GF) cfg lim d types[31]! rfl inst mi A n g ta hm hd Cg gt
    sp out ptr idx ob bs a rest j k mlen F live hob hout hlen hptr hsp ho hj hq he hk hend hmodel hroom halloc hroom7
  iintro #HC
  iunfold SerdeObjectNoEsc.parserCode at HC
  icases HC with ⟨#C66, #C169, #C646, #CDrop, #CIgn, #F644, #F66, #Hi⟩
  ihave #HS := hs $$ [C66 C169 C646 CDrop F644 F66 Hi]
  · iframe C66 C169 C646 CDrop F644 F66 Hi
  iapply (AllocFresh.MFunSpec_frame (Fr := SerdeObjectNoEsc.parserStatics n) ?_ ?_) $$ HS
  · intro args
    iintro ⟨%ha, Hg, Hs, Hvt, Hheap, Ho, Hbs, He, Hw, Hhex, HFr⟩
    iframe Hg Hs Hvt Hheap Ho Hbs He Hw Hhex HFr
    ipureintro; exact ha
  · intro args rs
    iintro ⟨HFr, %hrs, Hg, Hs, Hvt, Hbs, He, Hw, Hhex, Hresult⟩
    iframe Hg Hs Hvt Hbs He Hw Hhex HFr Hresult
    ipureintro; exact hrs

end Spec
end WNear.Binary.BalanceOf297PresentCall

namespace WNear.Binary.BalanceOf297PresentCall
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.SerdeRead (wsLen)
open WNear.Binary.BalanceOf297AbsentCall (copiedParserPages copiedParserFree initial_memory_room
  initial_parser_and_body_room initial_input_and_copy_room room_after_input_pages copied_parser_pages_le)

noncomputable def presentArrayParserGas (cfg : WasmConfig) (bs : List UInt8) (a : WNear.AccountId)
    (rest : List UInt8) (j k : Nat) : Nat :=
  45 * cfg.regularOpCost + ((700 + 96 * wsLen (bs.drop k)) * cfg.regularOpCost +
    SerdeStruct78Esc.costArray cfg 1 0 bs a.val.toUTF8.toList rest j)

section Spec
variable {GF : BundledGFunctors} [WasmGS NearState GF]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
theorem array_present_parser_family (cfg : WasmConfig) (lim : ExecLimits) (inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (gt : GlobalType)
    (bs rest : List UInt8) (a : WNear.AccountId) (j k : Nat)
    (ho : bs[wsLen bs]? = some 0x5B)
    (hj : j = wsLen bs + 1 + wsLen (bs.drop (wsLen bs + 1))) (hq : bs[j]? = some 0x22)
    (he : bs[bs.length - rest.length + wsLen (bs.drop (bs.length - rest.length))]? = some 0x5D)
    (hk : k = bs.length - rest.length + wsLen (bs.drop (bs.length - rest.length)) + 1)
    (hend : k + wsLen (bs.drop k) = bs.length)
    (hmodel : NearInterface.Json.stringBody (bs.drop (j + 1)) [] = some (some a.val, rest)) :
    PresentParserFamily (GF := GF) cfg lim inst mi A n g ta gt bs a 1
      (presentArrayParserGas cfg bs a rest j k) (copiedParserFree bs (j + 1) 1)
      (SerdeObjectNoEsc.parserCode n inst mi A) := by
  intro Cg d sp out ptr idx ob len live hd hob hout hlen hptr hsp hal hL
  have hpos : 0 < bs.length := by have := SerdeNextKey.getElem_lt ho; omega
  have hbase := initial_memory_room bs hlen
  obtain ⟨hr, hroomRun⟩ := initial_parser_and_body_room bs a (j + 1) InitialState.memLen rest hlen hmodel hbase
  obtain ⟨_, halloc⟩ := initial_input_and_copy_room bs a (j + 1) InitialState.memLen hpos hlen hr
  have htail : LookupMapOps.HeapRoomK 131 len 2048 := room_after_input_pages hbase (by
    simpa only [VecFromElem.grownLen] using hL)
  have hpages := copied_parser_pages_le bs a (j + 1) rest hmodel hlen
  have hr7 : LookupMapOps.HeapRoomK (copiedParserPages bs (j + 1) a + 7) len 2048 :=
    ParseStrRoom.heap_room_mono htail (by omega)
  exact array_present_parser_contract cfg lim d inst mi A n g ta hm (by omega) Cg gt sp out ptr idx ob bs a
    rest j k len 1 live hob hout hlen hptr hsp ho hj hq he hk hend hmodel (hroomRun len hL) (halloc len hL) hr7
end Spec

theorem array_present_deployed_provider (cfg : RuntimeConfig) (bs rest : List UInt8) (a : WNear.AccountId)
    (j k : Nat) (ho : bs[wsLen bs]? = some 0x5B)
    (hj : j = wsLen bs + 1 + wsLen (bs.drop (wsLen bs + 1))) (hq : bs[j]? = some 0x22)
    (he : bs[bs.length - rest.length + wsLen (bs.drop (bs.length - rest.length))]? = some 0x5D)
    (hk : k = bs.length - rest.length + wsLen (bs.drop (bs.length - rest.length)) + 1)
    (hend : k + wsLen (bs.drop k) = bs.length)
    (hmodel : NearInterface.Json.stringBody (bs.drop (j + 1)) [] = some (some a.val, rest)) :
    PresentDeployedParserProvider cfg bs a (presentArrayParserGas cfg.wasm bs a rest j k)
      (copiedParserFree bs (j + 1) 1) := by
  intro h _
  apply present_parser_family_mono cfg.wasm execLimits 0 wInst id 0 0 0 InitialState.g0.type
    bs a 1 (presentArrayParserGas cfg.wasm bs a rest j k) (copiedParserFree bs (j + 1) 1)
    (FromSliceSpec.codeCtx cfg h) (SerdeObjectNoEsc.parserCode 0 0 wInst id)
    (SerdeObjectNoEsc.parser_code_of_context cfg h)
  exact array_present_parser_family cfg.wasm execLimits 0 wInst id 0 0 0 Interface.wInst_ifaceMod
    InitialState.g0.type bs rest a j k ho hj hq he hk hend hmodel
end WNear.Binary.BalanceOf297PresentCall
