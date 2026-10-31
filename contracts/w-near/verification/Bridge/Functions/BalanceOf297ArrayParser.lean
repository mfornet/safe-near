import Bridge.Functions.BalanceOf297CopiedRoom
import Bridge.Functions.FromSliceModel

/-! Array parser resources for either successful string path. -/
namespace WNear.Binary.BalanceOf297AbsentCall
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
theorem f65_arr_model_room (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
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
    (hroom6 : HeapRoomK (copiedParserPages bs (j + 1) a + 6) mlen 2048) :
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
          ∃ hl', ⌜HeapRoomK 6 hl' 2048⌝ ∗ okAtFixed n out a live hl' (copiedParserFree bs (j + 1) F))) := by
  have hErr : SerdeErrBox.roomFor4 mlen 2048 20 := by
    have h20 : (AllocNewCell.cellPages (AllocAlloc.wordsOf 20) 4).toNat = 1 := by decide +kernel
    obtain ⟨ha, hp, hm, hb⟩ := hroom6
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
  iapply copied_result_room n mlen F live out p c len bs (j + 1) a hroom6
  iframe O0 O4 O8 O12 Hclean


end Spec
end WNear.Binary.BalanceOf297AbsentCall
