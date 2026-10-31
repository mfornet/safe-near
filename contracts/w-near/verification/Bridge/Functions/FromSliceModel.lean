import Bridge.Functions.SerdeFromTraitModel
import Bridge.Functions.FromSliceSpec

/-! Successful account-id array parsing for both borrowed and copied strings. -/
namespace WNear.Binary.FromSliceModel

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_addr roomFor)
open WNear.Binary.ArgsLeaves (sliceRead)
open WNear.Binary.SerdeRead (wsLen)
open WNear.Binary.ParseStr (borrowed roomRun)
open WNear.Binary.ParseStrSuccess (appendChunks)
open WNear.Binary.ScratchGrow (growthPages)
open WNear.Binary.SerdeFromTrait (code66)
open WNear.Binary.SerdeStruct78Model (costArray)
open WNear.Binary.SerdeScratchValueDrop (cleanValue)

section Proof
variable {GF : BundledGFunctors} [WasmGS NearState GF]
set_option maxRecDepth 100000 in
/-- The 65 entry accepts the escaped array, restores all 448 bytes and returns only the owned String. -/
theorem f65_arr_model (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 38 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp out ptr idx : UInt32) (ob bs : List UInt8) (value : String)
    (rest : List UInt8) (j k : Nat) (maxP mlen F : Nat) (live : List (Nat × Nat))
    (hob : ob.length = 16) (hout : out.toNat + 16 ≤ 2 ^ 32)
    (hlen : bs.length < 2 ^ 24) (hptr : ptr.toNat + bs.length < 2 ^ 32) (hsp : 448 ≤ sp.toNat)
    (ho : bs[wsLen bs]? = some 0x5B)
    (hj : j = wsLen bs + 1 + wsLen (bs.drop (wsLen bs + 1))) (hq : bs[j]? = some 0x22)
    (he : bs[bs.length - rest.length + wsLen (bs.drop (bs.length - rest.length))]? = some 0x5D)
    (hk : k = bs.length - rest.length + wsLen (bs.drop (bs.length - rest.length)) + 1)
    (hend : k + wsLen (bs.drop k) = bs.length)
    (hmodel : NearInterface.Json.stringBody (bs.drop (j + 1)) [] = some (some value, rest))
    (hr : SerdeErrBox.roomFor4 mlen maxP 20) (hroom : roomRun maxP mlen 0 [] (bs.drop (j + 1)))
    (hvalid : validAccountIdBytes value.toUTF8.toList = true)
    (halloc : roomFor (mlen + growthPages 0 0 (appendChunks (bs.drop (j + 1)) []) * 65536)
      maxP (UInt32.ofNat value.toUTF8.toList.length)) :
    code66 n maxP inst mi A ∗ SerdeAccountId.code169 n maxP inst mi A ∗
      ParseStr.code646 n maxP inst mi A ∗ DropVec.dropCode inst mi A ∗
      A 644 ↪[wf] FuncInst.wasm types[31]! inst f644 ∗ A 66 ↪[wf] FuncInst.wasm types[14]! inst f66 ∗
      inst ↪[inst] mi ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f65 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 ptr, .i32 (UInt32.ofNat bs.length)]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          stk n (sp.toNat - 448) 448 ∗ vt n 1057464 idx ta (A 578) ∗ heapInv n maxP mlen live F ∗
          n ↦[wms][ out.toNat ] ob ∗ n ↦[wms][ ptr.toNat ] bs ∗
          n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width ∗
          n ↦[wms][ 1062712 ] SerdeEsc.hexTable))
        (fun _ => 45 * cfg.regularOpCost + ((700 + 96 * wsLen (bs.drop k)) * cfg.regularOpCost +
          costArray cfg F 0 bs value.toUTF8.toList rest j))
        (fun _ rs => iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 448) 448 ∗
          vt n 1057464 idx ta (A 578) ∗ n ↦[wms][ ptr.toNat ] bs ∗
          n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width ∗
          n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗ ∃ (p c len : UInt32),
          n ↦[i32][ out.toNat ] 0 ∗ n ↦[i32][ out.toNat + 4 ] p ∗ n ↦[i32][ out.toNat + 8 ] c ∗
          n ↦[i32][ out.toNat + 12 ] len ∗ cleanValue n maxP mlen live F 0 bs value.toUTF8.toList (j + 1) p c len)) := by
  have hlt := sp.toNat_lt
  have h16 : (sp - 16).toNat = sp.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  let P : IProp GF := iprop(stk n (sp.toNat - 448) 432 ∗ vt n 1057464 idx ta (A 578) ∗
    heapInv n maxP mlen live F ∗ n ↦[wms][ out.toNat ] ob ∗ n ↦[wms][ ptr.toNat ] bs ∗
    n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width ∗
    n ↦[wms][ 1062712 ] SerdeEsc.hexTable)
  let Q : List Value → IProp GF := fun _ => iprop(stk n (sp.toNat - 448) 432 ∗ vt n 1057464 idx ta (A 578) ∗
    n ↦[wms][ ptr.toNat ] bs ∗ n ↦[wms][ 1062392 ] ParseStr.escTable ∗
    n ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width ∗ n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗
    ∃ (p c len : UInt32), n ↦[i32][ out.toNat ] 0 ∗ n ↦[i32][ out.toNat + 4 ] p ∗
      n ↦[i32][ out.toNat + 8 ] c ∗ n ↦[i32][ out.toNat + 12 ] len ∗
      cleanValue n maxP mlen live F 0 bs value.toUTF8.toList (j + 1) p c len)
  let K := (700 + 96 * wsLen (bs.drop k)) * cfg.regularOpCost + costArray cfg F 0 bs value.toUTF8.toList rest j
  have hs := SerdeFromTraitModel.f66_arr_model (GF := GF) cfg lim (d + 1) types[14]! rfl inst mi A n g ta hm
    (by omega) Cg gt (sp - 16) out (sp - 16) ptr idx ob bs value rest j k maxP mlen F live hob hout
    (by omega) hlen hptr (by omega) ho hj hq he hk hend hmodel hr hroom hvalid halloc
  rw [show (sp - 16).toNat - 432 = sp.toNat - 448 by omega] at hs
  have hs' : code66 n maxP inst mi A ∗ SerdeAccountId.code169 n maxP inst mi A ∗
      ParseStr.code646 n maxP inst mi A ∗ DropVec.dropCode inst mi A ⊢
      MFunSpec cfg lim (d + 1) types[14]! inst mi f66 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 (sp - 16)]⌝ ∗ g ↦[wg] ⟨gt, .i32 (sp - 16)⟩ ∗
          sliceRead n (sp - 16) ptr (UInt32.ofNat bs.length) 0 ∗ P))
        (fun _ => K)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 (sp - 16)⟩ ∗
          (∃ a b c : UInt32, sliceRead n (sp - 16) a b c) ∗ Q rs)) := by
    apply hs.trans
    apply SerdeValueState.spec_repack
    · intro args
      dsimp only [P]
      iintro ⟨%ha, Hg, Hrd, Hs, Hvt, Hheap, Ho, Hbs, He, Hw, Hhex⟩
      iframe Hg Hs Hvt Hheap Ho Hrd Hbs He Hw Hhex
      ipureintro; exact ha
    · intro args rs
      dsimp only [Q]
      iintro ⟨%hrs, Hg, Hs, Hvt, Hrd, Hbs, He, Hw, Hhex, Hresult⟩
      iframe Hg Hs Hvt Hbs He Hw Hhex Hresult
      isplitr
      · ipureintro; exact hrs
      iexists ptr, UInt32.ofNat bs.length, 0
      iexact Hrd
  have key := ArgsLeaves.f65_of_66 (GF := GF) cfg lim d type htype inst mi n g hm.mem hm.glob (A 66) (A 644)
    (hm.funcs 66 (by decide)) (hm.funcs 644 (by decide)) (by omega) Cg gt sp out ptr (UInt32.ofNat bs.length)
    (by omega) P K Q
  iintro ⟨#H66, #HC, #HP, #HD, #F644, #F66, #Hi⟩
  ihave #S66 := hs' $$ [H66 HC HP HD]
  · iframe H66 HC HP HD
  ihave #S65 := key $$ [F644 F66 Hi S66]
  · iframe F644 F66 Hi S66
  iapply SerdeValueState.spec_repack ?hPre ?hPost $$ S65
  case hPre =>
    intro args
    dsimp only [P]
    iintro ⟨%ha, Hg, Hs, Hvt, Hheap, Ho, Hbs, He, Hw, Hhex⟩
    icases stk_split n (sp.toNat - 448) 432 16 $$ Hs with ⟨Hs, Hs16⟩
    ihave Hs16 := stk_addr (show sp.toNat - 448 + 432 = sp.toNat - 16 by omega) $$ Hs16
    iframe Hg Hs16 Hs Hvt Hheap Ho Hbs He Hw Hhex
    ipureintro; exact ha
  case hPost =>
    intro args rs
    dsimp only [Q]
    iintro ⟨%hrs, Hg, Hs16, Hs, Hvt, Hbs, He, Hw, Hhex, Hresult⟩
    iframe Hg Hvt Hbs He Hw Hhex Hresult
    isplitr
    · ipureintro; exact hrs
    ihave Hs16 := stk_addr (show sp.toNat - 16 = sp.toNat - 448 + 432 by omega) $$ Hs16
    iapply stk_join n (sp.toNat - 448) 432 16
    iframe Hs Hs16
theorem f65_arr_model_bound (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 38 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp out ptr idx : UInt32) (ob bs : List UInt8) (value : String)
    (rest : List UInt8) (j k : Nat) (maxP mlen F : Nat) (live : List (Nat × Nat))
    (hob : ob.length = 16) (hout : out.toNat + 16 ≤ 2 ^ 32)
    (hlen : bs.length < 2 ^ 24) (hptr : ptr.toNat + bs.length < 2 ^ 32) (hsp : 448 ≤ sp.toNat)
    (ho : bs[wsLen bs]? = some 0x5B)
    (hj : j = wsLen bs + 1 + wsLen (bs.drop (wsLen bs + 1))) (hq : bs[j]? = some 0x22)
    (he : bs[bs.length - rest.length + wsLen (bs.drop (bs.length - rest.length))]? = some 0x5D)
    (hk : k = bs.length - rest.length + wsLen (bs.drop (bs.length - rest.length)) + 1)
    (hend : k + wsLen (bs.drop k) = bs.length)
    (hmodel : NearInterface.Json.stringBody (bs.drop (j + 1)) [] = some (some value, rest))
    (hr : SerdeErrBox.roomFor4 mlen maxP 20) (hroom : roomRun maxP mlen 0 [] (bs.drop (j + 1)))
    (hvalid : validAccountIdBytes value.toUTF8.toList = true)
    (halloc : roomFor (mlen + growthPages 0 0 (appendChunks (bs.drop (j + 1)) []) * 65536)
      maxP (UInt32.ofNat value.toUTF8.toList.length)) :
    code66 n maxP inst mi A ∗ SerdeAccountId.code169 n maxP inst mi A ∗
      ParseStr.code646 n maxP inst mi A ∗ DropVec.dropCode inst mi A ∗
      A 644 ↪[wf] FuncInst.wasm types[31]! inst f644 ∗ A 66 ↪[wf] FuncInst.wasm types[14]! inst f66 ∗
      inst ↪[inst] mi ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f65 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 ptr, .i32 (UInt32.ofNat bs.length)]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          stk n (sp.toNat - 448) 448 ∗ vt n 1057464 idx ta (A 578) ∗ heapInv n maxP mlen live F ∗
          n ↦[wms][ out.toNat ] ob ∗ n ↦[wms][ ptr.toNat ] bs ∗
          n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width ∗
          n ↦[wms][ 1062712 ] SerdeEsc.hexTable))
        (fun _ => 45 * cfg.regularOpCost + ((700 + 96 * wsLen (bs.drop k)) * cfg.regularOpCost +
          SerdeStruct78Esc.costArray cfg F 0 bs value.toUTF8.toList rest j))
        (fun _ rs => iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 448) 448 ∗
          vt n 1057464 idx ta (A 578) ∗ n ↦[wms][ ptr.toNat ] bs ∗
          n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width ∗
          n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗ ∃ (p c len : UInt32),
          n ↦[i32][ out.toNat ] 0 ∗ n ↦[i32][ out.toNat + 4 ] p ∗ n ↦[i32][ out.toNat + 8 ] c ∗
          n ↦[i32][ out.toNat + 12 ] len ∗ cleanValue n maxP mlen live F 0 bs value.toUTF8.toList (j + 1) p c len)) := by
  apply (f65_arr_model cfg lim d type htype inst mi A n g ta hm hd Cg gt sp out ptr idx ob bs value rest j k
    maxP mlen F live hob hout hlen hptr hsp ho hj hq he hk hend hmodel hr hroom hvalid halloc).trans
  apply AllocGen.MFunSpec_cost
  intro args
  have hb := SerdeStruct78Model.costArray_le cfg F 0 bs value rest j hq hmodel
  omega

end Proof
end WNear.Binary.FromSliceModel
