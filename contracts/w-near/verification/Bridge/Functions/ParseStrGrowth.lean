import Bridge.Functions.ParseStrSuccess
import Bridge.Functions.StrGrowthTrace

/-!
# The complete successful string call, with explicit amortized growth charges

All scan, dispatch, fitting append and UTF-8 work is in the 470-ops-per-byte
allowance. The remaining closed budget includes the changing allocator walk,
old-buffer copies and memory-growth fees. It retains the initial allocator bound
and growth count; it does not assert a uniform gas allowance for arbitrary heaps.
-/

namespace WNear.Binary.ParseStrSuccess

open WNear.Binary.ParseStr
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.AllocTwo (code310)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_intro stk_word stk_addr)
open WNear.Binary.FromUtf8 (res927 cost927)
open WNear.Binary.FromUtf8Gen (utf8Width)
open WNear.Binary.ArgsLeaves (sliceRead)
open WNear.Binary.SerdeRead (rd)
open WNear.Binary.SerdeErrBox (errCode costErr heapA roomFor4 f647_spec f648_spec_bad f657_eq)
open WNear.Binary.ScratchGrow (sbuf sgCode capAfter fAfter hlAfter roomRes costExt)
open WNear.Binary.ParseEscape (escDecode escK sbufE escCode res649)
open WNear.Binary.SerdeEsc (hexTable)



section Proof
variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- Successful strings with arbitrary scratch capacity, including all allocation/growth costs. -/
theorem f646_success_growth_traced (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 30 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp out de sc ptr idx ptrS capS : UInt32) (ob bs : List UInt8) (i : Nat)
    (maxP hl : Nat) (live : List (Nat × Nat)) (F : Nat)
    (hob : ob.length = 16) (hout : out.toNat + 16 ≤ 2 ^ 32) (hlen : bs.length < 2 ^ 24)
    (hptr : ptr.toNat + bs.length ≤ 2 ^ 32) (hde : de.toNat + 12 ≤ 2 ^ 32) (hsc : sc.toNat + 12 ≤ 2 ^ 32)
    (hsp : 192 ≤ sp.toNat) (hi : i ≤ bs.length) (hcapS : capS.toNat < 2 ^ 25)
    (hroom : roomRun maxP hl capS [] (bs.drop i))
    (finalBytes finalRest : List UInt8) (hok : strRun (bs.drop i) [] = .ok finalBytes finalRest)
    (hvalidUtf : Utf8.utf8Ok finalBytes = true) :
    code646 n maxP inst mi A ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f646 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 de, .i32 sc]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          stk n (sp.toNat - 192) 192 ∗ vt n 1057464 idx ta (A 578) ∗ n ↦[wms][ out.toNat ] ob ∗
          rd n de ptr bs i ∗ n ↦[i32][ sc.toNat ] ptrS ∗ n ↦[i32][ sc.toNat + 4 ] capS ∗
          n ↦[i32][ sc.toNat + 8 ] 0 ∗ sbuf n maxP hl live F ptrS capS [] ∗
          n ↦[wms][ 1062392 ] escTable ∗ n ↦[wms][ 1071704 ] utf8Width ∗ n ↦[wms][ 1062712 ] hexTable))
        (fun _ => (500 + 470 * ((bs.drop i).length - finalRest.length)) * cfg.regularOpCost +
          growthBudget cfg F (ScratchGrow.growthCount capS 0 (appendChunks (bs.drop i) [])) finalBytes.length)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 192) 192 ∗
          vt n 1057464 idx ta (A 578) ∗ n ↦[wms][ 1062392 ] escTable ∗ n ↦[wms][ 1071704 ] utf8Width ∗
          n ↦[wms][ 1062712 ] hexTable ∗ resStrTraced n maxP hl live F out de ptr sc ptrS capS ob bs i)) := by
  apply (f646_success_traced (GF := GF) cfg lim d type htype inst mi A n g ta hm hd Cg gt
    sp out de sc ptr idx ptrS capS ob bs i maxP hl live F hob hout hlen hptr hde hsc
    hsp hi hcapS hroom finalBytes finalRest hok hvalidUtf).trans
  apply AllocGen.MFunSpec_cost
  intro args
  have hsmall : ([] : List UInt8).length + (bs.drop i).length < 2 ^ 27 := by simp; omega
  have hb := (costRun_growth cfg F capS [] (bs.drop i) finalBytes finalRest bs.length hok hsmall).2
  have hg := appendChunks_growthBudget cfg F capS [] (bs.drop i) finalBytes finalRest hok (by simp) (by omega) hsmall
  simp only [List.length_nil, show UInt32.ofNat 0 = (0 : UInt32) from rfl, Nat.mul_zero, Nat.add_zero] at hb hg
  simp only [Nat.add_mul] at hb ⊢
  omega

/-- Compatibility interface that forgets the scratch-growth endpoint. -/
theorem f646_success_growth (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 30 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp out de sc ptr idx ptrS capS : UInt32) (ob bs : List UInt8) (i : Nat)
    (maxP hl : Nat) (live : List (Nat × Nat)) (F : Nat)
    (hob : ob.length = 16) (hout : out.toNat + 16 ≤ 2 ^ 32) (hlen : bs.length < 2 ^ 24)
    (hptr : ptr.toNat + bs.length ≤ 2 ^ 32) (hde : de.toNat + 12 ≤ 2 ^ 32) (hsc : sc.toNat + 12 ≤ 2 ^ 32)
    (hsp : 192 ≤ sp.toNat) (hi : i ≤ bs.length) (hcapS : capS.toNat < 2 ^ 25)
    (hroom : roomRun maxP hl capS [] (bs.drop i))
    (finalBytes finalRest : List UInt8) (hok : strRun (bs.drop i) [] = .ok finalBytes finalRest)
    (hvalidUtf : Utf8.utf8Ok finalBytes = true) :
    code646 n maxP inst mi A ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f646 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 de, .i32 sc]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          stk n (sp.toNat - 192) 192 ∗ vt n 1057464 idx ta (A 578) ∗ n ↦[wms][ out.toNat ] ob ∗
          rd n de ptr bs i ∗ n ↦[i32][ sc.toNat ] ptrS ∗ n ↦[i32][ sc.toNat + 4 ] capS ∗
          n ↦[i32][ sc.toNat + 8 ] 0 ∗ sbuf n maxP hl live F ptrS capS [] ∗
          n ↦[wms][ 1062392 ] escTable ∗ n ↦[wms][ 1071704 ] utf8Width ∗ n ↦[wms][ 1062712 ] hexTable))
        (fun _ => (500 + 470 * ((bs.drop i).length - finalRest.length)) * cfg.regularOpCost +
          growthBudget cfg F (ScratchGrow.growthCount capS 0 (appendChunks (bs.drop i) [])) finalBytes.length)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 192) 192 ∗
          vt n 1057464 idx ta (A 578) ∗ n ↦[wms][ 1062392 ] escTable ∗ n ↦[wms][ 1071704 ] utf8Width ∗
          n ↦[wms][ 1062712 ] hexTable ∗ resStr n maxP hl live F out de ptr sc ptrS capS ob bs i)) := by
  apply (f646_success_growth_traced cfg lim d type htype inst mi A n g ta hm hd Cg gt
    sp out de sc ptr idx ptrS capS ob bs i maxP hl live F hob hout hlen hptr hde hsc
    hsp hi hcapS hroom finalBytes finalRest hok hvalidUtf).trans
  apply spec_post
  intro args rs
  iintro ⟨%hrs, Hg, Hs, Hvt, He, Hw, Ht, Hres⟩
  iframe Hg Hs Hvt He Hw Ht
  isplitr
  · ipureintro; exact hrs
  iapply resStrTraced_forget
  iexact Hres

end Proof
end WNear.Binary.ParseStrSuccess
