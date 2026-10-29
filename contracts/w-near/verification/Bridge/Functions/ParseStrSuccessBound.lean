import Bridge.Functions.ParseStrSuccess
import Bridge.Functions.StrSuccessCostBound

/-!
# A callable successful string contract with linear non-append work

This bound preserves the complete functional result and keeps scratch allocation
and copying separate. Its conservative constants do not yet establish the
argument reader's 470-ops-per-byte allowance.
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

/-- A successful string read, with all non-append work bounded by consumed input bytes. -/
theorem f646_success_linear (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
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
        (fun _ => (700 + 550 * ((bs.drop i).length - finalRest.length)) * cfg.regularOpCost +
          appendCost cfg F capS [] (bs.drop i) bs.length)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 192) 192 ∗
          vt n 1057464 idx ta (A 578) ∗ n ↦[wms][ 1062392 ] escTable ∗ n ↦[wms][ 1071704 ] utf8Width ∗
          n ↦[wms][ 1062712 ] hexTable ∗ resStr n maxP hl live F out de ptr sc ptrS capS ob bs i)) := by
  apply (f646_success (GF := GF) cfg lim d type htype inst mi A n g ta hm hd Cg gt
    sp out de sc ptr idx ptrS capS ob bs i maxP hl live F hob hout hlen hptr hde hsc
    hsp hi hcapS hroom finalBytes finalRest hok hvalidUtf).trans
  apply AllocGen.MFunSpec_cost
  intro args
  have hbound := (costRun_linear_work cfg F capS [] (bs.drop i) finalBytes finalRest bs.length hok).2
  simp only [List.length_nil, Nat.mul_zero, Nat.add_zero] at hbound
  simp only [Nat.add_mul] at hbound ⊢
  omega

end Proof
end WNear.Binary.ParseStrSuccess
