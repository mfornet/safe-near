import Bridge.Functions.PanicEntries
import Binary.Code.Part11
import Binary.Code.Part13
namespace WNear.Binary.FormatResult
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.Interface
variable {GF : BundledGFunctors} [WasmGS NearState GF]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem f610_success (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 0) (inst : Nat) (mi : ModuleInst) (n g ta : Nat)
    (A : Nat → Nat) (hm : IfaceMod mi A n g ta) (Cg : Nat) (gt : GlobalType) (sp : UInt32) :
    ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f610 Cg
      (fun args => iprop(⌜args = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩))
      (fun _ => 12 * cfg.regularOpCost)
      (fun _ rs => iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩)) := by
  have hg := hm.glob
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg⟩
  subst hargs
  simp only [f610]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep
  mstep; mstep; mstep
  mstep; mstep; mstep; mstep [Hg]
  mstep_post
  simp only [UInt32.sub_add_cancel]
  iframe Hg Hc
set_option maxHeartbeats 4000000 in
/-- The actual line/column formatting argument constructor writes the pointer and tag pair. -/
theorem f725_pair (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 0) (inst : Nat) (mi : ModuleInst) (n : Nat)
    (hn : mi.memAddrs[0]? = some n) (Cg : Nat) (out ptr tag old0 old4 : UInt32)
    (hout : out.toNat + 8 ≤ 2 ^ 32) :
    ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f725 Cg
      (fun args => iprop(⌜args = [.i32 out, .i32 ptr, .i32 tag]⌝ ∗
        n ↦[i32][ out.toNat ] old0 ∗ n ↦[i32][ out.toNat + 4 ] old4))
      (fun _ => 6 * cfg.regularOpCost)
      (fun _ rs => iprop(⌜rs = []⌝ ∗
        n ↦[i32][ out.toNat ] ptr ∗ n ↦[i32][ out.toNat + 4 ] tag)) := by
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, W0, W4⟩
  subst hargs
  simp only [f725]
  mstep; mstep; mstep [W4]
  mstep; mstep; mstep [W0]
  mstep_post
  iframe Hc W0 W4
end WNear.Binary.FormatResult
