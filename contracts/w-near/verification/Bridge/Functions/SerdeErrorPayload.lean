import Bridge.Functions.SerdeErrorWriters
namespace WNear.Binary.SerdeErrorPayload
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.Interface WNear.Binary.SerdeErrorWriters
variable {GF : BundledGFunctors} [WasmGS NearState GF]
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000 in
/-- The actual message variant borrows its owned pointer and length and writes them through Formatter. -/
theorem f592_message (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 1 < lim.maxCallDepth) (Cg : Nat)
    (e fmt ptr len : UInt32) (Kw : Nat) (P Q : IProp GF) (he : e.toNat + 12 ≤ 2 ^ 32) :
    inst ↪[inst] mi ∗ A 912 ↪[wf] FuncInst.wasm types[15]! inst f912 ∗
      StaticWriteSpec cfg lim (d + 1) inst mi fmt ptr len Kw Cg P Q ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f592 Cg
        (fun args => iprop(⌜args = [.i32 e, .i32 fmt]⌝ ∗ n ↦[i32][ e.toNat ] 0 ∗
          n ↦[i32][ e.toNat + 4 ] ptr ∗ n ↦[i32][ e.toNat + 8 ] len ∗ P))
        (fun _ => 100 * cfg.regularOpCost +
          activationGas cfg.regularOpCost (entryLocals f912 [.i32 fmt, .i32 ptr, .i32 len]) + Kw)
        (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ n ↦[i32][ e.toNat ] 0 ∗
          n ↦[i32][ e.toNat + 4 ] ptr ∗ n ↦[i32][ e.toNat + 8 ] len ∗ Q)) := by
  unfold StaticWriteSpec
  iintro ⟨#Hi, #F912, #HS⟩
  have hn := hm.mem
  have ha912 := hm.funcs 912 (by decide)
  have t15 : types[15]!.params.length = 3 := rfl
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Tag, Ptr, Len, HP⟩
  subst hargs
  simp only [f592]
  repeat mstep
  mstep [Tag]
  repeat mstep
  simp only [UInt32.toNat_ofNat', Nat.reduceMod, List.getElem?_cons_zero, Option.getD_some]
  mstep_post
  simp only [List.getElem?_cons_zero, Option.getD_some]
  mstep_post
  repeat mstep
  mstep [Ptr]
  repeat mstep
  mstep [Len] with (simp [UInt32.toNat_add]; omega)
  repeat mstep
  mcall HS using [HP] with (mstep_norm_full; omega)
  · iframe HP
  icases HQ with ⟨%hrs, HQ⟩
  subst hrs
  repeat mstep
  mstep_post
  mcredits R
  simp [Post.mfunc, htype]
  iframe Hc Tag Ptr Len HQ

/-- Exact actual I/O payload formatter, with its owned payload and selected sink resources. -/
def IOErrorDebugSpec (cfg : WasmConfig) (lim : ExecLimits) (d inst : Nat) (mi : ModuleInst)
    (payload fmt : UInt32) (K Cg : Nat) (P Q : IProp GF) : IProp GF :=
  PanicDebug.DebugCalleeSpec cfg lim d inst mi f804 payload fmt K Cg P Q

set_option maxHeartbeats 16000000 in
/-- The I/O variant follows its actual payload formatter rather than inventing a static string. -/
theorem f592_io (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 1 < lim.maxCallDepth) (Cg : Nat)
    (e fmt : UInt32) (Kw : Nat) (P Q : IProp GF) (he : e.toNat + 4 < 2 ^ 32) :
    inst ↪[inst] mi ∗ A 804 ↪[wf] FuncInst.wasm types[13]! inst f804 ∗
      IOErrorDebugSpec cfg lim (d + 1) inst mi (e + 4) fmt Kw Cg P Q ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f592 Cg
        (fun args => iprop(⌜args = [.i32 e, .i32 fmt]⌝ ∗ n ↦[i32][ e.toNat ] 1 ∗ P))
        (fun _ => 100 * cfg.regularOpCost +
          activationGas cfg.regularOpCost (entryLocals f804 [.i32 (e + 4), .i32 fmt]) + Kw)
        (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ n ↦[i32][ e.toNat ] 1 ∗ Q)) := by
  unfold IOErrorDebugSpec PanicDebug.DebugCalleeSpec
  iintro ⟨#Hi, #F804, #HS⟩
  have hn := hm.mem
  have ha804 := hm.funcs 804 (by decide)
  have t13 : types[13]!.params.length = 2 := rfl
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Tag, HP⟩
  subst hargs
  simp only [f592]
  repeat mstep
  mstep [Tag]
  repeat mstep
  simp only [UInt32.toNat_ofNat', Nat.reduceMod]
  mstep_post
  repeat mstep
  mcall HS using [HP] with (mstep_norm_full; omega)
  · iframe HP
  icases HQ with ⟨%hrs, HQ⟩
  subst hrs
  repeat mstep
  mstep_post
  mcredits R
  simp [Post.mfunc, htype]
  iframe Hc Tag HQ
end WNear.Binary.SerdeErrorPayload
