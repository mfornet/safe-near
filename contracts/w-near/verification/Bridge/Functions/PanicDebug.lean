import Bridge.Functions.PanicEntries
import Binary.Code.Part18
import Binary.Code.Part11

namespace WNear.Binary.PanicDebug
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open WNear.Binary.Interface (IfaceMod)
variable {GF : BundledGFunctors} [WasmGS NearState GF]
/-- Exact remaining normal-return formatter contract behind dynamic Debug dispatch. -/
def DebugCalleeSpec (cfg : WasmConfig) (lim : ExecLimits) (d inst : Nat) (mi : ModuleInst)
    (code : Func) (err fmt : UInt32) (Kw Cg : Nat) (P Q : IProp GF) : IProp GF :=
  MFunSpec cfg lim d types[13]! inst mi code Cg
    (fun args => iprop(⌜args = [.i32 err, .i32 fmt]⌝ ∗ P)) (fun _ => Kw)
    (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ Q))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- The actual dynamic Debug trampoline preserves its descriptor and delegates the exact trait call. -/
theorem f882_delegate (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 1 < lim.maxCallDepth) (Cg : Nat)
    (pp err vt fi fmt : UInt32) (af : Nat) (code : Func) (Kw : Nat) (P Q : IProp GF)
    (hpp : pp.toNat + 8 ≤ 2 ^ 32) (hvt : vt.toNat + 16 ≤ 2 ^ 32) :
    inst ↪[inst] mi ∗ af ↪[wf] FuncInst.wasm types[13]! inst code ∗
      DebugCalleeSpec (GF := GF) cfg lim (d + 1) inst mi code err fmt Kw Cg P Q
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f882 Cg
        (fun args => iprop(⌜args = [.i32 pp, .i32 fmt]⌝ ∗
          n ↦[i32][ pp.toNat ] err ∗ n ↦[i32][ pp.toNat + 4 ] vt ∗
          n ↦[i32][ vt.toNat + 12 ] fi ∗ ta ↦[wt][ fi.toNat ] Ref.func af ∗ P))
        (fun _ => 8 * cfg.regularOpCost + activationGas cfg.regularOpCost (entryLocals code [.i32 err, .i32 fmt]) + Kw)
        (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ n ↦[i32][ pp.toNat ] err ∗ n ↦[i32][ pp.toNat + 4 ] vt ∗
          n ↦[i32][ vt.toNat + 12 ] fi ∗ ta ↦[wt][ fi.toNat ] Ref.func af ∗ Q)) := by
  unfold DebugCalleeSpec
  iintro ⟨#Hi, #HF, #HS⟩
  have hn := hm.mem
  have hta := hm.table
  have hty : types[13]! = mi.types[13]! := by rw [hm.types]
  have t13 : types[13]!.params.length = 2 := rfl
  generalize hact : activationGas cfg.regularOpCost (entryLocals code [.i32 err, .i32 fmt]) = ACT
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, E, V, D, HT, HP⟩
  subst hargs
  simp only [f882]
  mstep
  mstep [E]
  mstep; mstep
  mstep [V]
  mstep [D]
  iapply mwpi_cons
  iapply (Borrow.mwpi_call_indirect' (ty := 13) (t := 0) (ta := ta) (idx := fi) (a := af)
    (type := types[13]!) (inst := inst) (mi := mi) (code := code) [.i32 err, .i32 fmt])
  iframe HS HF Hi HT
  isplitr
  · ipureintro; exact ⟨rfl, hta, hty, rfl, hd⟩
  isplitl [Hc]
  · iexact Hc
  isplitr
  · ipureintro; rw [hact]; omega
  isplitl [HP]
  · iframe HP
    ipureintro; rfl
  inext
  iintro %rs HT Hc HQ
  icases HQ with ⟨%hrs, HQ⟩
  subst hrs
  ihave HR : credits Cg R $$ [Hc]
  · iapply BorrowMut.credits_le
    iframe Hc
    ipureintro; rw [hact]; omega
  mstep_post
  mstep
  simp [Post.mfunc, htype]
  iframe HR E V D HT HQ
  iintro Hret
  iexact Hret
end WNear.Binary.PanicDebug

namespace WNear.Binary.PanicDebug
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.Interface
variable {GF : BundledGFunctors} [WasmGS NearState GF]
set_option maxRecDepth 100000

theorem serde_error_debug_vtable : dataWord (1049036 + 12) = bytes32 12 := by
  rw [dataWord_eq _ (by decide)]
  decide +kernel

theorem serde_error_debug_table : wTable.elems[12]? = some (Ref.func 641) := rfl

theorem dynamic_debug_table : wTable.elems[200]? = some (Ref.func 882) := rfl

/-- Exact unresolved formatter at the deployed serde-error Debug method, independent of the dispatch wrapper. -/
def SerdeErrorDebugSpec (cfg : WasmConfig) (lim : ExecLimits) (d inst : Nat) (mi : ModuleInst)
    (err fmt : UInt32) (Kw Cg : Nat) (P Q : IProp GF) : IProp GF :=
  MFunSpec cfg lim d types[13]! inst mi f641 Cg
    (fun args => iprop(⌜args = [.i32 err, .i32 fmt]⌝ ∗ P)) (fun _ => Kw)
    (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ Q))

set_option maxHeartbeats 16000000 in
/-- The actual error vtable delegates to function 641; its precise formatting contract remains explicit. -/
theorem f882_serde_error_delegate (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 1 < lim.maxCallDepth) (Cg : Nat)
    (pp err fmt : UInt32) (Kw : Nat) (P Q : IProp GF) (hpp : pp.toNat + 8 ≤ 2 ^ 32) :
    inst ↪[inst] mi ∗ A 641 ↪[wf] FuncInst.wasm types[13]! inst f641 ∗
      SerdeErrorDebugSpec cfg lim (d + 1) inst mi err fmt Kw Cg P Q
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f882 Cg
        (fun args => iprop(⌜args = [.i32 pp, .i32 fmt]⌝ ∗
          n ↦[i32][ pp.toNat ] err ∗ n ↦[i32][ pp.toNat + 4 ] 1049036 ∗
          n ↦[i32][ 1049048 ] 12 ∗ ta ↦[wt][ 12 ] Ref.func (A 641) ∗ P))
        (fun _ => 19 * cfg.regularOpCost + Kw)
        (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ n ↦[i32][ pp.toNat ] err ∗ n ↦[i32][ pp.toNat + 4 ] 1049036 ∗
          n ↦[i32][ 1049048 ] 12 ∗ ta ↦[wt][ 12 ] Ref.func (A 641) ∗ Q)) := by
  have H := f882_delegate (GF := GF) cfg lim d type htype inst mi A n g ta hm hd Cg
    pp err 1049036 12 fmt (A 641) f641 Kw P Q hpp (by decide)
  have hact : activationGas cfg.regularOpCost (entryLocals f641 [.i32 err, .i32 fmt]) = 11 * cfg.regularOpCost := by
    simp [activationGas, entryLocals, f641, ValType.default]
  rw [hact] at H
  have hcost : 8 * cfg.regularOpCost + 11 * cfg.regularOpCost = 19 * cfg.regularOpCost := by omega
  rw [hcost] at H
  exact H
end WNear.Binary.PanicDebug
