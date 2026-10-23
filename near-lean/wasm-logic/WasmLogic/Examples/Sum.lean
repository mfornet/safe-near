import WasmLogic.Rules
import WasmLogic.Adequacy

/-!
# A worked example: a counting loop

`sumTo` is a hand-built module with one function `sum : [i32] → [i32]`
computing `1 + 2 + ... + n` with a `loop`, locals and `br_if`. The
specification is stated as a weakest precondition from store ownership and
proved by running the machine (`wp_run`); adequacy then turns it into a
statement about every run of `Exec.run`. The proof touches no step by hand:
the machine computes, the kernel checks the computation.
-/

namespace WasmLogic.Examples

open Wasm Iris Iris.BI Iris.ProgramLogic WasmLogic

/-- `local 0` is `n`, `local 1` accumulates. -/
def sumBody : Expr := [
  .block .empty [
    .loop .empty [
      .local_get 0, .i32_eqz, .br_if 1,
      .local_get 1, .local_get 0, .i32_binop .add, .local_set 1,
      .local_get 0, .i32_const 1, .i32_binop .sub, .local_set 0,
      .br 0]],
  .local_get 1]

def sumTo : Module :=
  { types := #[{ params := [.i32], results := [.i32] }],
    funcs := #[{ type := 0, locals := [.i32], body := sumBody }],
    exports := #[{ name := "sum", desc := .func 0 }] }

def limits : ExecLimits := {}

/-- The configuration about to run `sum n`: validate, instantiate with no
host, start the function at store address 0. -/
def entry (n : UInt32) : Option (Config Unit) :=
  match sumTo.validate .all with
  | .error _ => none
  | .ok vm =>
    match Link.instantiateModule (Store.empty ()) vm [] with
    | .error _ => none
    | .ok (store, inst) => Exec.startWasm store limits inst.funcAddrs[0]! [.i32 n]

/-- The values a run of `sum n` within `fuel` steps returns. -/
def result (n : UInt32) (fuel : Nat) : Option (List Value) :=
  match entry n with
  | none => none
  | some c =>
    match Exec.run fuel c with
    | .done vs _ => some vs
    | _ => none

/-- The machine computes `1 + ... + 10` in 200 steps; checked by the kernel. -/
theorem result_ten : result 10 200 = some [.i32 55] := by decide +kernel

theorem run_sum_ten : ∃ c s', entry 10 = some c ∧ Exec.run 200 c = .done [.i32 55] s' := by
  have h := result_ten
  unfold result at h
  split at h
  · cases h
  · rename_i c hc
    split at h
    · rename_i vs s' hrun
      cases h
      exact ⟨c, s', hc, hrun⟩
    · cases h

/-- The weakest-precondition specification of `sum 10`, from store ownership. -/
theorem wp_sum_ten {GF : BundledGFunctors} [OwnPGS (Store Unit) GF] (c : Config Unit)
    (hc : entry 10 = some c) :
    ownP (GF := GF) c.store ⊢ WP (Code.running (H := Unit) c.limits c.thread)
      @ Stuckness.MaybeStuck; ⊤ {{ o, ⌜o = .values [.i32 55]⌝ }} := by
  obtain ⟨c', s', hc', hrun⟩ := run_sum_ten
  rw [hc] at hc'
  cases hc'
  iintro Hσ
  iapply wp_run 200 c.store c.limits c.thread [.i32 55] s' hrun
  isplitl [Hσ]
  · iexact Hσ
  · iintro _
    ipureintro
    rfl

/-- Adequacy: every finished run of `sum 10` returns 55 and never traps. -/
theorem sum_ten_adequate (c : Config Unit) (hc : entry 10 = some c) (fuel : Nat) :
    match Exec.run fuel c with
    | .done vs _ => vs = [.i32 55]
    | .trap _ _ => False
    | .outOfFuel _ => True := by
  have h := adequacy (H := Unit) c.store c.limits c.thread (fun o => o = .values [.i32 55])
    (by intro i; exact wp_sum_ten c hc) fuel
  have hcfg : Code.config c.store c.limits c.thread = c := rfl
  rw [hcfg] at h
  revert h
  cases Exec.run fuel c <;> simp

end WasmLogic.Examples
