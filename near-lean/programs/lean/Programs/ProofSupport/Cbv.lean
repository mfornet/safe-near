import Lean.Elab.Tactic.Cbv
import Lean.Elab.Tactic.CbvSimproc
import Lean.Meta.Tactic.Cbv.ControlFlow

/-!
# Kernel-checked evaluation for program proofs

Lean 4.34.1's literal-conditional `cbv` shortcuts construct `ite_true`,
`ite_false`, `dite_true` and `dite_false` without their implicit `Decidable`
argument. The kernel rejects those proof terms. `program_cbv` supplies that
argument explicitly and lets ordinary reduction handle other conditionals.
The replacement procedures are enabled only during this tactic invocation.
Named theorems use `set_option Elab.async false in` because Lean permits
changes to this evaluator extension only on its main elaboration thread.
Every generated equality is still checked by the kernel.
-/

namespace Programs.ProofSupport

open Lean Meta Sym Sym.Simp

cbv_simproc_decl literalIte (@ite _ _ _ _ _) := fun e => do
  let_expr f@ite α c inst a b := e | return .rfl
  if (← isTrueExpr c) then
    return .step a (mkApp4 (mkConst ``_root_.ite_true f.constLevels!) α inst a b)
  else if (← isFalseExpr c) then
    return .step b (mkApp4 (mkConst ``_root_.ite_false f.constLevels!) α inst a b)
  return .rfl

cbv_simproc_decl literalDIte (@dite _ _ _ _ _) := fun e => do
  let_expr f@dite α c inst a b := e | return .rfl
  if (← isTrueExpr c) then
    let a' ← share <| a.betaRev #[mkConst ``True.intro]
    return .step a' (mkApp4 (mkConst ``_root_.dite_true f.constLevels!) α inst a b)
  else if (← isFalseExpr c) then
    let b' ← share <| b.betaRev #[mkConst ``not_false]
    return .step b' (mkApp4 (mkConst ``_root_.dite_false f.constLevels!) α inst a b)
  return .rfl

/-- Evaluate a program proof with the pinned toolchain's conditional fix. -/
elab "program_cbv" : tactic => do
  if (← getEnv).asyncPrefix?.isSome then
    throwError "program_cbv requires `set_option Elab.async false in` on a named theorem"
  let original ← Meta.Tactic.Cbv.getCbvSimprocs
  let some iteKeys ← Meta.Tactic.Cbv.getCbvSimprocDeclKeys? ``literalIte
    | throwError "Missing literal conditional simplifier pattern"
  let some diteKeys ← Meta.Tactic.Cbv.getCbvSimprocDeclKeys? ``literalDIte
    | throwError "Missing dependent conditional simplifier pattern"
  modifyEnv fun env => Meta.Tactic.Cbv.cbvSimprocExtension.modifyState env fun s =>
    s.simprocNames.fold (init :=
        (s.addCore iteKeys ``literalIte .pre literalIte).addCore diteKeys ``literalDIte .pre literalDIte) fun result name =>
      if name.toString.endsWith ".simpIteCbv" || name.toString.endsWith ".simpDIteCbv" then
        result.erase name
      else result
  try
    Elab.Tactic.evalTactic (← `(tactic| cbv))
  finally
    -- Keep lazily generated equation lemmas, restoring only the simproc set.
    modifyEnv fun env => Meta.Tactic.Cbv.cbvSimprocExtension.modifyState env fun _ => original

-- Exercise all four proof constructors, including noncanonical instances.
example (decision : Decidable True) : @ite Nat True decision 7 9 = 7 := by program_cbv
example (decision : Decidable False) : @ite Nat False decision 7 9 = 9 := by program_cbv
example (decision : Decidable True) : @dite Nat True decision (fun _ => 7) (fun _ => 9) = 7 := by program_cbv
example (decision : Decidable False) : @dite Nat False decision (fun _ => 7) (fun _ => 9) = 9 := by program_cbv

end Programs.ProofSupport
