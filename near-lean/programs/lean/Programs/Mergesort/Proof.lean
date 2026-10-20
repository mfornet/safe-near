-- Ported from Talos Mergesort/Proof.lean at 80644390de3ad4db3055445259a034413ae41577 (AGPL-3.0).
import Programs.Mergesort.Adequacy
import Programs.Mergesort.DriverProof
import Programs.Mergesort.Func1Proof
import Programs.Mergesort.Func5Proof
import Programs.Mergesort.Func8Proof
import Programs.Mergesort.Func9Proof

/-!
# Public correctness composition for merge sort

`func3_correct` composes the authoritative body contracts for the reachable
driver, Vec, and allocator functions.  `mergesort_correct` then applies the
checked partial-adequacy bridge from the real exported call to
`PublicEntrySpecification`.

The entry configuration is defined in `Adequacy` using `.call 6`.  No theorem
in this path starts execution at `func3Def.body`, and no theorem claims
termination.
-/

namespace Programs.Mergesort.Proof

open Iris
open Wasm Universal
open Wasm.SepLogic Wasm.SmallStep
open Programs.Mergesort.Contracts

/-- The generated driver satisfies its authoritative call contract by
composition of all reachable local-function correctness theorems. -/
theorem func3_correct
    {hlc : HasLC} [WasmSmallStepGS hlc Universal.State] :
    Func3Spec (hlc := hlc) := Programs.Mergesort.DriverProof.func3_correct_of
    (Programs.Mergesort.Func1Proof.func1_correct_of
      (Programs.Mergesort.Func0Proof.func0_correct_of
        Programs.Mergesort.Func5Proof.func5_correct
        Programs.Mergesort.Func8Proof.func8_correct))
    Programs.Mergesort.Func5Proof.func5_correct
    Programs.Mergesort.Func9Proof.func9_correct

/-- Public outcome-sensitive partial correctness for the exported
`mergesort` call. -/
@[proves Programs.Mergesort.Spec.PublicEntrySpecification]
theorem mergesort_correct :
    Programs.Mergesort.Spec.PublicEntrySpecification :=
  Programs.Mergesort.Adequacy.entry_adequacy_of_func3 func3_correct

end Programs.Mergesort.Proof
