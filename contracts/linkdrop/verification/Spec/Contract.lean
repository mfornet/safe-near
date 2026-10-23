import Model.Boundary.Contract

/-!
# linkdrop as a `ContractModel`

The contract model of `NearInterface`, instantiated with linkdrop's state at
the function-call boundary (`Model/Boundary`). `Refines R code linkdrop` is the
complete statement about the binary: every input, every amount of gas, every
resource state.
-/

namespace Linkdrop.Boundary

open NearInterface

def linkdrop : ContractModel where
  State := State
  Call := Call
  Ret := Ret
  Panic := Panic
  Promise := Receipt
  encodeState := encode
  Inv := State.Inv
  Parses := Parses
  encodeRet := encodeRet
  encodeReceipts := encodeReceipts
  panicFailure := Panic.failure
  step := contractStep
  gas := gasBound

theorem linkdrop_parsesFunctional : linkdrop.ParsesFunctional :=
  fun _ _ _ _ h h' => Parses.functional h h'

end Linkdrop.Boundary
