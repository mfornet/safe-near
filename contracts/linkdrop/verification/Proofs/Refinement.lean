import Spec.Contract
import NearRuntime.Boundary
import Lean

/-!
# The refinement obligation (open)

`Spec/Contract.lean` gives linkdrop's `ContractModel`; `NearRuntime.Boundary`
gives near-lean's `RuntimeInterface`. This file pins the deployed binary, so
that `refines_linkdrop` is a closed statement about `contract.wasm`.

The binary is embedded as a hex string, read when this file is elaborated;
decoding it is a hypothesis rather than evaluated in the kernel, and the
adapter tests (`just linkdrop-adapter-test`) check that it succeeds.
`create_account_advanced` deploys the bytes it is given, so the code decoder
is assumed to report no limitation.

The theorem is open. `just linkdrop-audit` tolerates `sorryAx` in this module
alone.
-/

namespace Linkdrop.Boundary

open NearInterface

open Lean Elab Term in
/-- The bytes of a file, as a hex string literal, read when this file is
elaborated. Paths are relative to the package root. -/
elab "file_hex%" path:str : term => do
  let bytes ← IO.FS.readBinFile path.getString
  let hex := String.join (bytes.toList.map fun b =>
    String.ofList [Nat.digitChar (b.toNat / 16), Nat.digitChar (b.toNat % 16)])
  return mkStrLit hex

/-- `contract.wasm`, as deployed on `near`. -/
def linkdropHex : String := file_hex% "../contract.wasm"

def linkdropBytes : ByteArray := ⟨(bytesOfHex linkdropHex).toArray⟩

/-- **Open.** The deployed linkdrop binary refines the model: for every
context and every resource state, near-lean's execution of `contract.wasm`
is the model's as `Refines` states it. `codeOf` decodes the code a call's
promises deploy (`create_account_advanced`); it reports no limitation. -/
theorem refines_linkdrop (code : Wasm.Module) (codeOf : List UInt8 → Near.ContractCode)
    (hcodeOf : ∀ bytes, (codeOf bytes).decodeIssue = none)
    (hcode : Wasm.Binary.decode linkdropBytes = .ok code) :
    Refines Near.Boundary.nearRuntime
      { code := { module := code, size := linkdropBytes.size, hash := "" }, codeOf } linkdrop := by
  sorry

end Linkdrop.Boundary
