import Spec.Contract
import NearRuntime.Boundary
import Lean

/-!
# The refinement obligation (open)

`Spec/Contract.lean` gives the wNEAR `ContractModel`; `NearRuntime.Boundary`
gives near-lean's `RuntimeInterface`, a function-call action followed by the
receipt's storage-stake check. This file pins the deployed binary, so that
`refines_wnear` below is a closed statement about `contract.wasm`.

The binary is embedded as a hex string, read when this file is elaborated;
decoding it is a hypothesis rather than evaluated in the kernel, and the
adapter tests (`just runtime-adapter-test`) check that it succeeds.

The theorem is the only open proof in the project. `just wnear-audit`
tolerates `sorryAx` in this module alone.
-/

namespace WNear

open NearInterface

open Lean Elab Term in
/-- The bytes of a file, as a hex string literal, read when this file is
elaborated. Paths are relative to the package root. -/
elab "file_hex%" path:str : term => do
  let bytes ← IO.FS.readBinFile path.getString
  let hex := String.join (bytes.toList.map fun b =>
    String.ofList [Nat.digitChar (b.toNat / 16), Nat.digitChar (b.toNat % 16)])
  return mkStrLit hex

/-- Bytes from a lowercase hex string. -/
def bytesOfHex (s : String) : ByteArray :=
  let digit (c : Char) : Nat := if c.isDigit then c.toNat - '0'.toNat else c.toNat - 'a'.toNat + 10
  let rec go : List Char → List UInt8
    | a :: b :: rest => UInt8.ofNat (digit a * 16 + digit b) :: go rest
    | _ => []
  ⟨(go s.toList).toArray⟩

/-- `contract.wasm`, as deployed. -/
def wNearHex : String := file_hex% "../contract.wasm"

def wNearBytes : ByteArray := bytesOfHex wNearHex

/-- **Open.** The deployed wNEAR binary refines the model: for every
configuration whose measured account entry fits a `u64`, every context and
every resource state, near-lean's execution of `contract.wasm` is the model's
as `Refines` states it. `codeOf` decodes code that the call's promises deploy;
wNEAR deploys none. -/
@[blueprint "spec:refinement"
  (statement := /-- The deployed binary refines \cref{def:contract-model}: for every storage representing a model state and every context the runtime can build, the execution reports no interpreter limitation; with at least the model's gas bound attached, it agrees with the model on return value, storage, balance, storage usage, logs, receipts and failure, and uses at most that much gas; with less, it agrees or fails for gas with no effects; and input that is no call fails with no effects. -/)]
theorem refines_wnear (cfg : Config) (code : Wasm.Module) (codeOf : List UInt8 → Near.ContractCode)
    (hcfg : cfg.WF) (hcode : Wasm.Binary.decode wNearBytes = .ok code) :
    Refines Near.Boundary.nearRuntime
      { code := { module := code, size := wNearBytes.size, hash := "" }, codeOf } (wnear cfg) := by
  sorry

end WNear
