import Spec.RuntimeInstance
import Interpreter.Wasm.Decoder.Wat
import Lean

/-!
# The refinement obligation (open)

`Spec/Refinement.lean` defines `Refines` for an abstract runtime and
`Spec/RuntimeInstance.lean` instantiates it with `near-lean/vm`. This file
pins the remaining inputs, the deployed module and its byte size, so that
`refines_near_lean` below is a closed statement about `contract.wasm`.

The module is `contract.wasm` printed as text (`wasm2wat`, kept at
`near-lean/vm/tests/fixtures/w_near.wat`) because `near-lean` only has a text
decoder. The text file is read at elaboration time; trusting the theorem means
trusting that the text is a faithful print of the binary, which
`just reproduce w-near` and the runtime conformance tests check but Lean does
not. The byte size is that of the binary itself, as the VM charges for it.

The theorem is the only open proof in the project. `just wnear-audit`
tolerates `sorryAx` in this module alone.
-/

namespace WNear

open Wasm.Near

open Lean Elab Term in
/-- The contents of a file, as a string literal, read when this file is elaborated.
Paths are relative to the package root (`contracts/w-near/verification`). -/
elab "file_contents%" path:str : term => do
  return mkStrLit (← IO.FS.readFile path.getString)

open Lean Elab Term in
/-- The size in bytes of a file, as a literal, read when this file is elaborated. -/
elab "file_size%" path:str : term => do
  return mkNatLit (← IO.FS.readBinFile path.getString).size

/-- `contract.wasm` in text form. -/
def wNearWat : String := file_contents% "../../../near-lean/vm/tests/fixtures/w_near.wat"

/-- Byte size of `contract.wasm`. -/
def wNearCodeSize : Nat := file_size% "../contract.wasm"

/-- The model's runtime parameters induced by the protocol parameters. -/
def Config.ofRuntime (cfg : RuntimeConfig) : Config :=
  { extraBytesPerRecord := cfg.fees.numExtraBytesRecord }

/-- **Open.** The deployed wNEAR binary refines the model under every protocol
configuration whose measured account entry fits a `u64`: whenever the text
form decodes to a module `code`, `RefinesNearLean cfg code wNearCodeSize
(Config.ofRuntime cfg)` holds.

Decoding is a hypothesis rather than evaluated here, so the statement does
not depend on running the decoder inside the kernel; the runtime tests
(`just runtime-adapter-test`) check that it succeeds. -/
theorem refines_near_lean (cfg : RuntimeConfig) (code : Wasm.Module)
    (hcfg : (Config.ofRuntime cfg).WF)
    (hcode : Wasm.Decoder.Wat.decode wNearWat = .ok code) :
    RefinesNearLean cfg code wNearCodeSize (Config.ofRuntime cfg) := by
  sorry

end WNear
