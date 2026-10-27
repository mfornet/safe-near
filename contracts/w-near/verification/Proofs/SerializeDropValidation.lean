import Proofs.SerializeValidation
import Proofs.DeallocateValidation

/-! The actual serializer drop in the getter satisfies the positive heap
branch used by the f321 proof, not merely code equivalence with f68. -/
namespace WNear.Proofs.SerializeDropValidation
open Wasm Wasm.Near WNear.Testing

def validate : IO Unit := do
  let protocol ← RuntimeConfig.load "../../../near-lean/vm/configs" RuntimeConfig.latestVersion
  let bytes ← IO.FS.readBinFile "../contract.wasm"
  let module ← orThrow ((Wasm.Binary.decode bytes).mapError Wasm.Binary.DecodeError.message)
  let h ← orThrow (Harness.load protocol module internalContext [])
  let seen ← captureAll protocol module bytes.size [321]
  let mut checked := 0
  for (method, entry) in seen.getD 321 #[] do
    if method != "ft_total_supply" then continue
    let address := u32Arg entry.args 0
    let memory := h.mem entry.store
    let core := DeallocateValidation.coreLayout h memory 1074896
      (UInt32.ofNat (h.readNat entry.store address 4)) (UInt32.ofNat (h.readNat entry.store (address+4) 4)) 1
    if !DeallocateValidation.coreNative core then throw (IO.userError "getter f321 native heap condition mismatch")
    let result := h.call entry.store 321 entry.args
    if result.gas != op h 318 then throw (IO.userError "getter f321 gas mismatch")
    DeallocateValidation.checkFuel h 321 229 entry
    DeallocateValidation.checkMemory h 321 result.after (DeallocateCore.finalMemory core)
    checked := checked + 1
  if checked != 1 then throw (IO.userError s!"expected one getter f321 capture, got {checked}")
  IO.println "PASS getter f321: positive native heap branch; actual318 units/229 steps; exact final memory"
#eval validate
end WNear.Proofs.SerializeDropValidation
