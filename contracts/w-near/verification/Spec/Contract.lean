import Spec.Invariants
import Model.Contract
import NearInterface.Refines

/-!
# wNEAR as a `ContractModel`

The contract model of `NearInterface`, instantiated with the wNEAR state,
calls and semantics. `wnear cfg` fixes the model's configuration only for
the invariant: the measured per-account storage usage a state records. The
semantics reads the protocol configuration from each context, as the binary
does.

`Refines R protocol code (wnear cfg)` is then the complete statement about the
binary under the protocol configuration `protocol`: every input, every amount
of gas, every resource state.
-/

namespace WNear

open NearInterface

/-- The wNEAR contract model. -/
@[blueprint "def:contract-model"
  (statement := /-- The wNEAR model at the function-call boundary: states stored as \cref{def:encode}, the invariant \cref{def:inv}, calls read from JSON arguments as near-sdk 3.1.0 does, \cref{def:step} followed by the runtime's balance and storage-stake checks, return values and receipts as serde\_json and near-sdk write them, the exact panic messages, and a gas bound valid for every trie. -/)]
def wnear (cfg : Config) : ContractModel where
  State := State
  Call := Call
  Ret := Ret
  Panic := Panic
  Promise := Promise
  encodeState := encode
  Inv := Inv cfg
  Parses := Parses
  encodeRet := encodeRet
  encodeReceipts _ := encodeReceipts
  panicFailure := Panic.failure
  step := contractStep
  gas ctx _ c := gasBound ctx c
  proofBound ctx _ _ := proofBound ctx

theorem wnear_parsesFunctional (cfg : Config) : (wnear cfg).ParsesFunctional :=
  fun _ _ _ _ h h' => Parses.functional h h'

end WNear
