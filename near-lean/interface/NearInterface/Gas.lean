import NearInterface.Error

/-!
# Gas accounting

`GasCounter` mirrors `near_vm_runner::logic::gas_counter::GasCounter`:
burnt gas is irreversible, promise gas is what this execution attaches to
the receipts it creates, and `used = burnt + promises`. Both are bounded:
burnt by the per-call limit, used by the prepaid gas.

`Fee` and `ActionFees` are `near_parameters::RuntimeFeesConfig` as the VM
needs them: send fees (same shard / other shard) and execution fees for each
`ActionCosts` variant.
-/

namespace Wasm.Near

/-- Diagnostic decomposition of gas burnt. Costs remain charged through the
gas counter; this records their origin for independent conformance comparisons. -/
structure GasProfile where
  ext : List (String × Nat) := []
  actionBurnt : Nat := 0
  wasm : Nat := 0
  deriving Repr, BEq, Inhabited

def GasProfile.addExt (profile : GasProfile) (name : String) (amount : Nat) : GasProfile :=
  if amount == 0 then profile
  else
    let previous := ((profile.ext.find? (·.1 == name)).map (·.2)).getD 0
    { profile with ext := (name, previous + amount) :: profile.ext.filter (·.1 != name) }

/-- All the gas the profile records. -/
def GasProfile.total (profile : GasProfile) : Nat :=
  (profile.ext.map (·.2)).sum + profile.actionBurnt + profile.wasm

/-- One action fee: `send_sir`, `send_not_sir`, `execution`. -/
structure Fee where
  sendSir : Nat := 0
  sendNotSir : Nat := 0
  execution : Nat := 0
  deriving Repr, Inhabited, BEq

def Fee.send (f : Fee) (sir : Bool) : Nat := if sir then f.sendSir else f.sendNotSir

/-- Accumulate fees before charging, preserving native exhaustion precedence. -/
def Fee.add (left right : Fee) : Fee :=
  { sendSir := left.sendSir + right.sendSir
    sendNotSir := left.sendNotSir + right.sendNotSir
    execution := left.execution + right.execution }

/-- `near_parameters::ActionCosts`. -/
structure ActionFees where
  createAccount : Fee := {}
  deleteAccount : Fee := {}
  deployContractBase : Fee := {}
  deployContractByte : Fee := {}
  functionCallBase : Fee := {}
  functionCallByte : Fee := {}
  transfer : Fee := {}
  stake : Fee := {}
  addFullAccessKey : Fee := {}
  addFunctionCallKeyBase : Fee := {}
  addFunctionCallKeyByte : Fee := {}
  deleteKey : Fee := {}
  newActionReceipt : Fee := {}
  newDataReceiptBase : Fee := {}
  newDataReceiptByte : Fee := {}
  delegate : Fee := {}
  useGlobalContractBase : Fee := {}
  useGlobalContractByte : Fee := {}
  deployGlobalContractBase : Fee := {}
  deployGlobalContractByte : Fee := {}
  gasKeyTransferBase : Fee := {}
  gasKeyByte : Fee := {}
  gasKeyNonceWriteBase : Fee := {}
  deriving Repr, Inhabited

/-- Replace the execution fee of the `ActionCosts` variant `name` (nearcore's snake_case
name); `none` for a name this table does not have. -/
def ActionFees.setExecution (f : ActionFees) (name : String) (execution : Nat) : Option ActionFees :=
  let set (fee : Fee) : Fee := { fee with execution }
  match name with
  | "create_account" => some { f with createAccount := set f.createAccount }
  | "delete_account" => some { f with deleteAccount := set f.deleteAccount }
  | "deploy_contract_base" => some { f with deployContractBase := set f.deployContractBase }
  | "deploy_contract_byte" => some { f with deployContractByte := set f.deployContractByte }
  | "function_call_base" => some { f with functionCallBase := set f.functionCallBase }
  | "function_call_byte" => some { f with functionCallByte := set f.functionCallByte }
  | "transfer" => some { f with transfer := set f.transfer }
  | "stake" => some { f with stake := set f.stake }
  | "add_full_access_key" => some { f with addFullAccessKey := set f.addFullAccessKey }
  | "add_function_call_key_base" => some { f with addFunctionCallKeyBase := set f.addFunctionCallKeyBase }
  | "add_function_call_key_byte" => some { f with addFunctionCallKeyByte := set f.addFunctionCallKeyByte }
  | "delete_key" => some { f with deleteKey := set f.deleteKey }
  | "new_action_receipt" => some { f with newActionReceipt := set f.newActionReceipt }
  | "new_data_receipt_base" => some { f with newDataReceiptBase := set f.newDataReceiptBase }
  | "new_data_receipt_byte" => some { f with newDataReceiptByte := set f.newDataReceiptByte }
  | "delegate" => some { f with delegate := set f.delegate }
  | "use_global_contract_base" => some { f with useGlobalContractBase := set f.useGlobalContractBase }
  | "use_global_contract_byte" => some { f with useGlobalContractByte := set f.useGlobalContractByte }
  | "deploy_global_contract_base" => some { f with deployGlobalContractBase := set f.deployGlobalContractBase }
  | "deploy_global_contract_byte" => some { f with deployGlobalContractByte := set f.deployGlobalContractByte }
  | "gas_key_transfer_base" => some { f with gasKeyTransferBase := set f.gasKeyTransferBase }
  | "gas_key_byte" => some { f with gasKeyByte := set f.gasKeyByte }
  | "gas_key_nonce_write_base" => some { f with gasKeyNonceWriteBase := set f.gasKeyNonceWriteBase }
  | _ => none

/-- `ExtCosts` as a lookup by nearcore's snake_case name; missing names cost
`0` so a partial table degrades gracefully instead of trapping. -/
structure ExtCosts where
  lookup : String → Nat := fun _ => 0

def ExtCosts.cost (c : ExtCosts) (name : String) : Nat := c.lookup name

instance : Inhabited ExtCosts := ⟨{}⟩

structure GasCounter where
  /-- Gas burnt by this execution so far (`fast_counter.burnt_gas`). -/
  burnt : Nat := 0
  /-- Gas attached to created receipts (`promises_gas`). -/
  promises : Nat := 0
  /-- `prepaid_gas` of the function call. -/
  prepaid : Nat := 0
  /-- `max_gas_burnt` (the limit config, or the view call's own limit). -/
  maxBurnt : Nat := 0
  deriving Repr, Inhabited

namespace GasCounter

def used (g : GasCounter) : Nat := g.burnt + g.promises

/-- `deduct_gas(burn, use)` with `burn ≤ use`. On failure the counter is left
in nearcore's post-failure shape (burnt capped at the hard limit, promise gas
dropped) and the error says which limit was hit. -/
def deduct (g : GasCounter) (burn use : Nat) : GasCounter × Option HostError :=
  let newPromises := g.promises + (use - burn)
  let newBurnt := g.burnt + burn
  let newUsed := newBurnt + newPromises
  if newBurnt ≤ g.maxBurnt ∧ newUsed ≤ g.prepaid then
    ({ g with burnt := newBurnt, promises := newPromises }, none)
  else
    let hardLimit := min g.prepaid g.maxBurnt
    ({ g with burnt := min newBurnt hardLimit, promises := 0 },
     some (if newBurnt > g.maxBurnt then .gasLimitExceeded else .gasExceeded))

/-- `burn_gas`. -/
def burn (g : GasCounter) (n : Nat) : GasCounter × Option HostError := g.deduct n n

/-- `prepay_gas`: attach `n` gas to a receipt (used, not burnt). -/
def prepay (g : GasCounter) (n : Nat) : GasCounter × Option HostError := g.deduct 0 n

/-- `pay_action_accumulated(burn, use)`: `burn` is burnt now, `use` on top is
owed to the receipt's execution. -/
def payAction (g : GasCounter) (burn use : Nat) : GasCounter × Option HostError :=
  g.deduct burn (burn + use)

end GasCounter

end Wasm.Near
