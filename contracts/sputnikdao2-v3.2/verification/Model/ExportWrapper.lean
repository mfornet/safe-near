import Model.WrapperInit

namespace SputnikDAO2

/-! Inventory of the 34 named contract exports in the canonical Wasm.
The source audit checks the binary names independently. Class and flags are
the pinned source/near-sdk 5.24.1 projection; this table itself is not a
proof that the Wasm instruction bodies implement the models. -/

inductive ExportClass where
  | init | call | view | raw
  deriving Repr, DecidableEq

structure ExportInfo where
  name : String
  kind : ExportClass
  payable : Bool
  privateCall : Bool
  deriving Repr, DecidableEq

private def entry (name : String) (kind : ExportClass)
    (payable privateCall : Bool := false) : ExportInfo :=
  ⟨name, kind, payable, privateCall⟩

def daoExports : List ExportInfo := [
  entry "new" .init,
  entry "migrate" .init false true,
  entry "remove_blob" .call,
  entry "get_factory_info" .view,
  entry "store_blob" .raw,
  entry "update" .raw,
  entry "add_proposal" .call true,
  entry "act_proposal" .call,
  entry "on_proposal_callback" .call false true,
  entry "bounty_claim" .call true,
  entry "bounty_done" .call true,
  entry "bounty_giveup" .call,
  entry "register_delegation" .call true,
  entry "delegate" .call,
  entry "undelegate" .call,
  entry "version" .view,
  entry "get_config" .view,
  entry "get_policy" .view,
  entry "get_staking_contract" .view,
  entry "has_blob" .view,
  entry "get_locked_storage_amount" .view,
  entry "get_available_amount" .view,
  entry "delegation_total_supply" .view,
  entry "delegation_balance_of" .view,
  entry "delegation_balance_ratio" .view,
  entry "get_last_proposal_id" .view,
  entry "get_proposals" .view,
  entry "get_proposal" .view,
  entry "get_bounty" .view,
  entry "get_last_bounty_id" .view,
  entry "get_bounties" .view,
  entry "get_bounty_claims" .view,
  entry "get_bounty_number_of_claims" .view,
  entry "get_actions_log" .view
]

def findDAOExport (name : String) : Option ExportInfo :=
  daoExports.find? (fun info => info.name == name)

structure CallWrapperContext where
  current : String
  predecessor : String
  attachedDeposit : Nat
  argumentsDecoded : Bool
  stateDecoded : Bool
  deriving Repr, DecidableEq

-- The generated mutating wrapper checks private/deposit/arguments/callback
-- inputs, reads Contract state, runs the method body, serializes its return,
-- then writes the resulting root. `body` supplies the body-level raw writes
-- and root bytes only on successful execution. JSON, callback-result and
-- return serialization are abstracted by the Boolean/Option inputs.
def runGeneratedCallWrapper (_raw : BountyRawTrie)
    (name : String) (ctx : CallWrapperContext)
    (body : Option (BountyRawTrie × BountyBytes)) : Option BountyRawTrie :=
  match findDAOExport name with
  | none => none
  | some info =>
      if info.kind != .call ||
          (info.privateCall && ctx.current != ctx.predecessor) ||
          (!info.payable && ctx.attachedDeposit != 0) ||
          !ctx.argumentsDecoded || !ctx.stateDecoded then none
      else body.map (fun (afterBody, rootBytes) =>
        bountyRawWrite afterBody daoRootKey rootBytes)

-- Generated views deserialize Contract state and serialize a return value,
-- but have no root write. Parsing/return serialization and host reads are
-- supplied by `decoded` and `view`.
def runGeneratedViewWrapper {α β : Type}
    (raw : BountyRawTrie) (name : String) (decoded : Option α)
    (attachedDeposit : Nat) (view : α → BountyRawTrie → β) :
    Option (β × BountyRawTrie) :=
  match findDAOExport name with
  | none => none
  | some info =>
      if info.kind != .view then none
      else runViewWrapper raw decoded attachedDeposit view

end SputnikDAO2
