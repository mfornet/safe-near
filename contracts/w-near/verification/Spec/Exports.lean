import Model.Args
import Wasm.Syntax

/-!
# What the binary exports

The functions `contract.wasm` exports are exactly the methods `Call.decode`
reads. `refines_wnear` takes this, and the absence of a start function, as
facts about the decoded module; the adapter tests check them on the binary.
-/

namespace WNear

/-- The binary's exported functions: the methods `Call.decode` reads. -/
def exportedMethods : List String :=
  ["storage_minimum_balance", "near_deposit", "near_withdraw", "new", "ft_transfer", "ft_transfer_call",
   "ft_total_supply", "ft_balance_of", "ft_resolve_transfer", "storage_deposit", "storage_withdraw",
   "storage_unregister", "storage_balance_bounds", "storage_balance_of", "ft_metadata"]

def funcExportNames (m : Wasm.Module) : List String :=
  m.exports.toList.filterMap fun e => match e.desc with
    | .func _ => some e.name
    | _ => none

end WNear
