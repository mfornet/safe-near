import Model.ExportWrapper
import Model.DelegationEncoding

namespace SputnikDAO2

/-! A first composition of a source method with its generated export wrapper.
`state` is the decoded projection of the Contract root. `encodeRoot` supplies
serialization of the complete resulting Contract, which is not inferred from
the delegation projection. The raw account write is the LookupMap effect. -/

def runDelegateExport (raw : BountyRawTrie) (ctx : CallWrapperContext)
    (state : Option DelegationState) (account : String) (amount : Nat)
    (encodeRoot : DelegationState → BountyBytes) : Option BountyRawTrie :=
  let body := state.bind fun before => do
    let after ← delegate before ctx.predecessor account amount
    let balance ← balanceOf after.balances account
    some (delegationRawDelegate raw account balance, encodeRoot after)
  runGeneratedCallWrapper raw "delegate"
    { ctx with stateDecoded := state.isSome } body

def runUndelegateExport (raw : BountyRawTrie) (ctx : CallWrapperContext)
    (state : Option DelegationState) (account : String) (amount : Nat)
    (encodeRoot : DelegationState → BountyBytes) : Option BountyRawTrie :=
  let body := state.bind fun before => do
    let after ← undelegate before ctx.predecessor account amount
    let balance ← balanceOf after.balances account
    some (delegationRawDelegate raw account balance, encodeRoot after)
  runGeneratedCallWrapper raw "undelegate"
    { ctx with stateDecoded := state.isSome } body

def runRegisterDelegationExport (raw : BountyRawTrie)
    (ctx : CallWrapperContext) (state : Option DelegationState)
    (account : String) (byteCost : Nat)
    (encodeRoot : DelegationState → BountyBytes) : Option BountyRawTrie :=
  let body := state.bind fun before => do
    let after ← registerDelegation before ctx.predecessor account
      ctx.attachedDeposit byteCost
    some (delegationRawRegister raw account, encodeRoot after)
  runGeneratedCallWrapper raw "register_delegation"
    { ctx with stateDecoded := state.isSome } body

end SputnikDAO2
