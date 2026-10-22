import Model.ConstructorTrie
import Model.Migration

namespace SputnikDAO2

/-! Projection of near-sdk 5.24.1's generated `#[init]` wrapper for `new`.
The macro checks deposit, parses JSON arguments, checks `STATE` existence,
calls `new`, and writes its returned Contract root. `argumentsDecoded` is a
parser result supplied by the adapter; gas, rollback and Wasm instruction
refinement remain external. -/

structure NewWrapperContext where
  attachedDeposit : Nat
  argumentsDecoded : Bool
  deriving Repr, DecidableEq

def runNewWrapper (raw : BountyRawTrie)
    (ctx : NewWrapperContext) (config : WireConfig)
    (policy : WirePolicy) (predecessor : String) :
    Option BountyRawTrie :=
  if ctx.attachedDeposit != 0 then none
  else if !ctx.argumentsDecoded then none
  else if (raw daoRootKey).isSome then none
  else some (constructorOnExistingTrie raw config policy predecessor)

/-! `migrate` is `#[private] #[init(ignore_state)]`: the macro checks
predecessor=self and zero deposit but deliberately has no `STATE`-exists
rejection. The method handles version/state reads, then the macro writes the
returned root. `encodeCurrent` is a separate Borsh-refinement input. -/

def runMigrateWrapper (raw : BountyRawTrie)
    (attachedDeposit : Nat) (ctx : MigrationContext)
    (encodeCurrent : CurrentState → BountyBytes) : Option BountyRawTrie := do
  if ctx.predecessor != ctx.current then none else pure ()
  if attachedDeposit != 0 then none else pure ()
  let result ← runMigrate ctx
  let afterVersion :=
    if result.wroteV2Version then
      bountyRawWrite raw daoVersionKey initializedVersionBytes
    else raw
  some (bountyRawWrite afterVersion daoRootKey
    (encodeCurrent result.state))

/-! near-sdk 5.24.1 classifies a method as View when its receiver is owned
`self` or a nonmutating reference. `get_staking_contract(self)` is therefore
loaded from state but not written back. View wrappers have no deposit check.
`decoded` and the result serializer are external refinement inputs. -/

def runViewWrapper {α β : Type} (raw : BountyRawTrie)
    (decoded : Option α) (_attachedDeposit : Nat)
    (view : α → BountyRawTrie → β) : Option (β × BountyRawTrie) :=
  decoded.map (fun state => (view state raw, raw))

def runStakingViewWrapper (raw : BountyRawTrie)
    (decoded : Option CurrentState) (attachedDeposit : Nat) :
    Option (String × BountyRawTrie) :=
  runViewWrapper raw decoded attachedDeposit
    (fun state _ => viewStakingContract state.core.stakingId)

end SputnikDAO2
