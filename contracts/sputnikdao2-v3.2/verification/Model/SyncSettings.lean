import Model.Upgrade
import Model.ProposalBonds

namespace SputnikDAO2

/-! Approved synchronous `ChangeConfig` and `FactoryInfoUpdate` execution.
The latter overwrites the raw FACTORY key without first decoding its old
contents, so it can replace malformed bytes. `update` subsequently reads
the newly stored info. Borsh encoding and storage failure are external. -/

structure ConfigImage where
  name : String
  purpose : String
  metadata : CodeBytes
  deriving Repr, DecidableEq

structure SyncSettingsState where
  config : ConfigImage
  factoryRead : FactoryRead
  locked : Nat
  deriving Repr, DecidableEq

inductive SyncSettingsAction where
  | changeConfig (config : ConfigImage)
  | factoryInfoUpdate (info : FactoryInfo)
  deriving Repr, DecidableEq

structure SyncSettingsOutcome where
  state : SyncSettingsState
  refund : BondTransfer
  callbackScheduled : Bool
  deriving Repr, DecidableEq

def executeSyncSettings (state : SyncSettingsState)
    (action : SyncSettingsAction) (oldProposalBond : Nat)
    (proposer : String) : SyncSettingsOutcome :=
  let next := match action with
    | .changeConfig config => { state with config := config }
    | .factoryInfoUpdate info => { state with factoryRead := .stored info }
  ⟨{ next with locked := state.locked - oldProposalBond },
    ⟨proposer, oldProposalBond⟩, false⟩

def updateContextAfterSettings (ctx : UpdateContext)
    (outcome : SyncSettingsOutcome) : UpdateContext :=
  { ctx with factoryRead := outcome.state.factoryRead }

end SputnikDAO2
