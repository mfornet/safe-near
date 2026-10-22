import Model.ExecuteUpgrade

namespace SputnikDAO2

theorem self_upgrade_ignores_factory_override (current : String)
    (storedA storedB : FactoryInfo) (args : CodeBytes)
    (locked : Nat) (policy : BondPolicyAmounts) (proposer : String) :
    executeUpgradeSelf current storedA args locked policy proposer =
      executeUpgradeSelf current storedB args locked policy proposer := by rfl

theorem self_upgrade_without_parent_aborts (current : String)
    (stored : FactoryInfo) (args : CodeBytes)
    (locked : Nat) (policy : BondPolicyAmounts) (proposer : String)
    (h : factoryParentSuffix current = none) :
    executeUpgradeSelf current stored args locked policy proposer = none := by
  simp [executeUpgradeSelf, h]

theorem self_upgrade_receipts (current parent : String)
    (stored : FactoryInfo) (args : CodeBytes)
    (locked : Nat) (policy : BondPolicyAmounts) (proposer : String)
    (h : factoryParentSuffix current = some parent) :
    executeUpgradeSelf current stored args locked policy proposer =
      some ⟨⟨parent, "update", args, 0, 0, 1⟩,
        returnProposalBonds locked policy proposer false, false⟩ := by
  simp [executeUpgradeSelf, h]

theorem remote_upgrade_missing_raw_blob_aborts (receiver method : String)
    (locked : Nat) (policy : BondPolicyAmounts) (proposer : String) :
    executeUpgradeRemote receiver method none locked policy proposer = none := by
  rfl

theorem remote_upgrade_receipts (receiver method : String)
    (code : CodeBytes) (locked : Nat) (policy : BondPolicyAmounts)
    (proposer : String) :
    executeUpgradeRemote receiver method (some code) locked policy proposer =
      some ⟨⟨receiver, method, code, 0, 0, 0⟩,
        returnProposalBonds locked policy proposer false, false⟩ := by
  rfl

theorem self_upgrade_bond_refund_is_current_policy (current parent : String)
    (stored : FactoryInfo) (args : CodeBytes)
    (locked : Nat) (policy : BondPolicyAmounts) (proposer : String)
    (h : factoryParentSuffix current = some parent) :
    (executeUpgradeSelf current stored args locked policy proposer).map
      (fun plan => (plan.immediateBondReturn.returnedTransfer,
        plan.immediateBondReturn.lockedAfter, plan.callbackScheduled)) =
      some (⟨proposer, policy.proposalBond⟩,
        locked - policy.proposalBond, false) := by
  simp [executeUpgradeSelf, h, returnProposalBonds]

end SputnikDAO2
