import Model.DelegationExport

namespace SputnikDAO2

theorem delegation_key_ne_root (account : String) :
    delegationKey account ≠ daoRootKey := by
  simp [delegationKey, daoRootKey]

theorem delegate_export_rejects_attached_deposit
    (raw : BountyRawTrie) (ctx : CallWrapperContext)
    (state : Option DelegationState) (account : String) (amount : Nat)
    (encodeRoot : DelegationState → BountyBytes)
    (hdeposit : ctx.attachedDeposit ≠ 0) :
    runDelegateExport raw ctx state account amount encodeRoot = none := by
  have hi : findDAOExport "delegate" =
      some ⟨"delegate", .call, false, false⟩ := by decide
  simp [runDelegateExport, runGeneratedCallWrapper, hi, hdeposit]

theorem delegate_export_rejects_wrong_caller
    (raw : BountyRawTrie) (ctx : CallWrapperContext)
    (state : DelegationState) (account : String) (amount : Nat)
    (encodeRoot : DelegationState → BountyBytes)
    (hcaller : state.stakingId ≠ some ctx.predecessor) :
    runDelegateExport raw ctx (some state) account amount encodeRoot = none := by
  have hi : findDAOExport "delegate" =
      some ⟨"delegate", .call, false, false⟩ := by decide
  simp [runDelegateExport, delegate, hcaller,
    runGeneratedCallWrapper, hi]

theorem delegate_export_rejects_missing_state
    (raw : BountyRawTrie) (ctx : CallWrapperContext)
    (account : String) (amount : Nat)
    (encodeRoot : DelegationState → BountyBytes) :
    runDelegateExport raw ctx none account amount encodeRoot = none := by
  have hi : findDAOExport "delegate" =
      some ⟨"delegate", .call, false, false⟩ := by decide
  simp [runDelegateExport, runGeneratedCallWrapper, hi]

theorem delegate_export_success_keys
    (raw final : BountyRawTrie) (ctx : CallWrapperContext)
    (state : DelegationState) (account : String) (amount : Nat)
    (encodeRoot : DelegationState → BountyBytes)
    (h : runDelegateExport raw ctx (some state) account amount
      encodeRoot = some final) :
    ∃ after balance,
      delegate state ctx.predecessor account amount = some after ∧
      balanceOf after.balances account = some balance ∧
      final (delegationKey account) =
        some (encodeDelegationBalance balance) ∧
      final daoRootKey = some (encodeRoot after) := by
  have hi : findDAOExport "delegate" =
      some ⟨"delegate", .call, false, false⟩ := by decide
  cases hd : delegate state ctx.predecessor account amount with
  | none =>
      simp [runDelegateExport, hd, runGeneratedCallWrapper, hi] at h
  | some after =>
      cases hb : balanceOf after.balances account with
      | none =>
          simp [runDelegateExport, hd, hb,
            runGeneratedCallWrapper, hi] at h
      | some balance =>
          have hw :
              runGeneratedCallWrapper raw "delegate"
                { ctx with stateDecoded := true }
                (some (delegationRawDelegate raw account balance,
                  encodeRoot after)) = some final := by
            simpa [runDelegateExport, hd, hb] using h
          simp [runGeneratedCallWrapper, hi] at hw
          rcases hw with ⟨_, hfinal⟩
          refine ⟨after, balance, rfl, hb, ?_, ?_⟩
          · rw [← hfinal]
            simp [bountyRawWrite, delegationRawDelegate,
              delegation_key_ne_root]
          · rw [← hfinal]
            simp [bountyRawWrite]

theorem undelegate_export_rejects_attached_deposit
    (raw : BountyRawTrie) (ctx : CallWrapperContext)
    (state : Option DelegationState) (account : String) (amount : Nat)
    (encodeRoot : DelegationState → BountyBytes)
    (hdeposit : ctx.attachedDeposit ≠ 0) :
    runUndelegateExport raw ctx state account amount encodeRoot = none := by
  have hi : findDAOExport "undelegate" =
      some ⟨"undelegate", .call, false, false⟩ := by decide
  simp [runUndelegateExport, runGeneratedCallWrapper, hi, hdeposit]

theorem undelegate_export_rejects_wrong_caller
    (raw : BountyRawTrie) (ctx : CallWrapperContext)
    (state : DelegationState) (account : String) (amount : Nat)
    (encodeRoot : DelegationState → BountyBytes)
    (hcaller : state.stakingId ≠ some ctx.predecessor) :
    runUndelegateExport raw ctx (some state) account amount
      encodeRoot = none := by
  have hi : findDAOExport "undelegate" =
      some ⟨"undelegate", .call, false, false⟩ := by decide
  simp [runUndelegateExport, undelegate, hcaller,
    runGeneratedCallWrapper, hi]

theorem undelegate_export_success_keys
    (raw final : BountyRawTrie) (ctx : CallWrapperContext)
    (state : DelegationState) (account : String) (amount : Nat)
    (encodeRoot : DelegationState → BountyBytes)
    (h : runUndelegateExport raw ctx (some state) account amount
      encodeRoot = some final) :
    ∃ after balance,
      undelegate state ctx.predecessor account amount = some after ∧
      balanceOf after.balances account = some balance ∧
      final (delegationKey account) =
        some (encodeDelegationBalance balance) ∧
      final daoRootKey = some (encodeRoot after) := by
  have hi : findDAOExport "undelegate" =
      some ⟨"undelegate", .call, false, false⟩ := by decide
  cases hd : undelegate state ctx.predecessor account amount with
  | none =>
      simp [runUndelegateExport, hd, runGeneratedCallWrapper, hi] at h
  | some after =>
      cases hb : balanceOf after.balances account with
      | none =>
          simp [runUndelegateExport, hd, hb,
            runGeneratedCallWrapper, hi] at h
      | some balance =>
          have hw :
              runGeneratedCallWrapper raw "undelegate"
                { ctx with stateDecoded := true }
                (some (delegationRawDelegate raw account balance,
                  encodeRoot after)) = some final := by
            simpa [runUndelegateExport, hd, hb] using h
          simp [runGeneratedCallWrapper, hi] at hw
          rcases hw with ⟨_, hfinal⟩
          refine ⟨after, balance, rfl, hb, ?_, ?_⟩
          · rw [← hfinal]
            simp [bountyRawWrite, delegationRawDelegate,
              delegation_key_ne_root]
          · rw [← hfinal]
            simp [bountyRawWrite]

theorem register_export_rejects_wrong_deposit
    (raw : BountyRawTrie) (ctx : CallWrapperContext)
    (state : Option DelegationState) (account : String)
    (byteCost : Nat) (encodeRoot : DelegationState → BountyBytes)
    (hdeposit : ctx.attachedDeposit ≠ registrationDeposit byteCost) :
    runRegisterDelegationExport raw ctx state account byteCost
      encodeRoot = none := by
  cases state with
  | none =>
      have hi : findDAOExport "register_delegation" =
          some ⟨"register_delegation", .call, true, false⟩ := by decide
      simp [runRegisterDelegationExport, runGeneratedCallWrapper, hi]
  | some before =>
      have hbody : registerDelegation before ctx.predecessor account
          ctx.attachedDeposit byteCost = none := by
        simp [registerDelegation, hdeposit]
      have hi : findDAOExport "register_delegation" =
          some ⟨"register_delegation", .call, true, false⟩ := by decide
      simp [runRegisterDelegationExport, hbody,
        runGeneratedCallWrapper, hi]

theorem register_export_rejects_wrong_caller
    (raw : BountyRawTrie) (ctx : CallWrapperContext)
    (state : DelegationState) (account : String)
    (byteCost : Nat) (encodeRoot : DelegationState → BountyBytes)
    (hcaller : state.stakingId ≠ some ctx.predecessor) :
    runRegisterDelegationExport raw ctx (some state) account byteCost
      encodeRoot = none := by
  have hi : findDAOExport "register_delegation" =
      some ⟨"register_delegation", .call, true, false⟩ := by decide
  simp [runRegisterDelegationExport, registerDelegation, hcaller,
    runGeneratedCallWrapper, hi]

theorem register_export_success_keys
    (raw final : BountyRawTrie) (ctx : CallWrapperContext)
    (state : DelegationState) (account : String) (byteCost : Nat)
    (encodeRoot : DelegationState → BountyBytes)
    (h : runRegisterDelegationExport raw ctx (some state) account byteCost
      encodeRoot = some final) :
    ∃ after,
      registerDelegation state ctx.predecessor account
        ctx.attachedDeposit byteCost = some after ∧
      final (delegationKey account) = some (encodeDelegationBalance 0) ∧
      final daoRootKey = some (encodeRoot after) := by
  have hi : findDAOExport "register_delegation" =
      some ⟨"register_delegation", .call, true, false⟩ := by decide
  cases hd : registerDelegation state ctx.predecessor account
      ctx.attachedDeposit byteCost with
  | none =>
      simp [runRegisterDelegationExport, hd,
        runGeneratedCallWrapper, hi] at h
  | some after =>
      have hw : runGeneratedCallWrapper raw "register_delegation"
          { ctx with stateDecoded := true }
          (some (delegationRawRegister raw account,
            encodeRoot after)) = some final := by
        simpa [runRegisterDelegationExport, hd] using h
      simp [runGeneratedCallWrapper, hi] at hw
      rcases hw with ⟨_, hfinal⟩
      refine ⟨after, rfl, ?_, ?_⟩
      · rw [← hfinal]
        simp [bountyRawWrite, delegationRawRegister,
          delegation_key_ne_root]
      · rw [← hfinal]
        simp [bountyRawWrite]

theorem exported_reregistration_can_break_accounting
    (raw : BountyRawTrie)
    (encodeRoot : DelegationState → BountyBytes) :
    let ctx : CallWrapperContext :=
      ⟨"dao.near", "stake.near", 16, true, true⟩
    let before : DelegationState :=
      ⟨some "stake.near", [("alice.near", 1)], 1⟩
    let after : DelegationState :=
      ⟨some "stake.near", [("alice.near", 0)], 1⟩
    coherentDelegation before ∧ ¬ coherentDelegation after ∧
      ∃ final,
        runRegisterDelegationExport raw ctx (some before)
          "alice.near" 1 encodeRoot = some final ∧
        final (delegationKey "alice.near") =
          some (encodeDelegationBalance 0) ∧
        final daoRootKey = some (encodeRoot after) := by
  dsimp
  refine ⟨by simp [coherentDelegation, balanceSum],
    by simp [coherentDelegation, balanceSum], ?_⟩
  have hi : findDAOExport "register_delegation" =
      some ⟨"register_delegation", .call, true, false⟩ := by decide
  let after : DelegationState :=
    ⟨some "stake.near", [("alice.near", 0)], 1⟩
  let final := bountyRawWrite
    (delegationRawRegister raw "alice.near") daoRootKey
    (encodeRoot after)
  refine ⟨final, ?_, ?_, ?_⟩
  · simp [runRegisterDelegationExport, registerDelegation,
      registrationDeposit, setBalance, runGeneratedCallWrapper,
      maxU128, hi, final, after]
  · simp [final, delegationRawRegister, bountyRawWrite,
      delegation_key_ne_root]
  · simp [final, after, bountyRawWrite]

end SputnikDAO2
