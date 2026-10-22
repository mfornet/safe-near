import Model.Proposal

namespace SputnikDAO2

theorem voteStep_requires_in_progress (state : VoteState)
    (account : String) (choice : VoteChoice) (amount threshold : Nat)
    (h : state.status ≠ .inProgress) :
    voteStep state account choice amount threshold = none := by
  simp [voteStep, h]

theorem voteStep_rejects_duplicate (state : VoteState)
    (account : String) (choice : VoteChoice) (amount threshold : Nat)
    (h : account ∈ state.voters) :
    voteStep state account choice amount threshold = none := by
  by_cases hs : state.status = .inProgress
  · simp [voteStep, hs, h]
  · simp [voteStep, hs]

theorem voteStep_adds_voter (state next : VoteState)
    (account : String) (choice : VoteChoice) (amount threshold : Nat)
    (h : voteStep state account choice amount threshold = some next) :
    account ∈ next.voters := by
  by_cases hs : state.status = .inProgress
  · by_cases hv : account ∈ state.voters
    · simp [voteStep, hs, hv] at h
    · simp [voteStep, hs, hv] at h
      cases h
      simp
  · simp [voteStep, hs] at h

theorem voteStep_prevents_second_vote (state next : VoteState)
    (account : String) (choice nextChoice : VoteChoice)
    (amount threshold nextAmount nextThreshold : Nat)
    (h : voteStep state account choice amount threshold = some next) :
    voteStep next account nextChoice nextAmount nextThreshold = none := by
  exact voteStep_rejects_duplicate next account nextChoice nextAmount
    nextThreshold (voteStep_adds_voter state next account choice amount threshold h)

theorem approve_vote_increments_count (state next : VoteState)
    (account : String) (amount threshold : Nat)
    (h : voteStep state account .approve amount threshold = some next) :
    next.approvals = state.approvals + amount := by
  by_cases hs : state.status = .inProgress
  · by_cases hv : account ∈ state.voters
    · simp [voteStep, hs, hv] at h
    · simp [voteStep, hs, hv, countVote] at h
      cases h
      rfl
  · simp [voteStep, hs] at h

theorem zero_weight_vote_with_zero_threshold_approves :
    voteStep
      ⟨.inProgress, [], 0, 0, 0⟩ "alice.near" .approve 0 0 =
      some ⟨.approved, ["alice.near"], 0, 0, 0⟩ := by
  decide

theorem callback_rejects_zero_results (status : ProposalStatus)
    (proposalExists callerSelf : Bool) (result : CallbackResult) :
    callbackStatus status proposalExists callerSelf 0 result = none := by
  simp [callbackStatus]

theorem callback_rejects_multiple_results (status : ProposalStatus)
    (proposalExists callerSelf : Bool) (result : CallbackResult)
    (count : Nat) (h : count ≠ 1) :
    callbackStatus status proposalExists callerSelf count result = none := by
  simp [callbackStatus, h]

theorem callback_rejects_external_caller (status : ProposalStatus)
    (result : CallbackResult) :
    callbackStatus status true false 1 result = none := by
  simp [callbackStatus]

theorem callback_rejects_missing_proposal (status : ProposalStatus)
    (result : CallbackResult) :
    callbackStatus status false true 1 result = none := by
  simp [callbackStatus]

theorem failed_callback_overwrites_approved :
    callbackStatus .approved true true 1 .failure = some .failed := by
  decide

theorem successful_callback_overwrites_failed :
    callbackStatus .failed true true 1 .success = some .approved := by
  decide

end SputnikDAO2
