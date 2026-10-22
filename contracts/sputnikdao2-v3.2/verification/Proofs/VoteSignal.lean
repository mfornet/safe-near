import Model.VoteSignal

namespace SputnikDAO2

theorem signal_vote_missing_proposal (state : SignalVoteState)
    (ctx : SignalVoteContext) (h : state.proposalPresent = false) :
    runSignalVote state ctx = none := by simp [runSignalVote, h]

theorem signal_vote_denied (state : SignalVoteState)
    (ctx : SignalVoteContext) (h : ctx.permissionAllowed = false) :
    runSignalVote state ctx = none := by simp [runSignalVote, h]

theorem signal_vote_wrong_kind (state : SignalVoteState)
    (ctx : SignalVoteContext) (h : ctx.exactKindMatches = false) :
    runSignalVote state ctx = none := by simp [runSignalVote, h]

theorem signal_vote_approved_refunds (state : SignalVoteState)
    (ctx : SignalVoteContext) (next : MultiVoteState)
    (hp : state.proposalPresent = true)
    (ha : ctx.permissionAllowed = true)
    (hk : ctx.exactKindMatches = true)
    (hv : multiVoteStep state.ballot ctx.account ctx.choice ctx.userWeight
      ctx.submission ctx.period ctx.now ctx.totalSupply = some next)
    (hs : next.status = .approved) :
    runSignalVote state ctx = some
      ⟨true, next,
        (returnProposalBonds state.locked ctx.currentBondPolicy state.proposer false).lockedAfter,
        appendLog20 state.globalLog
          ⟨ctx.account, ctx.proposalId, ctx.choice, ctx.blockHeight⟩,
        [(returnProposalBonds state.locked ctx.currentBondPolicy state.proposer false).returnedTransfer],
        .refundBond⟩ := by
  simp [runSignalVote, hp, ha, hk, hv, hs]

theorem signal_vote_rejected_refunds (state : SignalVoteState)
    (ctx : SignalVoteContext) (next : MultiVoteState)
    (hp : state.proposalPresent = true)
    (ha : ctx.permissionAllowed = true)
    (hk : ctx.exactKindMatches = true)
    (hv : multiVoteStep state.ballot ctx.account ctx.choice ctx.userWeight
      ctx.submission ctx.period ctx.now ctx.totalSupply = some next)
    (hs : next.status = .rejected) :
    runSignalVote state ctx = some
      ⟨true, next,
        (returnProposalBonds state.locked ctx.currentBondPolicy state.proposer false).lockedAfter,
        appendLog20 state.globalLog
          ⟨ctx.account, ctx.proposalId, ctx.choice, ctx.blockHeight⟩,
        [(returnProposalBonds state.locked ctx.currentBondPolicy state.proposer false).returnedTransfer],
        .refundBond⟩ := by
  simp [runSignalVote, hp, ha, hk, hv, hs]

theorem signal_vote_removed_keeps_lock (state : SignalVoteState)
    (ctx : SignalVoteContext) (next : MultiVoteState)
    (hp : state.proposalPresent = true)
    (ha : ctx.permissionAllowed = true)
    (hk : ctx.exactKindMatches = true)
    (hv : multiVoteStep state.ballot ctx.account ctx.choice ctx.userWeight
      ctx.submission ctx.period ctx.now ctx.totalSupply = some next)
    (hs : next.status = .removed) :
    runSignalVote state ctx = some
      ⟨false, next, state.locked,
        appendLog20 state.globalLog
          ⟨ctx.account, ctx.proposalId, ctx.choice, ctx.blockHeight⟩,
        [], .deleteProposal⟩ := by
  simp [runSignalVote, hp, ha, hk, hv, hs]

theorem signal_vote_expired_keeps_lock (state : SignalVoteState)
    (ctx : SignalVoteContext) (next : MultiVoteState)
    (hp : state.proposalPresent = true)
    (ha : ctx.permissionAllowed = true)
    (hk : ctx.exactKindMatches = true)
    (hv : multiVoteStep state.ballot ctx.account ctx.choice ctx.userWeight
      ctx.submission ctx.period ctx.now ctx.totalSupply = some next)
    (hs : next.status = .expired) :
    runSignalVote state ctx = some
      ⟨true, next, state.locked,
        appendLog20 state.globalLog
          ⟨ctx.account, ctx.proposalId, ctx.choice, ctx.blockHeight⟩,
        [], .storeOnly⟩ := by
  simp [runSignalVote, hp, ha, hk, hv, hs]

theorem signal_vote_in_progress_keeps_lock (state : SignalVoteState)
    (ctx : SignalVoteContext) (next : MultiVoteState)
    (hp : state.proposalPresent = true)
    (ha : ctx.permissionAllowed = true)
    (hk : ctx.exactKindMatches = true)
    (hv : multiVoteStep state.ballot ctx.account ctx.choice ctx.userWeight
      ctx.submission ctx.period ctx.now ctx.totalSupply = some next)
    (hs : next.status = .inProgress) :
    runSignalVote state ctx = some
      ⟨true, next, state.locked,
        appendLog20 state.globalLog
          ⟨ctx.account, ctx.proposalId, ctx.choice, ctx.blockHeight⟩,
        [], .storeOnly⟩ := by
  simp [runSignalVote, hp, ha, hk, hv, hs]

theorem signal_vote_success_log_bounded (state : SignalVoteState)
    (ctx : SignalVoteContext) (result : SignalVoteResult)
    (h : runSignalVote state ctx = some result)
    (hlog : state.globalLog.length ≤ 20) :
    result.globalLog.length ≤ 20 := by
  have happend : (appendLog20 state.globalLog
      ⟨ctx.account, ctx.proposalId, ctx.choice, ctx.blockHeight⟩).length ≤ 20 := by
    by_cases hf : 20 ≤ state.globalLog.length
    · simp [appendLog20, hf]
      omega
    · simp [appendLog20, hf]
      omega
  unfold runSignalVote at h
  split at h <;> try contradiction
  cases hv : multiVoteStep state.ballot ctx.account ctx.choice ctx.userWeight
      ctx.submission ctx.period ctx.now ctx.totalSupply with
  | none => simp [hv] at h
  | some next =>
      simp [hv] at h
      cases hs : next.status <;> simp [hs] at h <;> cases h <;> exact happend

end SputnikDAO2
