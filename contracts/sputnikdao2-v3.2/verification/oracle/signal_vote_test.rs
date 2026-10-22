
#[cfg(test)]
mod signal_vote_projection_oracle {
    use super::*;
    use near_sdk::mock::MockAction;
    use near_sdk::test_utils::{get_created_receipts, VMContextBuilder};
    use near_sdk::testing_env;
    use std::collections::{HashMap, VecDeque};

    fn run(action: Action, now: u64, high_quorum: bool) ->
        (Option<ProposalStatus>, NearToken, Vec<NearToken>, usize, Option<U128>) {
        let voter: AccountId = "alice.near".parse().unwrap();
        let mut context = VMContextBuilder::new();
        context.predecessor_account_id(voter.clone()).block_timestamp(now);
        testing_env!(context.build());
        let mut contract = Contract::new(
            Config::test_config(),
            VersionedPolicy::Default(vec![voter.clone()]),
        );
        if high_quorum {
            let mut policy = default_policy(vec![voter.clone()]);
            policy.default_vote_policy.quorum = U128(2);
            contract.policy.set(&VersionedPolicy::Current(policy));
        }
        contract.proposals.insert(&0, &VersionedProposal::Latest(Proposal {
            proposer: voter,
            description: "signal".into(),
            kind: ProposalKind::Vote,
            status: ProposalStatus::InProgress,
            vote_counts: HashMap::new(),
            votes: HashMap::new(),
            submission_time: U64(0),
            last_actions_log: VecDeque::new(),
        }));
        contract.last_proposal_id = 1;
        contract.locked_amount = NearToken::from_near(1);
        contract.act_proposal(0, action, ProposalKind::Vote, None);
        let transfers = get_created_receipts().iter().flat_map(|receipt|
            receipt.actions.iter().filter_map(|action| match action {
                MockAction::Transfer { deposit, .. } => Some(*deposit),
                _ => None,
            })
        ).collect::<Vec<_>>();
        let stored: Option<Proposal> = contract.proposals.get(&0).map(Into::into);
        let approval_count = stored.as_ref().and_then(|proposal|
            proposal.vote_counts.get("council").map(|counts| counts[0]));
        (stored.map(|proposal| proposal.status), contract.locked_amount,
            transfers, contract.actions_log.len(), approval_count)
    }

    #[test]
    fn signal_vote_dispatches_all_status_branches() {
        let bond = NearToken::from_near(1);
        let zero = NearToken::from_yoctonear(0);
        let (status, locked, transfers, logs, count) = run(Action::VoteApprove, 0, false);
        assert_eq!(status, Some(ProposalStatus::Approved));
        assert_eq!(locked, zero);
        assert_eq!(transfers, vec![bond]);
        assert_eq!(logs, 1);
        assert_eq!(count, Some(U128(1)));

        let (status, locked, transfers, logs, _) = run(Action::VoteReject, 0, false);
        assert_eq!(status, Some(ProposalStatus::Rejected));
        assert_eq!(locked, zero);
        assert_eq!(transfers, vec![bond]);
        assert_eq!(logs, 1);

        let (status, locked, transfers, logs, _) = run(Action::VoteRemove, 0, false);
        assert_eq!(status, None);
        assert_eq!(locked, bond);
        assert!(transfers.is_empty());
        assert_eq!(logs, 1);

        let (status, locked, transfers, logs, count) = run(Action::VoteApprove, 700_000_000_000_000, false);
        assert_eq!(status, Some(ProposalStatus::Expired));
        assert_eq!(locked, bond);
        assert!(transfers.is_empty());
        assert_eq!(logs, 1);
        assert_eq!(count, Some(U128(1)));

        let (status, locked, transfers, logs, count) = run(Action::VoteApprove, 0, true);
        assert_eq!(status, Some(ProposalStatus::InProgress));
        assert_eq!(locked, bond);
        assert!(transfers.is_empty());
        assert_eq!(logs, 1);
        assert_eq!(count, Some(U128(1)));
    }
}
