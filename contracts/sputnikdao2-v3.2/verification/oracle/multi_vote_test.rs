
#[cfg(test)]
mod multi_vote_projection_oracle {
    use super::*;
    use crate::policy::{WeightKind, WeightOrRatio};
    use near_sdk::test_utils::VMContextBuilder;
    use near_sdk::testing_env;
    use std::collections::{HashMap, HashSet, VecDeque};

    fn fresh_proposal(account: &AccountId) -> Proposal {
        Proposal {
            proposer: account.clone(),
            description: "two role fixture".into(),
            kind: ProposalKind::Vote,
            status: ProposalStatus::InProgress,
            vote_counts: HashMap::new(),
            votes: HashMap::new(),
            submission_time: U64(0),
            last_actions_log: VecDeque::new(),
        }
    }

    #[test]
    fn two_allowed_roles_use_distinct_weights_and_expiry_follows_counting() {
        let account: AccountId = "alice.near".parse().unwrap();
        let mut context = VMContextBuilder::new();
        testing_env!(context.build());
        let mut policy = default_policy(vec![account.clone()]);
        policy.roles.push(RolePermission {
            name: "token".into(),
            kind: RoleKind::Group(HashSet::from([account.clone()])),
            permissions: HashSet::from(["*:VoteApprove".to_string()]),
            vote_policy: HashMap::from([("vote".to_string(), VotePolicy {
                weight_kind: WeightKind::TokenWeight,
                quorum: U128(0),
                threshold: WeightOrRatio::Weight(U128(5)),
            })]),
        });
        let (roles, allowed) = policy.can_execute_action(
            UserInfo { account_id: account.clone(), amount: 7 },
            &ProposalKind::Vote, &Action::VoteApprove,
        );
        assert!(allowed);
        assert_eq!(roles.len(), 2);
        assert!(roles.contains(&"council".to_string()));
        assert!(roles.contains(&"token".to_string()));

        let mut proposal = fresh_proposal(&account);
        proposal.update_votes(&account, &roles, Vote::Approve, &policy, 7);
        assert_eq!(proposal.vote_counts["council"][0], U128(1));
        assert_eq!(proposal.vote_counts["token"][0], U128(7));
        assert!(proposal.votes.contains_key(&account));
        assert_eq!(policy.proposal_status(&proposal, roles.clone(), 10), ProposalStatus::Approved);

        // The source accepts and counts a vote before checking expiry.
        policy.proposal_period = U64(1);
        testing_env!(context.block_timestamp(2).build());
        let mut expired = fresh_proposal(&account);
        expired.update_votes(&account, &roles, Vote::Approve, &policy, 7);
        assert_eq!(expired.vote_counts["council"][0], U128(1));
        assert_eq!(expired.vote_counts["token"][0], U128(7));
        assert_eq!(policy.proposal_status(&expired, roles, 10), ProposalStatus::Expired);
    }

    #[test]
    fn duplicate_name_uses_later_permissions_but_first_voting_rules() {
        testing_env!(VMContextBuilder::new().build());
        let account: AccountId = "alice.near".parse().unwrap();
        let mut policy = default_policy(vec![account.clone()]);
        policy.roles[1].permissions.clear();
        policy.roles.push(RolePermission {
            name: "council".into(),
            kind: RoleKind::Group(HashSet::from([account.clone()])),
            permissions: HashSet::from(["*:VoteApprove".to_string()]),
            vote_policy: HashMap::from([("vote".to_string(), VotePolicy {
                weight_kind: WeightKind::TokenWeight,
                quorum: U128(0),
                threshold: WeightOrRatio::Ratio(
                    1, std::num::NonZeroU64::new(1).unwrap()),
            })]),
        });
        let (roles, allowed) = policy.can_execute_action(
            UserInfo { account_id: account.clone(), amount: 7 },
            &ProposalKind::Vote, &Action::VoteApprove,
        );
        assert!(allowed);
        assert_eq!(roles, vec!["council"]);
        assert!(!policy.is_token_weighted(&"council".to_string(), &"vote".to_string()));

        let mut proposal = fresh_proposal(&account);
        proposal.update_votes(&account, &roles, Vote::Approve, &policy, 7);
        assert_eq!(proposal.vote_counts["council"][0], U128(1));
        assert_eq!(policy.proposal_status(&proposal, roles, u128::MAX),
            ProposalStatus::Approved);
    }

    #[test]
    fn role_matching_uses_member_threshold_and_group_set_membership() {
        let alice: AccountId = "alice.near".parse().unwrap();
        let bob: AccountId = "bob.near".parse().unwrap();
        let at_threshold = UserInfo { account_id: alice.clone(), amount: 7 };
        let below_threshold = UserInfo { account_id: alice.clone(), amount: 6 };
        assert!(RoleKind::Everyone.match_user(&below_threshold));
        assert!(RoleKind::Member(U128(7)).match_user(&at_threshold));
        assert!(!RoleKind::Member(U128(7)).match_user(&below_threshold));
        let group = RoleKind::Group(HashSet::from([alice.clone(), alice]));
        assert_eq!(group.get_role_size(), Some(1));
        assert!(group.match_user(&at_threshold));
        assert!(!group.match_user(&UserInfo { account_id: bob, amount: 7 }));
    }
}
