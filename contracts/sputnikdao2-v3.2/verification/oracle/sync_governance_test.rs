
#[cfg(test)]
mod sync_governance_projection_oracle {
    use super::*;
    use near_sdk::mock::MockAction;
    use near_sdk::test_utils::{get_created_receipts, VMContextBuilder};
    use near_sdk::testing_env;
    use std::collections::{HashMap, HashSet, VecDeque};

    fn setup() -> Contract {
        let mut context = VMContextBuilder::new();
        context.current_account_id("dao.sputnik-dao.near".parse().unwrap());
        context.predecessor_account_id("alice.near".parse().unwrap());
        testing_env!(context.build());
        Contract::new(Config::test_config(),
            VersionedPolicy::Default(vec!["alice.near".parse().unwrap()]))
    }

    fn approve(contract: &mut Contract, kind: ProposalKind) {
        let id = contract.last_proposal_id;
        contract.proposals.insert(&id, &VersionedProposal::Latest(Proposal {
            proposer: "alice.near".parse().unwrap(),
            description: "governance".into(),
            kind: kind.clone(),
            status: ProposalStatus::InProgress,
            vote_counts: HashMap::new(),
            votes: HashMap::new(),
            submission_time: U64(0),
            last_actions_log: VecDeque::new(),
        }));
        contract.last_proposal_id += 1;
        contract.locked_amount = NearToken::from_near(1);
        contract.act_proposal(id, Action::VoteApprove, kind, None);
    }

    fn has_refund(amount: NearToken) -> bool {
        get_created_receipts().iter().any(|receipt|
            receipt.receiver_id.as_str() == "alice.near" &&
            receipt.actions.iter().any(|action| matches!(action,
                MockAction::Transfer { deposit, .. } if *deposit == amount)))
    }

    fn has_callback() -> bool {
        get_created_receipts().iter().any(|receipt|
            receipt.receiver_id.as_str() == "dao.sputnik-dao.near" &&
            receipt.actions.iter().any(|action| matches!(action,
                MockAction::FunctionCallWeight { method_name, .. }
                    if method_name == b"on_proposal_callback")))
    }

    #[test]
    fn policy_replacement_uses_old_bond_for_immediate_refund() {
        let mut contract = setup();
        let mut new_policy = contract.policy.get().unwrap().to_policy();
        new_policy.proposal_bond = NearToken::from_near(2);
        let replacement = VersionedPolicy::Current(new_policy);
        approve(&mut contract, ProposalKind::ChangePolicy {
            policy: replacement.clone(),
        });
        assert_eq!(env::storage_read(&[1]).unwrap(),
            near_sdk::borsh::to_vec(&replacement).unwrap());
        assert_eq!(contract.get_policy().proposal_bond,
            NearToken::from_near(2));
        assert_eq!(contract.policy.get().unwrap().to_policy().proposal_bond,
            NearToken::from_near(2));
        assert_eq!(contract.locked_amount, NearToken::from_yoctonear(0));
        assert!(has_refund(NearToken::from_near(1)));
        assert!(!has_callback());
    }

    #[test]
    fn current_policy_replacement_can_store_ratio_with_increment_overflow() {
        let mut contract = setup();
        approve(&mut contract, ProposalKind::SetStakingContract {
            staking_id: "staking.near".parse().unwrap(),
        });
        let mut replacement = contract.policy.get().unwrap().to_policy();
        replacement.default_vote_policy.threshold = crate::policy::WeightOrRatio::Ratio(
            1, std::num::NonZeroU64::new(1).unwrap());
        let mut unsafe_role = replacement.roles[1].clone();
        unsafe_role.name = "unsafe".into();
        unsafe_role.kind = RoleKind::Member(U128(0));
        replacement.roles.push(unsafe_role);
        replacement.roles[1].permissions.clear();
        let kind = ProposalKind::ChangePolicy {
            policy: VersionedPolicy::Current(replacement.clone()),
        };
        let mut context = VMContextBuilder::new();
        context.current_account_id("dao.sputnik-dao.near".parse().unwrap());
        context.predecessor_account_id("alice.near".parse().unwrap());
        context.attached_deposit(NearToken::from_near(1));
        testing_env!(context.build());
        let id = contract.add_proposal(ProposalInput {
            description: "ratio arithmetic boundary".into(),
            kind: kind.clone(),
        });
        testing_env!(context.attached_deposit(NearToken::from_yoctonear(0)).build());
        contract.act_proposal(id, Action::VoteApprove, kind, None);
        let stored = contract.get_policy();
        assert_eq!(stored.default_vote_policy.threshold,
            replacement.default_vote_policy.threshold);
        assert!(std::panic::catch_unwind(||
            stored.default_vote_policy.threshold.to_weight(u128::MAX)
        ).is_err());

        let mut staking_context = VMContextBuilder::new();
        staking_context.current_account_id("dao.sputnik-dao.near".parse().unwrap());
        staking_context.predecessor_account_id("staking.near".parse().unwrap());
        staking_context.attached_deposit(env::storage_byte_cost().saturating_mul(16));
        testing_env!(staking_context.build());
        contract.register_delegation(&"alice.near".parse().unwrap());
        testing_env!(staking_context.attached_deposit(NearToken::from_yoctonear(0)).build());
        let (_, balance, total) = contract.delegate(
            &"alice.near".parse().unwrap(), U128(u128::MAX));
        assert_eq!(balance, U128(u128::MAX));
        assert_eq!(total, U128(u128::MAX));
        assert_eq!(contract.total_delegation_amount, u128::MAX);

        let mut voter_context = VMContextBuilder::new();
        voter_context.current_account_id("dao.sputnik-dao.near".parse().unwrap());
        voter_context.predecessor_account_id("alice.near".parse().unwrap());
        voter_context.attached_deposit(NearToken::from_near(1));
        testing_env!(voter_context.build());
        let vote_id = contract.add_proposal(ProposalInput {
            description: "unsafe vote threshold".into(),
            kind: ProposalKind::Vote,
        });
        testing_env!(voter_context.attached_deposit(NearToken::from_yoctonear(0)).build());
        assert!(std::panic::catch_unwind(std::panic::AssertUnwindSafe(||
            contract.act_proposal(vote_id, Action::VoteApprove,
                ProposalKind::Vote, None)
        )).is_err());
        testing_env!(voter_context.attached_deposit(NearToken::from_near(1)).build());
        let finalize_id = contract.add_proposal(ProposalInput {
            description: "unsafe finalize threshold".into(),
            kind: ProposalKind::Vote,
        });
        testing_env!(voter_context.attached_deposit(NearToken::from_yoctonear(0)).build());
        assert!(std::panic::catch_unwind(std::panic::AssertUnwindSafe(||
            contract.act_proposal(finalize_id, Action::Finalize,
                ProposalKind::Vote, None)
        )).is_err());

        let mut vote_counts = HashMap::new();
        vote_counts.insert("council".into(), [U128(1), U128(0), U128(0)]);
        let mut proposal = Proposal {
            proposer: "alice.near".parse().unwrap(),
            description: "ordered arithmetic".into(),
            kind: ProposalKind::Vote,
            status: ProposalStatus::InProgress,
            vote_counts,
            votes: HashMap::new(),
            submission_time: U64(0),
            last_actions_log: VecDeque::new(),
        };
        assert_eq!(stored.proposal_status(&proposal,
            vec!["council".into(), "unsafe".into()], contract.total_delegation_amount),
            ProposalStatus::Approved);
        assert!(std::panic::catch_unwind(|| stored.proposal_status(&proposal,
            vec!["unsafe".into(), "council".into()],
            contract.total_delegation_amount)).is_err());
        testing_env!(staking_context.block_timestamp(stored.proposal_period.0 + 1).build());
        assert_eq!(stored.proposal_status(&proposal,
            vec!["unsafe".into()], contract.total_delegation_amount),
            ProposalStatus::Expired);
        proposal.submission_time = U64(u64::MAX);
        assert!(std::panic::catch_unwind(|| stored.proposal_status(&proposal,
            vec!["unsafe".into()], contract.total_delegation_amount)).is_err());
    }

    #[test]
    fn default_policy_creation_is_rejected_but_unchecked_execution_stores_it() {
        let mut contract = setup();
        let legacy = VersionedPolicy::Default(vec!["alice.near".parse().unwrap()]);
        let replacement = ProposalKind::ChangePolicy {
            policy: legacy.clone(),
        };
        let mut context = VMContextBuilder::new();
        context.current_account_id("dao.sputnik-dao.near".parse().unwrap());
        context.predecessor_account_id("alice.near".parse().unwrap());
        context.attached_deposit(NearToken::from_near(1));
        testing_env!(context.build());
        assert!(std::panic::catch_unwind(std::panic::AssertUnwindSafe(||
            contract.add_proposal(ProposalInput {
                description: "invalid policy".into(), kind: replacement.clone(),
            }))).is_err());
        assert_eq!(contract.last_proposal_id, 0);
        assert!(matches!(contract.policy.get(), Some(VersionedPolicy::Current(_))));
        testing_env!(context.attached_deposit(NearToken::from_yoctonear(0)).build());
        // `approve` inserts a synthetic proposal directly into the map and
        // thereby bypasses the public creation-time version check.
        let proposal_id = contract.last_proposal_id;
        approve(&mut contract, replacement);
        assert!(matches!(contract.policy.get(), Some(VersionedPolicy::Default(_))));
        assert_eq!(env::storage_read(&[1]).unwrap(),
            near_sdk::borsh::to_vec(&legacy).unwrap());
        if let Some(VersionedProposal::Latest(stored)) =
            contract.proposals.get(&proposal_id) {
            assert_eq!(stored.status, ProposalStatus::Approved);
            assert_eq!(stored.votes.len(), 1);
            assert_eq!(stored.last_actions_log.len(), 1);
        } else {
            panic!("approved legacy-policy proposal was not stored");
        }
        assert_eq!(contract.actions_log.len(), 1);
        assert!(std::panic::catch_unwind(std::panic::AssertUnwindSafe(||
            contract.get_policy())).is_err());
        assert!(std::panic::catch_unwind(std::panic::AssertUnwindSafe(||
            contract.act_proposal(proposal_id, Action::MoveToHub,
                ProposalKind::ChangePolicy { policy: legacy.clone() }, None)
        )).is_err());
        assert!(std::panic::catch_unwind(std::panic::AssertUnwindSafe(||
            contract.add_proposal(ProposalInput {
                description: "after legacy replacement".into(),
                kind: ProposalKind::Vote,
            }))).is_err());
    }

    #[test]
    fn change_policy_cannot_repair_unreadable_current_policy() {
        let mut contract = setup();
        let replacement = ProposalKind::ChangePolicy {
            policy: VersionedPolicy::Current(
                contract.policy.get().unwrap().to_policy()),
        };
        env::storage_write(&[1], &[0xff]);
        assert!(std::panic::catch_unwind(std::panic::AssertUnwindSafe(||
            approve(&mut contract, replacement))).is_err());
        assert_eq!(env::storage_read(&[1]), Some(vec![0xff]));
    }

    #[test]
    fn parameter_patch_preserves_unspecified_fields_and_refunds_old_bond() {
        let mut contract = setup();
        let old = contract.policy.get().unwrap().to_policy();
        approve(&mut contract, ProposalKind::ChangePolicyUpdateParameters {
            parameters: PolicyParameters {
                proposal_bond: Some(NearToken::from_near(2)),
                proposal_period: None,
                bounty_bond: None,
                bounty_forgiveness_period: None,
            },
        });
        let new = contract.policy.get().unwrap().to_policy();
        assert_eq!(new.proposal_bond, NearToken::from_near(2));
        assert_eq!(new.proposal_period, old.proposal_period);
        assert_eq!(new.bounty_bond, old.bounty_bond);
        assert_eq!(new.bounty_forgiveness_period, old.bounty_forgiveness_period);
        assert_eq!(contract.locked_amount, NearToken::from_yoctonear(0));
        assert!(has_refund(NearToken::from_near(1)));
        assert!(!has_callback());
    }

    #[test]
    fn public_period_patch_can_make_later_vote_and_finalize_overflow() {
        let mut contract = setup();
        let mut context = VMContextBuilder::new();
        context.current_account_id("dao.sputnik-dao.near".parse().unwrap());
        context.predecessor_account_id("alice.near".parse().unwrap());
        context.block_timestamp(1);
        context.attached_deposit(NearToken::from_near(1));
        testing_env!(context.build());
        let patch_kind = ProposalKind::ChangePolicyUpdateParameters {
            parameters: PolicyParameters {
                proposal_bond: None,
                proposal_period: Some(U64(u64::MAX)),
                bounty_bond: None,
                bounty_forgiveness_period: None,
            },
        };
        let patch_id = contract.add_proposal(ProposalInput {
            description: "max period".into(), kind: patch_kind.clone(),
        });
        testing_env!(context.attached_deposit(NearToken::from_yoctonear(0)).build());
        contract.act_proposal(patch_id, Action::VoteApprove, patch_kind, None);
        assert_eq!(contract.get_policy().proposal_period, U64(u64::MAX));

        testing_env!(context.attached_deposit(NearToken::from_near(1)).build());
        let vote_id = contract.add_proposal(ProposalInput {
            description: "overflow vote".into(), kind: ProposalKind::Vote,
        });
        testing_env!(context.attached_deposit(NearToken::from_yoctonear(0)).build());
        assert!(std::panic::catch_unwind(std::panic::AssertUnwindSafe(||
            contract.act_proposal(vote_id, Action::VoteApprove,
                ProposalKind::Vote, None)
        )).is_err());

        testing_env!(context.attached_deposit(NearToken::from_near(1)).build());
        let finalize_id = contract.add_proposal(ProposalInput {
            description: "overflow finalize".into(), kind: ProposalKind::Vote,
        });
        testing_env!(context.attached_deposit(NearToken::from_yoctonear(0)).build());
        assert!(std::panic::catch_unwind(std::panic::AssertUnwindSafe(||
            contract.act_proposal(finalize_id, Action::Finalize,
                ProposalKind::Vote, None)
        )).is_err());
    }

    #[test]
    fn staking_execution_rechecks_one_time_guard() {
        let mut contract = setup();
        let first = ProposalKind::SetStakingContract {
            staking_id: "staking.near".parse().unwrap(),
        };
        let second = ProposalKind::SetStakingContract {
            staking_id: "other.near".parse().unwrap(),
        };
        let mut context = VMContextBuilder::new();
        context.current_account_id("dao.sputnik-dao.near".parse().unwrap());
        context.predecessor_account_id("alice.near".parse().unwrap());
        context.attached_deposit(NearToken::from_near(1));
        testing_env!(context.build());
        let first_id = contract.add_proposal(ProposalInput {
            description: "first staking".into(), kind: first.clone(),
        });
        let second_id = contract.add_proposal(ProposalInput {
            description: "second staking".into(), kind: second.clone(),
        });
        assert_eq!((first_id, second_id), (0, 1));
        assert_eq!(contract.locked_amount, NearToken::from_near(2));
        testing_env!(context.attached_deposit(NearToken::from_yoctonear(0)).build());
        contract.act_proposal(first_id, Action::VoteApprove, first, None);
        assert_eq!(contract.staking_id.as_ref().unwrap().as_str(), "staking.near");
        assert!(has_refund(NearToken::from_near(1)));
        assert!(!has_callback());

        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(||
            contract.act_proposal(second_id, Action::VoteApprove, second, None)));
        assert!(result.is_err());
        assert_eq!(contract.staking_id.as_ref().unwrap().as_str(), "staking.near");
    }

    #[test]
    fn duplicate_role_update_replaces_only_first_matching_entry() {
        let mut contract = setup();
        let mut policy = contract.policy.get().unwrap().to_policy();
        let mut first = policy.roles[1].clone();
        first.name = "duplicate".into();
        first.kind = RoleKind::Group(HashSet::new());
        let mut second = first.clone();
        second.permissions.insert("marker:VoteApprove".into());
        policy.roles.push(first.clone());
        policy.roles.push(second.clone());
        contract.policy.set(&VersionedPolicy::Current(policy));

        let mut replacement = first;
        replacement.permissions.insert("new:VoteApprove".into());
        approve(&mut contract, ProposalKind::ChangePolicyAddOrUpdateRole {
            role: replacement.clone(),
        });
        let updated = contract.policy.get().unwrap().to_policy();
        assert_eq!(updated.roles.len(), 4);
        assert_eq!(updated.roles[2], replacement);
        assert_eq!(updated.roles[3], second);
        assert!(has_refund(NearToken::from_near(1)));
        assert!(!has_callback());
    }

    #[test]
    fn duplicate_role_removal_removes_only_first_matching_entry() {
        let mut contract = setup();
        let mut policy = contract.policy.get().unwrap().to_policy();
        let mut first = policy.roles[1].clone();
        first.name = "duplicate".into();
        first.kind = RoleKind::Group(HashSet::new());
        let mut second = first.clone();
        second.permissions.insert("marker:VoteApprove".into());
        policy.roles.push(first);
        policy.roles.push(second.clone());
        contract.policy.set(&VersionedPolicy::Current(policy));

        approve(&mut contract, ProposalKind::ChangePolicyRemoveRole {
            role: "duplicate".into(),
        });
        let roles = contract.policy.get().unwrap().to_policy().roles;
        assert_eq!(roles.len(), 3);
        assert_eq!(roles[2], second);
        assert!(has_refund(NearToken::from_near(1)));
    }

    #[test]
    fn group_member_add_and_remove_mutate_only_target_group() {
        let mut contract = setup();
        let mut policy = contract.policy.get().unwrap().to_policy();
        let mut target = policy.roles[1].clone();
        target.name = "target".into();
        target.kind = RoleKind::Group(HashSet::new());
        policy.roles.push(target);
        contract.policy.set(&VersionedPolicy::Current(policy));
        approve(&mut contract, ProposalKind::AddMemberToRole {
            member_id: "bob.near".parse().unwrap(), role: "target".into(),
        });
        let roles = contract.policy.get().unwrap().to_policy().roles;
        let bob: AccountId = "bob.near".parse().unwrap();
        assert!(matches!(&roles[2].kind, RoleKind::Group(members)
            if members.contains(&bob)));
        assert!(has_refund(NearToken::from_near(1)));
        approve(&mut contract, ProposalKind::AddMemberToRole {
            member_id: bob.clone(), role: "target".into(),
        });
        let roles = contract.policy.get().unwrap().to_policy().roles;
        assert!(matches!(&roles[2].kind, RoleKind::Group(members)
            if members.len() == 1 && members.contains(&bob)));

        let mut contract = setup();
        let mut policy = contract.policy.get().unwrap().to_policy();
        let mut target = policy.roles[1].clone();
        target.name = "target".into();
        target.kind = RoleKind::Group(HashSet::from(["bob.near".parse().unwrap()]));
        policy.roles.push(target);
        contract.policy.set(&VersionedPolicy::Current(policy));
        approve(&mut contract, ProposalKind::RemoveMemberFromRole {
            member_id: "bob.near".parse().unwrap(), role: "target".into(),
        });
        let roles = contract.policy.get().unwrap().to_policy().roles;
        assert!(matches!(&roles[2].kind, RoleKind::Group(members) if members.is_empty()));
        assert!(has_refund(NearToken::from_near(1)));
        approve(&mut contract, ProposalKind::RemoveMemberFromRole {
            member_id: "bob.near".parse().unwrap(), role: "target".into(),
        });
        let roles = contract.policy.get().unwrap().to_policy().roles;
        assert!(matches!(&roles[2].kind, RoleKind::Group(members) if members.is_empty()));
    }

    #[test]
    fn wrong_kind_first_duplicate_is_noop_but_refunds() {
        let mut contract = setup();
        let mut policy = contract.policy.get().unwrap().to_policy();
        let mut first = policy.roles[1].clone();
        first.name = "duplicate".into();
        first.kind = RoleKind::Everyone;
        first.permissions.clear();
        let mut second = first.clone();
        second.kind = RoleKind::Group(HashSet::new());
        policy.roles.push(first);
        policy.roles.push(second);
        let original = policy.roles.clone();
        contract.policy.set(&VersionedPolicy::Current(policy));

        approve(&mut contract, ProposalKind::AddMemberToRole {
            member_id: "bob.near".parse().unwrap(), role: "duplicate".into(),
        });
        assert_eq!(contract.policy.get().unwrap().to_policy().roles, original);
        assert!(near_sdk::test_utils::get_logs().iter().any(|line|
            line == "ERR_ROLE_WRONG_KIND:duplicate"));
        assert!(has_refund(NearToken::from_near(1)));
        assert!(!has_callback());
    }

    #[test]
    fn missing_role_removal_is_noop_but_refunds() {
        let mut contract = setup();
        let original = contract.policy.get().unwrap().to_policy().roles;
        approve(&mut contract, ProposalKind::ChangePolicyRemoveRole {
            role: "absent".into(),
        });
        assert_eq!(contract.policy.get().unwrap().to_policy().roles, original);
        assert!(near_sdk::test_utils::get_logs().iter().any(|line|
            line == "ERR_ROLE_NOT_FOUND:absent"));
        assert!(has_refund(NearToken::from_near(1)));
        assert!(!has_callback());
    }

    #[test]
    fn default_vote_policy_update_refunds_immediately() {
        let mut contract = setup();
        let mut voting = contract.policy.get().unwrap().to_policy().default_vote_policy;
        voting.quorum = U128(3);
        approve(&mut contract, ProposalKind::ChangePolicyUpdateDefaultVotePolicy {
            vote_policy: voting,
        });
        assert_eq!(contract.policy.get().unwrap().to_policy().default_vote_policy.quorum,
            U128(3));
        assert!(has_refund(NearToken::from_near(1)));
        assert!(!has_callback());
    }

    #[test]
    fn config_update_replaces_all_fields_and_refunds_immediately() {
        let mut contract = setup();
        env::storage_write(&[0], &[0xff]);
        let proposal_id = contract.last_proposal_id;
        let config = Config {
            name: "New DAO".into(),
            purpose: "New purpose".into(),
            metadata: vec![1, 2, 3].into(),
        };
        approve(&mut contract, ProposalKind::ChangeConfig {
            config: config.clone(),
        });
        assert_eq!(contract.config.get().unwrap(), config);
        assert_eq!(env::storage_read(&[0]).unwrap(),
            near_sdk::borsh::to_vec(&config).unwrap());
        assert_eq!(contract.get_config(), config);
        if let Some(VersionedProposal::Latest(stored)) =
            contract.proposals.get(&proposal_id) {
            assert_eq!(stored.status, ProposalStatus::Approved);
            assert_eq!(stored.votes.len(), 1);
            assert_eq!(stored.last_actions_log.len(), 1);
        } else {
            panic!("approved config proposal was not stored");
        }
        assert_eq!(contract.actions_log.len(), 1);
        assert_eq!(contract.locked_amount, NearToken::from_yoctonear(0));
        assert!(has_refund(NearToken::from_near(1)));
        assert!(!has_callback());
    }

    #[test]
    fn factory_info_update_repairs_raw_key_and_disables_auto_update_flag() {
        let mut contract = setup();
        env::storage_write(b"FACTORY", &[0xff]);
        let proposal_id = contract.last_proposal_id;
        let info = FactoryInfo {
            factory_id: "factory.near".parse().unwrap(), auto_update: false,
        };
        approve(&mut contract, ProposalKind::FactoryInfoUpdate {
            factory_info: info.clone(),
        });
        assert_eq!(contract.get_factory_info(), info);
        assert_eq!(env::storage_read(b"FACTORY").unwrap(),
            near_sdk::borsh::to_vec(&info).unwrap());
        assert!(matches!(contract.proposals.get(&proposal_id),
            Some(VersionedProposal::Latest(Proposal {
                status: ProposalStatus::Approved, ..
            }))));
        if let Some(VersionedProposal::Latest(stored)) =
            contract.proposals.get(&proposal_id) {
            assert_eq!(stored.votes.len(), 1);
            assert_eq!(stored.last_actions_log.len(), 1);
        } else {
            panic!("approved proposal was not stored");
        }
        assert_eq!(contract.actions_log.len(), 1);
        assert_eq!(contract.locked_amount, NearToken::from_yoctonear(0));
        assert!(has_refund(NearToken::from_near(1)));
        assert!(!has_callback());
    }

    #[test]
    fn enabled_factory_info_update_authorizes_raw_update() {
        let mut contract = setup();
        approve(&mut contract, ProposalKind::FactoryInfoUpdate {
            factory_info: FactoryInfo {
                factory_id: "factory.near".parse().unwrap(), auto_update: true,
            },
        });
        // The manual raw export reads FACTORY, even if policy conversion
        // would now fail in generated governance methods.
        contract.policy.set(&VersionedPolicy::Default(
            vec!["alice.near".parse().unwrap()],
        ));
        let mut context = VMContextBuilder::new();
        context.current_account_id("dao.sputnik-dao.near".parse().unwrap());
        context.predecessor_account_id("factory.near".parse().unwrap());
        context.context.input = vec![1, 2, 3].into();
        context.attached_deposit(NearToken::from_yoctonear(1));
        testing_env!(context.build());
        // The manual raw export reads FACTORY but does not decode STATE.
        env::storage_remove(b"STATE");
        assert!(env::storage_read(b"STATE").is_none());
        crate::upgrade::update();
        assert!(get_created_receipts().iter().any(|receipt|
            receipt.receiver_id.as_str() == "dao.sputnik-dao.near" &&
            receipt.actions.iter().any(|action| matches!(action,
                MockAction::UseGlobalContract { .. })) &&
            receipt.actions.iter().any(|action| matches!(action,
                MockAction::FunctionCallWeight { method_name, .. }
                    if method_name == b"migrate"))));
    }

    #[test]
    fn synthetic_failed_factory_proposal_can_finalize_and_refund_again() {
        let mut contract = setup();
        let info = FactoryInfo {
            factory_id: "factory.near".parse().unwrap(), auto_update: false,
        };
        let kind = ProposalKind::FactoryInfoUpdate {
            factory_info: info.clone(),
        };
        approve(&mut contract, kind.clone());
        let id = contract.last_proposal_id - 1;
        // A synchronous FactoryInfoUpdate does not itself enter Failed.
        // Inject that status to exercise Finalize's re-execution branch.
        let Some(VersionedProposal::Latest(mut proposal)) =
            contract.proposals.get(&id) else { panic!("missing proposal") };
        proposal.status = ProposalStatus::Failed;
        contract.proposals.insert(&id, &VersionedProposal::Latest(proposal));
        env::storage_write(b"FACTORY", &[0xff]);

        contract.act_proposal(id, Action::Finalize, kind, None);
        assert_eq!(contract.get_factory_info(), info);
        assert_eq!(contract.get_proposal(id).proposal.status,
            ProposalStatus::Approved);
        assert_eq!(contract.actions_log.len(), 2);
        assert_eq!(contract.locked_amount, NearToken::from_yoctonear(0));
        let refunds = get_created_receipts().iter().filter(|receipt|
            receipt.receiver_id.as_str() == "alice.near" &&
            receipt.actions.iter().any(|action| matches!(action,
                MockAction::Transfer { deposit, .. }
                    if *deposit == NearToken::from_near(1)))).count();
        assert_eq!(refunds, 2);
    }
}
