
#[cfg(test)]
mod views_projection_oracle {
    use super::*;
    use near_sdk::json_types::U64;
    use near_sdk::test_utils::VMContextBuilder;
    use near_sdk::testing_env;
    use std::collections::{HashMap, VecDeque};

    #[test]
    fn sparse_pages_and_missing_single_reads() {
        testing_env!(VMContextBuilder::new().build());
        let owner: AccountId = "alice.near".parse().unwrap();
        let mut contract = Contract::new(
            Config::test_config(),
            VersionedPolicy::Default(vec![owner.clone()]),
        );
        let proposal = Proposal {
            proposer: owner,
            description: "fixture".into(),
            kind: ProposalKind::Vote,
            status: ProposalStatus::InProgress,
            vote_counts: HashMap::new(),
            votes: HashMap::new(),
            submission_time: U64(0),
            last_actions_log: VecDeque::new(),
        };
        contract.proposals.insert(&1, &VersionedProposal::Latest(proposal.clone()));
        contract.proposals.insert(&3, &VersionedProposal::Latest(proposal));
        contract.last_proposal_id = 5;

        let bounty = Bounty {
            description: "fixture".into(),
            token: String::new(),
            amount: U128(1),
            times: 1,
            max_deadline: U64(10),
        };
        contract.bounties.insert(&1, &VersionedBounty::Default(bounty.clone()));
        contract.bounties.insert(&3, &VersionedBounty::Default(bounty));
        contract.last_bounty_id = 5;

        assert_eq!(contract.get_proposals(0, 4).iter().map(|p| p.id).collect::<Vec<_>>(), vec![1, 3]);
        assert_eq!(contract.get_bounties(0, 4).iter().map(|b| b.id).collect::<Vec<_>>(), vec![1, 3]);
        assert_eq!(contract.get_proposals(2, 2).iter().map(|p| p.id).collect::<Vec<_>>(), vec![3]);
        assert_eq!(contract.get_bounties(2, 2).iter().map(|b| b.id).collect::<Vec<_>>(), vec![3]);
        assert!(contract.get_proposals(5, 0).is_empty());
        assert!(contract.get_bounties(5, 0).is_empty());
        assert_eq!(contract.get_proposal(1).id, 1);
        assert_eq!(contract.get_bounty(3).id, 3);
        assert!(std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| contract.get_proposal(2))).is_err());
        assert!(std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| contract.get_bounty(2))).is_err());
        assert!(std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| contract.get_proposals(u64::MAX, 1))).is_err());
        assert!(std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| contract.get_bounties(u64::MAX, 1))).is_err());
    }

    #[test]
    fn available_balance_saturates_and_claims_default() {
        let mut context = VMContextBuilder::new();
        testing_env!(context.build());
        let owner: AccountId = "alice.near".parse().unwrap();
        let mut contract = Contract::new(
            Config::test_config(),
            VersionedPolicy::Default(vec![owner.clone()]),
        );
        contract.locked_amount = NearToken::from_yoctonear(2);
        testing_env!(context.storage_usage(32).account_balance(NearToken::from_yoctonear(0)).build());
        let reserve = env::storage_byte_cost().saturating_mul(32);
        assert_eq!(contract.get_locked_storage_amount(), reserve);
        assert_eq!(contract.get_available_amount(), NearToken::from_yoctonear(0));
        testing_env!(context.account_balance(reserve.saturating_add(NearToken::from_yoctonear(17))).build());
        assert_eq!(contract.get_available_amount(), NearToken::from_yoctonear(15));
        assert!(contract.get_bounty_claims(owner.clone()).is_empty());
        assert_eq!(contract.get_bounty_number_of_claims(7), 0);
        assert_eq!(contract.delegation_balance_ratio(owner), (U128(0), U128(0)));
    }

    #[test]
    fn policy_view_requires_upgraded_storage() {
        testing_env!(VMContextBuilder::new().build());
        let owner: AccountId = "alice.near".parse().unwrap();
        let mut contract = Contract::new(
            Config::test_config(),
            VersionedPolicy::Default(vec![owner.clone()]),
        );
        assert_eq!(contract.version(), "2.3.1");
        assert_eq!(contract.get_config().name, "Test");
        assert_eq!(contract.get_policy().roles.len(), 2);
        contract.policy.set(&VersionedPolicy::Default(vec![owner.clone()]));
        assert!(std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| contract.get_policy())).is_err());
        contract.staking_id = Some(owner.clone());
        assert_eq!(contract.get_staking_contract(), owner.to_string());
    }

    #[test]
    fn owned_staking_view_reads_without_changing_root() {
        let mut context = VMContextBuilder::new();
        testing_env!(context.build());
        let mut contract = Contract::new(
            Config::test_config(),
            VersionedPolicy::Default(vec!["alice.near".parse().unwrap()]),
        );
        contract.staking_id = Some("stake.near".parse().unwrap());
        env::state_write(&contract);
        let root_before = env::storage_read(b"STATE").unwrap();
        testing_env!(context.attached_deposit(NearToken::from_yoctonear(1)).build());
        // Native direct invocation mirrors the generated owned-view call's
        // state read. The macro, not this fixture, establishes no writeback.
        let loaded: Contract = env::state_read().unwrap();
        assert_eq!(loaded.get_staking_contract(), "stake.near");
        assert_eq!(env::storage_read(b"STATE"), Some(root_before));
    }

    #[test]
    fn factory_info_uses_first_dot_parent_only_when_key_is_missing() {
        let mut context = VMContextBuilder::new();
        context.current_account_id("dao.team.sputnik-dao.near".parse().unwrap());
        context.predecessor_account_id("other.near".parse().unwrap());
        testing_env!(context.build());
        let contract = Contract::new(
            Config::test_config(),
            VersionedPolicy::Default(vec![]),
        );
        assert_eq!(contract.get_factory_info().factory_id.as_str(), "other.near");
        assert!(env::storage_remove(b"FACTORY"));
        let fallback = contract.get_factory_info();
        assert_eq!(fallback.factory_id.as_str(), "team.sputnik-dao.near");
        assert!(fallback.auto_update);
        env::storage_write(b"FACTORY", &[255]);
        assert!(std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| contract.get_factory_info())).is_err());
        let encoded = near_sdk::borsh::to_vec(&FactoryInfo {
            factory_id: "factory.near".parse().unwrap(), auto_update: true,
        }).unwrap();
        let mut invalid_bool = encoded.clone();
        *invalid_bool.last_mut().unwrap() = 2;
        env::storage_write(b"FACTORY", &invalid_bool);
        assert!(std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| contract.get_factory_info())).is_err());
        let mut trailing = encoded;
        trailing.push(0);
        env::storage_write(b"FACTORY", &trailing);
        assert!(std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| contract.get_factory_info())).is_err());
        assert!(env::storage_remove(b"FACTORY"));
        testing_env!(context.current_account_id("near".parse().unwrap()).build());
        assert!(std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| contract.get_factory_info())).is_err());
    }
}
