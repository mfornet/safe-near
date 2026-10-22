
#[cfg(test)]
mod migration_wire_projection_oracle {
    use super::*;
    use near_sdk::test_utils::VMContextBuilder;
    use near_sdk::testing_env;

    #[test]
    fn v1_root_gains_only_empty_log_and_keeps_legacy_policy_bytes() {
        let dao: AccountId = "dao.near".parse().unwrap();
        let council: AccountId = "alice.near".parse().unwrap();
        let mut context = VMContextBuilder::new();
        context.current_account_id(dao.clone());
        context.predecessor_account_id(dao);
        testing_env!(context.build());

        let mut current = Contract::new(
            Config::test_config(),
            VersionedPolicy::Default(vec![council.clone()]),
        );
        // `new` upgraded the value at key 1. A legacy snapshot may still
        // contain Default at that key, which migration does not rewrite.
        current.policy.set(&VersionedPolicy::Default(vec![council]));
        let policy_before = env::storage_read(&[1]).unwrap();
        assert_eq!(policy_before[0], 0); // Default enum discriminant
        let old = ContractV1 {
            config: current.config,
            policy: current.policy,
            locked_amount: current.locked_amount,
            staking_id: current.staking_id,
            total_delegation_amount: current.total_delegation_amount,
            delegations: current.delegations,
            last_proposal_id: current.last_proposal_id,
            proposals: current.proposals,
            last_bounty_id: current.last_bounty_id,
            bounties: current.bounties,
            bounty_claimers: current.bounty_claimers,
            bounty_claims_count: current.bounty_claims_count,
            blobs: current.blobs,
        };
        let old_bytes = near_sdk::borsh::to_vec(&old).unwrap();
        assert_eq!(old_bytes.len(), 89);
        env::state_write(&old);
        env::storage_remove(b"STATEVERSION");

        let migrated = Contract::migrate();
        let migrated_bytes = near_sdk::borsh::to_vec(&migrated).unwrap();
        assert_eq!(migrated_bytes.len(), 93);
        assert_eq!(&migrated_bytes[..89], old_bytes.as_slice());
        assert_eq!(&migrated_bytes[89..], &[0, 0, 0, 0]);
        assert_eq!(env::storage_read(b"STATEVERSION"), Some(vec![1]));
        assert_eq!(env::storage_read(&[1]), Some(policy_before));
        assert!(std::panic::catch_unwind(std::panic::AssertUnwindSafe(||
            migrated.get_policy())).is_err());
    }

    #[test]
    fn v2_direct_migration_reads_existing_root_without_version_rewrite() {
        let dao: AccountId = "dao.near".parse().unwrap();
        let mut context = VMContextBuilder::new();
        context.current_account_id(dao.clone());
        context.predecessor_account_id(dao);
        testing_env!(context.build());

        let contract = Contract::new(
            Config::test_config(),
            VersionedPolicy::Default(vec!["alice.near".parse().unwrap()]),
        );
        env::state_write(&contract);
        let root_before = env::storage_read(b"STATE").unwrap();
        let version_before = env::storage_read(b"STATEVERSION").unwrap();
        assert_eq!(version_before, vec![1]);

        let migrated = Contract::migrate();
        assert_eq!(near_sdk::borsh::to_vec(&migrated).unwrap(), root_before);
        assert_eq!(env::storage_read(b"STATE"), Some(root_before.clone()));
        assert_eq!(env::storage_read(b"STATEVERSION"), Some(version_before));
        // The generated #[init(ignore_state)] wrapper writes the returned
        // state; this direct call deliberately leaves that step explicit.
        env::state_write(&migrated);
        assert_eq!(env::storage_read(b"STATE"), Some(root_before));
    }

    #[test]
    fn malformed_version_bytes_abort_migration() {
        let dao: AccountId = "dao.near".parse().unwrap();
        let mut context = VMContextBuilder::new();
        context.current_account_id(dao.clone());
        context.predecessor_account_id(dao);
        testing_env!(context.build());

        let contract = Contract::new(
            Config::test_config(),
            VersionedPolicy::Default(vec!["alice.near".parse().unwrap()]),
        );
        env::state_write(&contract);

        for malformed in [vec![2], vec![1, 0]] {
            env::storage_write(b"STATEVERSION", &malformed);
            assert!(std::panic::catch_unwind(std::panic::AssertUnwindSafe(||
                Contract::migrate())).is_err());
        }
    }

    #[test]
    fn v2_migration_preserves_unreadable_policy_key() {
        let dao: AccountId = "dao.near".parse().unwrap();
        let mut context = VMContextBuilder::new();
        context.current_account_id(dao.clone());
        context.predecessor_account_id(dao);
        testing_env!(context.build());

        let mut contract = Contract::new(
            Config::test_config(),
            VersionedPolicy::Default(vec!["alice.near".parse().unwrap()]),
        );
        contract.policy.set(&VersionedPolicy::Default(
            vec!["alice.near".parse().unwrap()],
        ));
        env::state_write(&contract);
        let policy_before = env::storage_read(&[1]).unwrap();
        assert_eq!(policy_before[0], 0);

        let migrated = Contract::migrate();
        assert_eq!(env::storage_read(&[1]), Some(policy_before));
        assert!(std::panic::catch_unwind(std::panic::AssertUnwindSafe(||
            migrated.get_policy())).is_err());
    }
}
