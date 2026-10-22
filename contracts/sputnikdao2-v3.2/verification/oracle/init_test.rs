
#[cfg(test)]
mod initialization_projection_oracle {
    use super::*;
    use near_sdk::test_utils::VMContextBuilder;
    use near_sdk::testing_env;

    #[test]
    fn action_log_enum_discriminants_match_root_model() {
        for (action, tag) in [
            (Action::AddProposal, 0),
            (Action::RemoveProposal, 1),
            (Action::VoteApprove, 2),
            (Action::VoteReject, 3),
            (Action::VoteRemove, 4),
            (Action::Finalize, 5),
            (Action::MoveToHub, 6),
        ] {
            assert_eq!(near_sdk::borsh::to_vec(&action).unwrap(), vec![tag]);
        }
    }

    #[test]
    fn new_writes_factory_version_and_empty_initial_state() {
        let predecessor: AccountId = "factory.near".parse().unwrap();
        let council: AccountId = "alice.near".parse().unwrap();
        let mut context = VMContextBuilder::new();
        context.predecessor_account_id(predecessor.clone());
        testing_env!(context.build());

        let contract = Contract::new(
            Config::test_config(),
            VersionedPolicy::Default(vec![council.clone()]),
        );
        assert!(!env::state_exists()); // direct method; SDK wrapper writes STATE
        assert_eq!(contract.get_config().name, "Test");
        assert_eq!(contract.get_policy().roles.len(), 2);
        assert_eq!(contract.locked_amount, NearToken::from_yoctonear(0));
        assert_eq!(contract.staking_id, None);
        assert_eq!(contract.total_delegation_amount, 0);
        assert_eq!(contract.last_proposal_id, 0);
        assert_eq!(contract.last_bounty_id, 0);
        assert!(contract.actions_log.is_empty());
        assert_eq!(contract.delegations.get(&council), None);
        assert!(contract.proposals.get(&0).is_none());
        assert!(contract.bounties.get(&0).is_none());
        assert!(contract.bounty_claimers.get(&council).is_none());
        assert!(contract.bounty_claims_count.get(&0).is_none());

        // Borsh AccountId string: u32 length 12, UTF-8 "factory.near", bool 1.
        assert_eq!(env::storage_read(b"FACTORY"), Some(vec![
            12, 0, 0, 0, 102, 97, 99, 116, 111, 114, 121, 46, 110, 101, 97, 114, 1,
        ]));
        assert_eq!(env::storage_read(b"STATEVERSION"), Some(vec![1]));
        assert!(env::storage_read(&[0]).is_some());
        assert!(env::storage_read(&[1]).is_some());
        let factory = contract.get_factory_info();
        assert_eq!(factory.factory_id, predecessor);
        assert!(factory.auto_update);

        // Root Contract Borsh stores eight length-prefixed one-byte collection
        // handles, scalar counters, and an empty VecDeque. Collection values
        // remain under separate trie keys. This vector is built independently
        // of the derive used to serialize `contract`.
        let mut expected_root = vec![1, 0, 0, 0, 0, 1, 0, 0, 0, 1];
        expected_root.extend([0; 33]); // locked, None, total delegation
        expected_root.extend([1, 0, 0, 0, 2]);
        expected_root.extend([0; 8]); // last proposal id
        expected_root.extend([1, 0, 0, 0, 3]);
        expected_root.extend([0; 8]); // last bounty id
        expected_root.extend([
            1, 0, 0, 0, 4, 1, 0, 0, 0, 5,
            1, 0, 0, 0, 6, 1, 0, 0, 0, 7,
        ]);
        expected_root.extend([0; 4]); // empty action log
        assert_eq!(expected_root.len(), 93);
        assert_eq!(near_sdk::borsh::to_vec(&contract).unwrap(), expected_root);
        env::state_write(&contract);
        assert_eq!(env::storage_read(b"STATE"), Some(expected_root.clone()));
        assert!(env::state_exists());
        for prefix in 2u8..=7u8 {
            assert_eq!(env::storage_read(&[prefix]), None);
        }
        assert_eq!(env::state_read::<Contract>().unwrap().last_proposal_id, 0);

        let mut changed = contract;
        changed.last_proposal_id = 7;
        changed.last_bounty_id = 9;
        let changed_root = near_sdk::borsh::to_vec(&changed).unwrap();
        assert_eq!(&changed_root[48..56], &[7, 0, 0, 0, 0, 0, 0, 0]);
        assert_eq!(&changed_root[61..69], &[9, 0, 0, 0, 0, 0, 0, 0]);
        assert_eq!(changed_root.len(), 93);

        changed.locked_amount = NearToken::from_yoctonear(17);
        changed.staking_id = Some("staking.near".parse().unwrap());
        changed.total_delegation_amount = 19;
        changed.actions_log.push_back(ActionLog {
            account_id: council,
            proposal_id: 7.into(),
            action: Action::VoteApprove,
            block_height: 123.into(),
        });
        let mut populated_root = vec![1, 0, 0, 0, 0, 1, 0, 0, 0, 1];
        populated_root.extend([17]);
        populated_root.extend([0; 15]);
        populated_root.extend([1, 12, 0, 0, 0]);
        populated_root.extend(b"staking.near");
        populated_root.extend([19]);
        populated_root.extend([0; 15]);
        populated_root.extend([1, 0, 0, 0, 2]);
        populated_root.extend([7, 0, 0, 0, 0, 0, 0, 0]);
        populated_root.extend([1, 0, 0, 0, 3]);
        populated_root.extend([9, 0, 0, 0, 0, 0, 0, 0]);
        populated_root.extend([
            1, 0, 0, 0, 4, 1, 0, 0, 0, 5,
            1, 0, 0, 0, 6, 1, 0, 0, 0, 7,
        ]);
        populated_root.extend([1, 0, 0, 0]); // one action log
        populated_root.extend([10, 0, 0, 0]);
        populated_root.extend(b"alice.near");
        populated_root.extend([7, 0, 0, 0, 0, 0, 0, 0]);
        populated_root.push(2); // VoteApprove discriminant
        populated_root.extend([123, 0, 0, 0, 0, 0, 0, 0]);
        assert_eq!(populated_root.len(), 140);
        assert_eq!(near_sdk::borsh::to_vec(&changed).unwrap(), populated_root);
    }

    #[test]
    fn direct_new_preserves_unrelated_preexisting_storage() {
        let predecessor: AccountId = "factory.near".parse().unwrap();
        let council: AccountId = "alice.near".parse().unwrap();
        let mut context = VMContextBuilder::new();
        context.predecessor_account_id(predecessor);
        testing_env!(context.build());
        env::storage_write(b"unrelated", b"keep-me");
        env::storage_write(&[0], b"old-config");
        env::storage_write(&[1], b"old-policy");
        assert!(!env::state_exists());
        let contract = Contract::new(
            Config::test_config(),
            VersionedPolicy::Default(vec![council]),
        );
        assert_eq!(env::storage_read(b"unrelated"), Some(b"keep-me".to_vec()));
        assert_ne!(env::storage_read(&[0]), Some(b"old-config".to_vec()));
        assert_ne!(env::storage_read(&[1]), Some(b"old-policy".to_vec()));
        assert!(!env::state_exists()); // direct method leaves root to wrapper
        env::state_write(&contract);
        assert!(env::state_exists());
        assert_eq!(env::storage_read(b"unrelated"), Some(b"keep-me".to_vec()));
    }
}
