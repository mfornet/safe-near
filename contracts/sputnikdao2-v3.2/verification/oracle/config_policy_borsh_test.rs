
#[cfg(test)]
mod config_policy_borsh_projection_oracle {
    use super::*;
    use near_sdk::json_types::{Base64VecU8, U64};
    use near_sdk::test_utils::VMContextBuilder;
    use near_sdk::testing_env;
    use std::collections::{HashMap, HashSet};

    fn push_string(out: &mut Vec<u8>, text: &str) {
        out.extend_from_slice(&(text.len() as u32).to_le_bytes());
        out.extend_from_slice(text.as_bytes());
    }

    fn push_vote_with_quorum(out: &mut Vec<u8>, quorum: u128) {
        out.push(1); // RoleWeight
        out.extend_from_slice(&quorum.to_le_bytes());
        out.push(1); // Ratio
        out.extend_from_slice(&1u64.to_le_bytes());
        out.extend_from_slice(&2u64.to_le_bytes());
    }

    fn push_default_vote(out: &mut Vec<u8>) {
        push_vote_with_quorum(out, 0);
    }

    #[test]
    fn constructor_writes_exact_config_and_current_policy_values() {
        testing_env!(VMContextBuilder::new().build());
        let config = Config {
            name: "Test".to_string(),
            purpose: "to test".to_string(),
            metadata: Base64VecU8(vec![0, 255, 1]),
        };
        let policy = Policy {
            roles: vec![],
            default_vote_policy: VotePolicy::default(),
            proposal_bond: NearToken::from_yoctonear(17),
            proposal_period: U64(123),
            bounty_bond: NearToken::from_yoctonear(19),
            bounty_forgiveness_period: U64(456),
        };
        let contract = Contract::new(config.clone(), VersionedPolicy::Current(policy.clone()));

        let mut expected_config = Vec::new();
        push_string(&mut expected_config, "Test");
        push_string(&mut expected_config, "to test");
        expected_config.extend_from_slice(&3u32.to_le_bytes());
        expected_config.extend_from_slice(&[0, 255, 1]);
        assert_eq!(expected_config.len(), 26);
        assert_eq!(env::storage_read(&[0]), Some(expected_config));
        assert_eq!(contract.get_config(), config);

        let mut expected_policy = vec![1]; // Current
        expected_policy.extend_from_slice(&0u32.to_le_bytes()); // no roles
        push_default_vote(&mut expected_policy);
        expected_policy.extend_from_slice(&17u128.to_le_bytes());
        expected_policy.extend_from_slice(&123u64.to_le_bytes());
        expected_policy.extend_from_slice(&19u128.to_le_bytes());
        expected_policy.extend_from_slice(&456u64.to_le_bytes());
        assert_eq!(expected_policy.len(), 87);
        assert_eq!(env::storage_read(&[1]), Some(expected_policy));
        assert_eq!(contract.get_policy(), policy);
        assert_eq!(near_sdk::borsh::to_vec(&VersionedPolicy::Default(vec![])).unwrap(),
            vec![0, 0, 0, 0, 0]);
    }

    #[test]
    fn role_set_and_policy_map_entries_serialize_in_ord_order() {
        let group: HashSet<AccountId> = ["z.near".parse().unwrap(),
            "a.near".parse().unwrap()].into_iter().collect();
        let permissions: HashSet<String> = ["X:VoteReject".to_string(),
            "X:VoteApprove".to_string()].into_iter().collect();
        let vote_policy: HashMap<String, VotePolicy> = [
            ("Z".to_string(), VotePolicy::default()),
            ("A".to_string(), VotePolicy::default()),
        ].into_iter().collect();
        let role = RolePermission {
            name: "council".to_string(),
            kind: RoleKind::Group(group),
            permissions,
            vote_policy,
        };
        let mut expected = Vec::new();
        push_string(&mut expected, "council");
        expected.push(2); // Group
        expected.extend_from_slice(&2u32.to_le_bytes());
        push_string(&mut expected, "a.near");
        push_string(&mut expected, "z.near");
        expected.extend_from_slice(&2u32.to_le_bytes());
        push_string(&mut expected, "X:VoteApprove");
        push_string(&mut expected, "X:VoteReject");
        expected.extend_from_slice(&2u32.to_le_bytes());
        push_string(&mut expected, "A");
        push_default_vote(&mut expected);
        push_string(&mut expected, "Z");
        push_default_vote(&mut expected);
        assert_eq!(expected.len(), 155);
        assert_eq!(near_sdk::borsh::to_vec(&role).unwrap(), expected);
    }

    #[test]
    fn constructor_default_input_writes_same_current_policy_as_explicit_upgrade() {
        let council: AccountId = "alice.near".parse().unwrap();
        testing_env!(VMContextBuilder::new().build());
        let _ = Contract::new(Config::test_config(),
            VersionedPolicy::Default(vec![council.clone()]));
        let default_input_bytes = env::storage_read(&[1]).unwrap();
        assert_eq!(default_input_bytes[0], 1); // Current after upgrade

        testing_env!(VMContextBuilder::new().build());
        let _ = Contract::new(Config::test_config(),
            VersionedPolicy::Current(default_policy(vec![council])));
        assert_eq!(env::storage_read(&[1]), Some(default_input_bytes));
    }

    #[test]
    fn malformed_config_and_policy_bytes_are_rejected() {
        let config = Config {
            name: "Test".to_string(),
            purpose: "to test".to_string(),
            metadata: Base64VecU8(vec![0, 255, 1]),
        };
        let mut config_bytes = near_sdk::borsh::to_vec(&config).unwrap();
        config_bytes[4] = 255; // invalid UTF-8 in the name
        assert!(Config::try_from_slice(&config_bytes).is_err());
        let mut config_trailing = near_sdk::borsh::to_vec(&config).unwrap();
        config_trailing.push(9);
        assert!(Config::try_from_slice(&config_trailing).is_err());

        let policy = Policy {
            roles: vec![],
            default_vote_policy: VotePolicy::default(),
            proposal_bond: NearToken::from_yoctonear(17),
            proposal_period: U64(123),
            bounty_bond: NearToken::from_yoctonear(19),
            bounty_forgiveness_period: U64(456),
        };
        let mut policy_bytes = near_sdk::borsh::to_vec(&
            VersionedPolicy::Current(policy)).unwrap();
        assert_eq!(policy_bytes.len(), 87);
        let mut wrong_tag = policy_bytes.clone();
        wrong_tag[0] = 2;
        assert!(VersionedPolicy::try_from_slice(&wrong_tag).is_err());
        policy_bytes[31..39].fill(0); // Ratio's NonZeroU64 denominator
        assert!(VersionedPolicy::try_from_slice(&policy_bytes).is_err());
    }

    #[test]
    fn noncanonical_role_collections_are_accepted_then_normalized() {
        // The resolved Borsh dependency does not enable de_strict_order.
        // The Rust HashSet absorbs duplicates and serialization sorts keys.
        let mut raw = Vec::new();
        push_string(&mut raw, "test");
        raw.push(0); // Everyone
        raw.extend_from_slice(&3u32.to_le_bytes());
        push_string(&mut raw, "Z");
        push_string(&mut raw, "A");
        push_string(&mut raw, "A");
        raw.extend_from_slice(&3u32.to_le_bytes());
        push_string(&mut raw, "Z");
        push_vote_with_quorum(&mut raw, 3);
        push_string(&mut raw, "A");
        push_vote_with_quorum(&mut raw, 5);
        push_string(&mut raw, "A");
        push_vote_with_quorum(&mut raw, 7);
        let role = RolePermission::try_from_slice(&raw).unwrap();
        assert_eq!(role.permissions.len(), 2);
        assert_eq!(role.vote_policy.len(), 2);
        assert_eq!(role.vote_policy.get("A").unwrap().quorum.0, 7);
        let mut canonical = Vec::new();
        push_string(&mut canonical, "test");
        canonical.push(0);
        canonical.extend_from_slice(&2u32.to_le_bytes());
        push_string(&mut canonical, "A");
        push_string(&mut canonical, "Z");
        canonical.extend_from_slice(&2u32.to_le_bytes());
        push_string(&mut canonical, "A");
        push_vote_with_quorum(&mut canonical, 7);
        push_string(&mut canonical, "Z");
        push_vote_with_quorum(&mut canonical, 3);
        assert_ne!(raw, canonical);
        assert_eq!(near_sdk::borsh::to_vec(&role).unwrap(), canonical);
    }
}
