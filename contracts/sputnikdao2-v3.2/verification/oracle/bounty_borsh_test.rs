
#[cfg(test)]
mod bounty_borsh_projection_oracle {
    use super::*;

    const CLAIMER_KEY: [u8; 15] = [
        5, 10, 0, 0, 0, 97, 108, 105, 99, 101, 46, 110, 101, 97, 114,
    ];
    const COUNT_KEY: [u8; 9] = [6, 7, 0, 0, 0, 0, 0, 0, 0];
    const NEXT_COUNT_KEY: [u8; 9] = [6, 8, 0, 0, 0, 0, 0, 0, 0];
    const OPEN_VALUE: [u8; 29] = [
        1, 0, 0, 0,
        7, 0, 0, 0, 0, 0, 0, 0,
        1, 0, 0, 0, 0, 0, 0, 0,
        10, 0, 0, 0, 0, 0, 0, 0,
        0,
    ];
    const NEXT_VALUE: [u8; 29] = [
        1, 0, 0, 0,
        8, 0, 0, 0, 0, 0, 0, 0,
        3, 0, 0, 0, 0, 0, 0, 0,
        10, 0, 0, 0, 0, 0, 0, 0,
        0,
    ];

    #[test]
    fn bounty_borsh_matches_projection() {
        use near_sdk::collections::LookupMap;
        use near_sdk::test_utils::VMContextBuilder;
        use near_sdk::testing_env;

        testing_env!(VMContextBuilder::new().build());
        let account: AccountId = "alice.near".parse().unwrap();
        let id = 7_u64;
        let claim = BountyClaim {
            bounty_id: id,
            start_time: U64::from(1),
            deadline: U64::from(10),
            completed: false,
        };

        // These arrays are the checked Lean encoders evaluated on the same
        // account, ID and claim in Model/BountyEncoding.lean.
        let mut completed_value = OPEN_VALUE;
        completed_value[28] = 1;

        let mut claimers: LookupMap<AccountId, Vec<BountyClaim>> =
            LookupMap::new(StorageKeys::BountyClaimers);
        let mut counts: LookupMap<u64, u32> =
            LookupMap::new(StorageKeys::BountyClaimCounts);

        claimers.insert(&account, &vec![claim]);
        counts.insert(&id, &1);
        assert_eq!(env::storage_read(&CLAIMER_KEY), Some(OPEN_VALUE.to_vec()));
        assert_eq!(env::storage_read(&COUNT_KEY), Some(vec![1, 0, 0, 0]));

        let mut completed = claimers.get(&account).unwrap();
        completed[0].completed = true;
        claimers.insert(&account, &completed);
        assert_eq!(env::storage_read(&CLAIMER_KEY), Some(completed_value.to_vec()));

        claimers.remove(&account);
        counts.insert(&id, &0);
        assert_eq!(env::storage_read(&CLAIMER_KEY), None);
        assert_eq!(env::storage_read(&COUNT_KEY), Some(vec![0, 0, 0, 0]));
    }

    #[test]
    fn synthetic_digest_claimers_alias_decodes_then_overwrites() {
        use near_sdk::test_utils::VMContextBuilder;
        use near_sdk::testing_env;

        let account: AccountId = "aaaaaaaaaaaaaaaaaaaaaaaaaaa".parse().unwrap();
        let mut context = VMContextBuilder::new();
        context.predecessor_account_id(account.clone()).block_timestamp(1);
        testing_env!(context.build());
        let mut contract = Contract::new(
            Config::test_config(),
            VersionedPolicy::Default(vec![account.clone()]),
        );
        let id = contract.internal_add_bounty(&Bounty {
            description: "alias fixture".into(),
            token: String::from(OLD_BASE_TOKEN),
            amount: U128(1),
            times: 1,
            max_deadline: U64::from(20),
        });
        let mut raw_key = vec![5, 27, 0, 0, 0];
        raw_key.extend(account.as_bytes());
        let digest: CryptoHash = raw_key.clone().try_into().unwrap();
        let mut owner_key = vec![7];
        owner_key.extend(&digest);
        // This is a synthetic digest-shaped key, not a SHA-256 preimage.
        env::storage_write(&digest, &[0, 0, 0, 0]); // valid empty Vec<BountyClaim>
        contract.blobs.insert(&digest, &account);
        let bond = contract.policy.get().unwrap().to_policy().bounty_bond;
        testing_env!(context.attached_deposit(bond).build());
        contract.bounty_claim(id, U64::from(10));
        let raw_after = env::storage_read(&raw_key).unwrap();
        assert_eq!(raw_after.len(), 29);
        assert_eq!(&raw_after[..4], &[1, 0, 0, 0]);
        assert!(env::storage_read(&owner_key).is_some());
        let _refund = contract.remove_blob(Base58CryptoHash::from(digest));
        assert_eq!(env::storage_read(&raw_key), None);
        assert!(contract.bounty_claimers.get(&account).is_none());
        assert_eq!(contract.bounty_claims_count.get(&id), Some(1));
    }

    #[test]
    fn malformed_synthetic_blob_payload_aborts_bounty_claim() {
        use near_sdk::test_utils::VMContextBuilder;
        use near_sdk::testing_env;

        let account: AccountId = "aaaaaaaaaaaaaaaaaaaaaaaaaaa".parse().unwrap();
        let mut context = VMContextBuilder::new();
        context.predecessor_account_id(account.clone()).block_timestamp(1);
        testing_env!(context.build());
        let mut contract = Contract::new(
            Config::test_config(),
            VersionedPolicy::Default(vec![account.clone()]),
        );
        let id = contract.internal_add_bounty(&Bounty {
            description: "alias fixture".into(),
            token: String::from(OLD_BASE_TOKEN),
            amount: U128(1),
            times: 1,
            max_deadline: U64::from(20),
        });
        let mut raw_key = vec![5, 27, 0, 0, 0];
        raw_key.extend(account.as_bytes());
        env::storage_write(&raw_key, b"bad");
        let bond = contract.policy.get().unwrap().to_policy().bounty_bond;
        testing_env!(context.attached_deposit(bond).build());
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(||
            contract.bounty_claim(id, U64::from(10))));
        assert!(result.is_err());
        // The native mock does not establish on-chain rollback of count writes.
    }

    #[test]
    fn bounty_claim_done_and_remove_write_projected_bytes() {
        use near_sdk::test_utils::VMContextBuilder;
        use near_sdk::testing_env;

        let account: AccountId = "alice.near".parse().unwrap();
        let mut context = VMContextBuilder::new();
        context.predecessor_account_id(account.clone()).block_timestamp(1);
        testing_env!(context.build());
        let mut contract = Contract::new(
            Config::test_config(),
            VersionedPolicy::Default(vec![account.clone()]),
        );
        contract.last_bounty_id = 7;
        assert_eq!(contract.internal_add_bounty(&Bounty {
            description: "oracle bounty".to_string(),
            token: String::from(OLD_BASE_TOKEN),
            amount: U128(1),
            times: 2,
            max_deadline: U64::from(20),
        }), 7);
        let policy = contract.policy.get().unwrap().to_policy();
        testing_env!(context.attached_deposit(policy.bounty_bond).build());

        contract.bounty_claim(7, U64::from(10));
        assert_eq!(env::storage_read(&CLAIMER_KEY), Some(OPEN_VALUE.to_vec()));
        assert_eq!(env::storage_read(&COUNT_KEY), Some(vec![1, 0, 0, 0]));

        testing_env!(context.attached_deposit(policy.proposal_bond)
            .block_timestamp(2).build());
        contract.bounty_done(7, None, "done".to_string());
        let mut completed_value = OPEN_VALUE;
        completed_value[28] = 1;
        assert_eq!(env::storage_read(&CLAIMER_KEY), Some(completed_value.to_vec()));
        assert_eq!(env::storage_read(&COUNT_KEY), Some(vec![1, 0, 0, 0]));

        assert_eq!(contract.internal_add_bounty(&Bounty {
            description: "second oracle bounty".to_string(),
            token: String::from(OLD_BASE_TOKEN),
            amount: U128(1),
            times: 2,
            max_deadline: U64::from(20),
        }), 8);
        testing_env!(context.attached_deposit(policy.bounty_bond)
            .block_timestamp(3).build());
        contract.bounty_claim(8, U64::from(10));
        contract.internal_remove_claim(7, &account);
        assert_eq!(env::storage_read(&CLAIMER_KEY), Some(NEXT_VALUE.to_vec()));
        assert_eq!(env::storage_read(&COUNT_KEY), Some(vec![0, 0, 0, 0]));
        assert_eq!(env::storage_read(&NEXT_COUNT_KEY), Some(vec![1, 0, 0, 0]));

        contract.internal_remove_claim(8, &account);
        assert_eq!(env::storage_read(&CLAIMER_KEY), None);
        assert_eq!(env::storage_read(&NEXT_COUNT_KEY), Some(vec![0, 0, 0, 0]));
    }

    #[test]
    fn legacy_policy_blocks_bounty_calls_but_expired_done_cleans_claim() {
        use near_sdk::test_utils::VMContextBuilder;
        use near_sdk::testing_env;

        let account: AccountId = "alice.near".parse().unwrap();
        let mut context = VMContextBuilder::new();
        context.predecessor_account_id(account.clone()).block_timestamp(1);
        testing_env!(context.build());
        let mut contract = Contract::new(
            Config::test_config(),
            VersionedPolicy::Default(vec![account.clone()]),
        );
        let id = contract.internal_add_bounty(&Bounty {
            description: "policy barrier".into(),
            token: String::from(OLD_BASE_TOKEN),
            amount: U128(1),
            times: 2,
            max_deadline: U64::from(20),
        });
        let policy = contract.policy.get().unwrap().to_policy();
        testing_env!(context.attached_deposit(policy.bounty_bond).build());
        contract.bounty_claim(id, U64::from(10));
        contract.policy.set(&VersionedPolicy::Default(vec![account.clone()]));

        assert!(std::panic::catch_unwind(std::panic::AssertUnwindSafe(||
            contract.bounty_claim(id, U64::from(10)))).is_err());
        testing_env!(context.attached_deposit(NearToken::from_yoctonear(0))
            .block_timestamp(2).build());
        assert!(std::panic::catch_unwind(std::panic::AssertUnwindSafe(||
            contract.bounty_giveup(id))).is_err());
        testing_env!(context.attached_deposit(policy.proposal_bond).build());
        assert!(std::panic::catch_unwind(std::panic::AssertUnwindSafe(||
            contract.bounty_done(id, None, "timely".into()))).is_err());

        testing_env!(context.attached_deposit(NearToken::from_yoctonear(0))
            .block_timestamp(12).build());
        contract.bounty_done(id, None, "expired".into());
        assert!(contract.bounty_claimers.get(&account).is_none());
        assert_eq!(contract.bounty_claims_count.get(&id), Some(0));
        assert_eq!(contract.locked_amount, policy.bounty_bond);
    }
}
