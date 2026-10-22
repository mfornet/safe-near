
#[cfg(test)]
mod delegation_projection_oracle {
    use super::*;
    use near_sdk::test_utils::VMContextBuilder;
    use near_sdk::testing_env;

    #[test]
    fn delegation_methods_write_projected_bytes() {
        let staking: AccountId = "stake.near".parse().unwrap();
        let alice: AccountId = "alice.near".parse().unwrap();
        let bob: AccountId = "bob.near".parse().unwrap();
        let alice_key: [u8; 15] = [
            2, 10, 0, 0, 0, 97, 108, 105, 99, 101, 46, 110, 101, 97, 114,
        ];
        let bob_key: [u8; 13] = [
            2, 8, 0, 0, 0, 98, 111, 98, 46, 110, 101, 97, 114,
        ];
        let mut context = VMContextBuilder::new();
        context.predecessor_account_id(staking.clone());
        testing_env!(context.build());
        let mut contract = Contract::new(
            Config::test_config(),
            VersionedPolicy::Default(vec![staking.clone()]),
        );
        contract.staking_id = Some(staking);

        let registration_deposit = env::storage_byte_cost().saturating_mul(16);
        testing_env!(context.attached_deposit(registration_deposit).build());
        contract.register_delegation(&alice);
        assert_eq!(env::storage_read(&alice_key), Some(vec![0; 16]));

        testing_env!(context.attached_deposit(NearToken::from_yoctonear(0)).build());
        assert_eq!(contract.delegate(&alice, U128(258)),
            (U128(0), U128(258), U128(258)));
        let mut delegated = vec![0; 16];
        delegated[0] = 2;
        delegated[1] = 1;
        assert_eq!(env::storage_read(&alice_key), Some(delegated));

        assert_eq!(contract.undelegate(&alice, U128(2)),
            (U128(258), U128(256), U128(256)));
        let mut remaining = vec![0; 16];
        remaining[1] = 1;
        assert_eq!(env::storage_read(&alice_key), Some(remaining));

        // The source permits zero undelegation for an absent account.
        assert_eq!(contract.undelegate(&bob, U128(0)),
            (U128(0), U128(0), U128(256)));
        assert_eq!(env::storage_read(&bob_key), Some(vec![0; 16]));

        // Re-registration overwrites Alice's balance but retains the total.
        testing_env!(context.attached_deposit(registration_deposit).build());
        contract.register_delegation(&alice);
        assert_eq!(env::storage_read(&alice_key), Some(vec![0; 16]));
        assert_eq!(contract.total_delegation_amount, 256);
    }

    #[test]
    fn account_indexes_can_have_the_same_length_as_a_raw_blob_hash() {
        let account: AccountId = "aaaaaaaaaaaaaaaaaaaaaaaaaaa".parse().unwrap();
        let mut context = VMContextBuilder::new();
        context.predecessor_account_id(account.clone());
        testing_env!(context.build());
        let mut contract = Contract::new(
            Config::test_config(),
            VersionedPolicy::Default(vec![account.clone()]),
        );
        let mut delegation_key = vec![2, 27, 0, 0, 0];
        delegation_key.extend(account.as_bytes());
        let mut claimers_key = vec![5, 27, 0, 0, 0];
        claimers_key.extend(account.as_bytes());
        assert_eq!(delegation_key.len(), 32);
        assert_eq!(claimers_key.len(), 32);
        contract.delegations.insert(&account, &0);
        contract.bounty_claimers.insert(&account, &Vec::new());
        assert_eq!(env::storage_read(&delegation_key), Some(vec![0; 16]));
        assert!(env::storage_read(&claimers_key).is_some());

        let hash = [9u8; 32];
        let mut owner_key = vec![7];
        owner_key.extend(hash);
        contract.blobs.insert(&hash, &account);
        assert_eq!(owner_key.len(), 33);
        assert!(env::storage_read(&owner_key).is_some());
    }

    #[test]
    fn synthetic_digest_key_alias_is_overwritten_by_later_delegation() {
        let account: AccountId = "aaaaaaaaaaaaaaaaaaaaaaaaaaa".parse().unwrap();
        let mut context = VMContextBuilder::new();
        context.predecessor_account_id(account.clone());
        testing_env!(context.build());
        let mut contract = Contract::new(
            Config::test_config(),
            VersionedPolicy::Default(vec![account.clone()]),
        );
        let mut raw_key = vec![2, 27, 0, 0, 0];
        raw_key.extend(account.as_bytes());
        let digest: CryptoHash = raw_key.clone().try_into().unwrap();
        let mut owner_key = vec![7];
        owner_key.extend(&digest);

        // This deliberately supplies a candidate digest-shaped key; it does
        // not claim an input whose SHA-256 output is this key.
        assert!(!env::storage_has_key(&digest));
        let payload = vec![0x5a; 16]; // valid Borsh u128 at the alias key
        env::storage_write(&digest, &payload);
        contract.blobs.insert(&digest, &account);
        assert_eq!(env::storage_read(&raw_key), Some(payload));
        assert!(env::storage_read(&owner_key).is_some());

        contract.delegations.insert(&account, &0);
        assert_eq!(env::storage_read(&raw_key), Some(vec![0; 16]));
        assert_eq!(contract.blobs.get(&digest), Some(account.clone()));
        assert!(env::storage_read(&owner_key).is_some());
        // A subsequent raw `store_blob` would fail its storage_has_key guard.
        assert!(env::storage_has_key(&digest));

        let _refund = contract.remove_blob(Base58CryptoHash::from(digest));
        assert_eq!(env::storage_read(&raw_key), None);
        assert_eq!(env::storage_read(&owner_key), None);
        assert_eq!(contract.delegations.get(&account), None);
    }

    #[test]
    fn malformed_synthetic_blob_payload_aborts_delegation_insert() {
        let account: AccountId = "aaaaaaaaaaaaaaaaaaaaaaaaaaa".parse().unwrap();
        let mut context = VMContextBuilder::new();
        context.predecessor_account_id(account.clone());
        testing_env!(context.build());
        let mut contract = Contract::new(
            Config::test_config(),
            VersionedPolicy::Default(vec![account.clone()]),
        );
        let mut raw_key = vec![2, 27, 0, 0, 0];
        raw_key.extend(account.as_bytes());
        env::storage_write(&raw_key, b"not u128");
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(||
            contract.delegations.insert(&account, &0)));
        assert!(result.is_err());
        // The native mock does not establish on-chain rollback after panic.
    }
}
