
#[cfg(test)]
mod add_proposal_projection_oracle {
    use super::*;
    use near_sdk::test_utils::VMContextBuilder;
    use near_sdk::testing_env;

    const PROPOSAL_ZERO_KEY: [u8; 9] = [3, 0, 0, 0, 0, 0, 0, 0, 0];

    fn setup() -> (VMContextBuilder, Contract) {
        let council: AccountId = "alice.near".parse().unwrap();
        let mut context = VMContextBuilder::new();
        context.predecessor_account_id(council.clone());
        testing_env!(context.build());
        let contract = Contract::new(Config::test_config(),
            VersionedPolicy::Default(vec![council]));
        (context, contract)
    }

    fn vote_input(description: &str) -> ProposalInput {
        ProposalInput { description: description.into(), kind: ProposalKind::Vote }
    }

    #[test]
    fn fresh_add_writes_proposal_key_and_increments_id_and_lock() {
        let (mut context, mut contract) = setup();
        assert_eq!(env::storage_read(&PROPOSAL_ZERO_KEY), None);
        let bond = contract.policy.get().unwrap().to_policy().proposal_bond;
        testing_env!(context.attached_deposit(bond).build());
        assert_eq!(contract.add_proposal(vote_input("first")), 0);
        assert!(env::storage_read(&PROPOSAL_ZERO_KEY).is_some());
        assert_eq!(contract.get_proposal(0).proposal.description, "first");
        assert_eq!(contract.last_proposal_id, 1);
        assert_eq!(contract.locked_amount, bond);
    }

    #[test]
    fn malformed_occupied_old_proposal_value_aborts_insert() {
        let (mut context, mut contract) = setup();
        env::storage_write(&PROPOSAL_ZERO_KEY, b"malformed proposal");
        let bond = contract.policy.get().unwrap().to_policy().proposal_bond;
        testing_env!(context.attached_deposit(bond).build());
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(||
            contract.add_proposal(vote_input("replacement"))));
        assert!(result.is_err());
        // The native mock does not establish on-chain rollback after panic.
    }

    #[test]
    fn decodable_occupied_old_proposal_value_can_be_replaced() {
        let (mut context, mut contract) = setup();
        let bond = contract.policy.get().unwrap().to_policy().proposal_bond;
        testing_env!(context.attached_deposit(bond).build());
        assert_eq!(contract.add_proposal(vote_input("old")), 0);
        let old_bytes = env::storage_read(&PROPOSAL_ZERO_KEY).unwrap();

        // Reusing an ID is a deliberately noncanonical state. LookupMap
        // decodes the old value before replacing it.
        contract.last_proposal_id = 0;
        assert_eq!(contract.add_proposal(vote_input("new")), 0);
        assert_ne!(env::storage_read(&PROPOSAL_ZERO_KEY), Some(old_bytes));
        assert_eq!(contract.get_proposal(0).proposal.description, "new");
        assert_eq!(contract.last_proposal_id, 1);
        assert_eq!(contract.locked_amount, bond.saturating_mul(2));
    }
}
