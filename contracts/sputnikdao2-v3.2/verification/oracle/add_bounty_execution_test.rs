
#[cfg(test)]
mod add_bounty_execution_projection_oracle {
    use super::*;
    use near_sdk::mock::MockAction;
    use near_sdk::test_utils::{get_created_receipts, VMContextBuilder};
    use near_sdk::testing_env;

    fn context(deposit: NearToken) -> VMContextBuilder {
        let mut context = VMContextBuilder::new();
        context.current_account_id("dao.sputnik-dao.near".parse().unwrap());
        context.predecessor_account_id("alice.near".parse().unwrap());
        context.attached_deposit(deposit);
        context
    }

    fn setup() -> Contract {
        testing_env!(context(NearToken::from_yoctonear(0)).build());
        Contract::new(Config::test_config(),
            VersionedPolicy::Default(vec!["alice.near".parse().unwrap()]))
    }

    fn propose(contract: &mut Contract, bounty: Bounty) -> u64 {
        testing_env!(context(NearToken::from_near(1)).build());
        contract.add_proposal(ProposalInput {
            description: "add bounty".into(),
            kind: ProposalKind::AddBounty { bounty },
        })
    }

    fn approve(contract: &mut Contract, id: u64) {
        testing_env!(context(NearToken::from_yoctonear(0)).build());
        let kind = contract.get_proposal(id).proposal.kind;
        contract.act_proposal(id, Action::VoteApprove, kind, None);
    }

    fn refund_scheduled() -> bool {
        get_created_receipts().iter().any(|receipt|
            receipt.receiver_id.as_str() == "alice.near" &&
            receipt.actions.iter().any(|action| matches!(action,
                MockAction::Transfer { deposit, .. } if *deposit == NearToken::from_near(1))))
    }

    fn callback_scheduled() -> bool {
        get_created_receipts().iter().any(|receipt|
            receipt.receiver_id.as_str() == "dao.sputnik-dao.near" &&
            receipt.actions.iter().any(|action| matches!(action,
                MockAction::FunctionCallWeight { method_name, .. }
                    if method_name == b"on_proposal_callback")))
    }

    #[test]
    fn zero_times_and_unparsed_token_are_stored_without_claim_counter_write() {
        let mut contract = setup();
        let bounty = Bounty {
            description: "unclaimable".into(),
            token: "not a valid account id".into(),
            amount: U128(7),
            times: 0,
            max_deadline: U64(42),
        };
        let id = propose(&mut contract, bounty.clone());
        assert_eq!(id, 0);
        assert_eq!(contract.last_bounty_id, 0);
        approve(&mut contract, id);
        assert_eq!(contract.get_bounty(0).bounty, bounty);
        assert_eq!(contract.last_bounty_id, 1);
        assert_eq!(contract.bounty_claims_count.get(&0), None);
        assert_eq!(contract.locked_amount, NearToken::from_yoctonear(0));
        assert!(refund_scheduled());
        assert!(!callback_scheduled());

        testing_env!(context(NearToken::from_near(1)).build());
        assert!(std::panic::catch_unwind(std::panic::AssertUnwindSafe(||
            contract.bounty_claim(0, U64(1)))).is_err());
    }

    #[test]
    fn reused_last_id_overwrites_bounty_but_keeps_claim_count() {
        let mut contract = setup();
        let old = Bounty {
            description: "old".into(), token: "".into(), amount: U128(2),
            times: 3, max_deadline: U64(10),
        };
        let new = Bounty {
            description: "new".into(), token: "".into(), amount: U128(9),
            times: 1, max_deadline: U64(20),
        };
        contract.last_bounty_id = 7;
        contract.bounties.insert(&7, &VersionedBounty::Default(old));
        contract.bounty_claims_count.insert(&7, &2);
        let id = propose(&mut contract, new.clone());
        approve(&mut contract, id);
        assert_eq!(contract.get_bounty(7).bounty, new);
        assert_eq!(contract.last_bounty_id, 8);
        assert_eq!(contract.bounty_claims_count.get(&7), Some(2));
        assert!(refund_scheduled());
    }

    #[test]
    fn max_bounty_id_aborts_checked_increment() {
        let mut contract = setup();
        let bounty = Bounty {
            description: "overflow".into(), token: "".into(), amount: U128(1),
            times: 1, max_deadline: U64(1),
        };
        let id = propose(&mut contract, bounty);
        contract.last_bounty_id = u64::MAX;
        assert!(std::panic::catch_unwind(std::panic::AssertUnwindSafe(||
            approve(&mut contract, id))).is_err());
    }
}
