
#[cfg(test)]
mod bounty_payout_projection_oracle {
    use super::*;
    use near_sdk::mock::{MockAction, Receipt};
    use near_sdk::test_utils::{get_created_receipts, VMContextBuilder};
    use near_sdk::{testing_env, PromiseResult};
    use std::collections::HashMap;

    const PROPOSAL_KEY: [u8; 9] = [3, 0, 0, 0, 0, 0, 0, 0, 0];
    const BOUNTY_KEY: [u8; 9] = [4, 0, 0, 0, 0, 0, 0, 0, 0];

    fn context(predecessor: &str, deposit: NearToken) -> VMContextBuilder {
        let mut context = VMContextBuilder::new();
        context.current_account_id("dao.sputnik-dao.near".parse().unwrap());
        context.predecessor_account_id(predecessor.parse().unwrap());
        context.attached_deposit(deposit);
        context
    }

    fn callback_env(result: PromiseResult) {
        testing_env!(context("dao.sputnik-dao.near", NearToken::from_yoctonear(0)).build(),
            near_sdk::test_vm_config(), near_sdk::RuntimeFeesConfig::test(),
            HashMap::default(), vec![result]);
    }

    fn prepare_bounty_done(token: &str) -> Contract {
        testing_env!(context("alice.near", NearToken::from_yoctonear(0)).build());
        let mut contract = Contract::new(Config::test_config(),
            VersionedPolicy::Default(vec!["alice.near".parse().unwrap()]));
        assert_eq!(contract.internal_add_bounty(&Bounty {
            description: "task".into(), token: token.into(), amount: U128(7),
            times: 1, max_deadline: U64(20),
        }), 0);
        testing_env!(context("bob.near", NearToken::from_near(1)).build());
        contract.bounty_claim(0, U64(10));
        contract.bounty_done(0, None, "finished".into());
        assert_eq!(contract.locked_amount, NearToken::from_near(2));
        assert_eq!(contract.get_bounty_number_of_claims(0), 1);
        contract
    }

    fn approve_bounty_done(token: &str) -> Contract {
        let mut contract = prepare_bounty_done(token);
        testing_env!(context("alice.near", NearToken::from_yoctonear(0)).build());
        let kind = contract.get_proposal(0).proposal.kind;
        contract.act_proposal(0, Action::VoteApprove, kind, None);
        assert_eq!(contract.get_proposal(0).proposal.status, ProposalStatus::Approved);
        assert_eq!(contract.get_bounty_number_of_claims(0), 0);
        assert!(contract.get_bounty_claims("bob.near".parse().unwrap()).is_empty());
        assert_eq!(contract.get_bounty(0).bounty.times, 1);
        assert_eq!(contract.locked_amount, NearToken::from_near(2));
        contract
    }

    fn has_callback(receipts: &[Receipt]) -> bool {
        receipts.iter().any(|receipt|
            receipt.receiver_id.as_str() == "dao.sputnik-dao.near" &&
            receipt.actions.iter().any(|action| matches!(action,
                MockAction::FunctionCallWeight { method_name, .. }
                    if method_name == b"on_proposal_callback")))
    }

    fn refund_count(receipts: &[Receipt]) -> usize {
        receipts.iter().filter(|receipt| receipt.receiver_id.as_str() == "bob.near")
            .flat_map(|receipt| receipt.actions.iter())
            .filter(|action| matches!(action, MockAction::Transfer {
                deposit, .. } if *deposit == NearToken::from_near(1)))
            .count()
    }

    #[test]
    fn native_payout_removes_claim_and_schedules_callback_before_refunds() {
        let _contract = approve_bounty_done("");
        let receipts = get_created_receipts();
        assert!(receipts.iter().any(|receipt| receipt.receiver_id.as_str() == "bob.near" &&
            receipt.actions.iter().any(|action| matches!(action,
                MockAction::Transfer { deposit, .. } if *deposit == NearToken::from_yoctonear(7)))));
        assert!(has_callback(&receipts));
        assert_eq!(refund_count(&receipts), 0);
    }

    #[test]
    fn ft_payout_uses_transfer_without_message_and_schedules_callback() {
        let _contract = approve_bounty_done("token.near");
        let receipts = get_created_receipts();
        assert!(receipts.iter().any(|receipt| receipt.receiver_id.as_str() == "token.near" &&
            receipt.actions.iter().any(|action| matches!(action,
                MockAction::FunctionCallWeight {
                    method_name, args, attached_deposit, prepaid_gas, ..
                } if method_name == b"ft_transfer" &&
                    *attached_deposit == NearToken::from_yoctonear(1) &&
                    *prepaid_gas == GAS_FOR_FT_TRANSFER &&
                    String::from_utf8_lossy(args).contains("Bounty 0 payout")))));
        assert!(!receipts.iter().any(|receipt| receipt.actions.iter().any(|action|
            matches!(action, MockAction::FunctionCallWeight { method_name, .. }
                if method_name == b"ft_transfer_call"))));
        assert!(has_callback(&receipts));
        assert_eq!(refund_count(&receipts), 0);
    }

    #[test]
    fn successful_callback_stores_zero_times_and_returns_both_bonds() {
        let mut contract = approve_bounty_done("");
        let bounty_before = env::storage_read(&BOUNTY_KEY).unwrap();
        assert!(env::storage_read(&PROPOSAL_KEY).is_some());
        callback_env(PromiseResult::Successful(vec![]));
        let _ = contract.on_proposal_callback(0);
        assert_eq!(contract.get_proposal(0).proposal.status, ProposalStatus::Approved);
        assert_eq!(contract.get_bounty(0).bounty.times, 0);
        assert_ne!(env::storage_read(&BOUNTY_KEY), Some(bounty_before));
        assert!(env::storage_read(&BOUNTY_KEY).is_some());
        assert!(env::storage_read(&PROPOSAL_KEY).is_some());
        assert_eq!(contract.locked_amount, NearToken::from_yoctonear(0));
        assert_eq!(refund_count(&get_created_receipts()), 2);
    }

    #[test]
    fn successful_callback_uses_current_bonds_even_above_locked_amount() {
        let mut contract = approve_bounty_done("");
        let mut policy = contract.policy.get().unwrap().to_policy();
        policy.bounty_bond = NearToken::from_near(2);
        policy.proposal_bond = NearToken::from_near(3);
        contract.policy.set(&VersionedPolicy::Current(policy));
        callback_env(PromiseResult::Successful(vec![]));
        let _ = contract.on_proposal_callback(0);
        assert_eq!(contract.locked_amount, NearToken::from_yoctonear(0));
        let refunds: Vec<_> = get_created_receipts().iter()
            .filter(|receipt| receipt.receiver_id.as_str() == "bob.near")
            .flat_map(|receipt| receipt.actions.iter())
            .filter_map(|action| match action {
                MockAction::Transfer { deposit, .. } => Some(*deposit),
                _ => None,
            }).collect();
        assert!(refunds.contains(&NearToken::from_near(2)));
        assert!(refunds.contains(&NearToken::from_near(3)));
    }

    #[test]
    fn second_success_callback_removes_zero_times_bounty_and_refunds_again() {
        let mut contract = approve_bounty_done("");
        callback_env(PromiseResult::Successful(vec![]));
        let _ = contract.on_proposal_callback(0);
        assert_eq!(contract.get_bounty(0).bounty.times, 0);
        assert!(env::storage_read(&BOUNTY_KEY).is_some());
        callback_env(PromiseResult::Successful(vec![]));
        let _ = contract.on_proposal_callback(0);
        assert!(contract.bounties.get(&0).is_none());
        assert_eq!(env::storage_read(&BOUNTY_KEY), None);
        assert!(env::storage_read(&PROPOSAL_KEY).is_some());
        assert_eq!(refund_count(&get_created_receipts()), 2);
    }

    #[test]
    fn failed_callback_keeps_bonds_and_direct_retry_lacks_claim() {
        let mut contract = approve_bounty_done("");
        let bounty_before = env::storage_read(&BOUNTY_KEY);
        let proposal_before = env::storage_read(&PROPOSAL_KEY);
        callback_env(PromiseResult::Failed);
        let _ = contract.on_proposal_callback(0);
        assert_eq!(contract.get_proposal(0).proposal.status, ProposalStatus::Failed);
        assert_eq!(contract.get_bounty(0).bounty.times, 1);
        assert_eq!(env::storage_read(&BOUNTY_KEY), bounty_before);
        assert_ne!(env::storage_read(&PROPOSAL_KEY), proposal_before);
        assert_eq!(contract.locked_amount, NearToken::from_near(2));
        assert_eq!(refund_count(&get_created_receipts()), 0);

        testing_env!(context("alice.near", NearToken::from_yoctonear(0)).build());
        let kind = contract.get_proposal(0).proposal.kind;
        assert!(std::panic::catch_unwind(std::panic::AssertUnwindSafe(||
            contract.act_proposal(0, Action::Finalize, kind, None))).is_err());
    }

    #[test]
    fn rejected_vote_removes_claim_and_refunds_both_bonds() {
        let mut contract = prepare_bounty_done("");
        testing_env!(context("alice.near", NearToken::from_yoctonear(0)).build());
        let kind = contract.get_proposal(0).proposal.kind;
        contract.act_proposal(0, Action::VoteReject, kind, None);
        assert_eq!(contract.get_proposal(0).proposal.status, ProposalStatus::Rejected);
        assert_eq!(contract.get_bounty_number_of_claims(0), 0);
        assert!(contract.get_bounty_claims("bob.near".parse().unwrap()).is_empty());
        assert_eq!(contract.get_bounty(0).bounty.times, 1);
        assert_eq!(contract.locked_amount, NearToken::from_yoctonear(0));
        let receipts = get_created_receipts();
        assert_eq!(refund_count(&receipts), 2);
        assert!(!has_callback(&receipts));
    }

    #[test]
    fn removal_vote_removes_claim_and_proposal_without_refunds() {
        let mut contract = prepare_bounty_done("");
        testing_env!(context("alice.near", NearToken::from_yoctonear(0)).build());
        let kind = contract.get_proposal(0).proposal.kind;
        contract.act_proposal(0, Action::VoteRemove, kind, None);
        assert!(contract.proposals.get(&0).is_none());
        assert_eq!(contract.get_bounty_number_of_claims(0), 0);
        assert!(contract.get_bounty_claims("bob.near".parse().unwrap()).is_empty());
        assert_eq!(contract.get_bounty(0).bounty.times, 1);
        assert_eq!(contract.locked_amount, NearToken::from_near(2));
        let receipts = get_created_receipts();
        assert_eq!(refund_count(&receipts), 0);
        assert!(!has_callback(&receipts));
    }

    #[test]
    fn expired_finalize_removes_claim_and_refunds_both_bonds() {
        let mut contract = prepare_bounty_done("");
        let mut context = context("alice.near", NearToken::from_yoctonear(0));
        context.block_timestamp(700_000_000_000_000);
        testing_env!(context.build());
        let kind = contract.get_proposal(0).proposal.kind;
        contract.act_proposal(0, Action::Finalize, kind, None);
        assert_eq!(contract.get_proposal(0).proposal.status, ProposalStatus::Expired);
        assert_eq!(contract.get_bounty_number_of_claims(0), 0);
        assert_eq!(contract.locked_amount, NearToken::from_yoctonear(0));
        assert_eq!(refund_count(&get_created_receipts()), 2);
    }

    #[test]
    fn giveup_before_rejection_leaves_no_claim_and_rejection_aborts() {
        let mut contract = prepare_bounty_done("");
        testing_env!(context("bob.near", NearToken::from_yoctonear(0)).build());
        let _ = contract.bounty_giveup(0);
        assert_eq!(contract.get_bounty_number_of_claims(0), 0);
        testing_env!(context("alice.near", NearToken::from_yoctonear(0)).build());
        let kind = contract.get_proposal(0).proposal.kind;
        assert!(std::panic::catch_unwind(std::panic::AssertUnwindSafe(||
            contract.act_proposal(0, Action::VoteReject, kind, None))).is_err());
    }

    #[test]
    fn authorized_remove_proposal_leaves_completed_claim_and_bonds_locked() {
        let mut contract = prepare_bounty_done("");
        let mut policy = contract.policy.get().unwrap().to_policy();
        policy.roles[1].permissions.insert("bounty_done:RemoveProposal".into());
        contract.policy.set(&VersionedPolicy::Current(policy));
        testing_env!(context("alice.near", NearToken::from_yoctonear(0)).build());
        let kind = contract.get_proposal(0).proposal.kind;
        contract.act_proposal(0, Action::RemoveProposal, kind, None);
        assert!(contract.proposals.get(&0).is_none());
        assert_eq!(contract.get_bounty_number_of_claims(0), 1);
        let claims = contract.get_bounty_claims("bob.near".parse().unwrap());
        assert_eq!(claims.len(), 1);
        assert_eq!(near_sdk::serde_json::to_value(&claims[0]).unwrap()["completed"], true);
        assert_eq!(contract.locked_amount, NearToken::from_near(2));
        assert_eq!(refund_count(&get_created_receipts()), 0);
    }

    #[test]
    fn old_done_proposal_can_consume_fresh_uncompleted_claim() {
        let mut contract = prepare_bounty_done("");
        testing_env!(context("bob.near", NearToken::from_yoctonear(0)).build());
        let _ = contract.bounty_giveup(0);
        assert_eq!(contract.get_bounty_number_of_claims(0), 0);
        assert_eq!(contract.locked_amount, NearToken::from_near(1));
        testing_env!(context("bob.near", NearToken::from_near(1)).build());
        contract.bounty_claim(0, U64(10));
        let claims = contract.get_bounty_claims("bob.near".parse().unwrap());
        assert_eq!(claims.len(), 1);
        assert_eq!(near_sdk::serde_json::to_value(&claims[0]).unwrap()["completed"], false);
        assert_eq!(contract.get_bounty_number_of_claims(0), 1);
        assert_eq!(contract.locked_amount, NearToken::from_near(2));

        testing_env!(context("alice.near", NearToken::from_yoctonear(0)).build());
        let old_kind = contract.get_proposal(0).proposal.kind;
        contract.act_proposal(0, Action::VoteApprove, old_kind, None);
        assert_eq!(contract.get_proposal(0).proposal.status, ProposalStatus::Approved);
        assert_eq!(contract.get_bounty_number_of_claims(0), 0);
        assert!(contract.get_bounty_claims("bob.near".parse().unwrap()).is_empty());
        assert!(has_callback(&get_created_receipts()));
    }

    #[test]
    fn completed_first_claim_blocks_later_uncompleted_claim() {
        testing_env!(context("alice.near", NearToken::from_yoctonear(0)).build());
        let mut contract = Contract::new(Config::test_config(),
            VersionedPolicy::Default(vec!["alice.near".parse().unwrap()]));
        contract.internal_add_bounty(&Bounty {
            description: "repeatable".into(), token: "".into(), amount: U128(7),
            times: 2, max_deadline: U64(20),
        });
        testing_env!(context("bob.near", NearToken::from_near(1)).build());
        contract.bounty_claim(0, U64(10));
        contract.bounty_done(0, None, "first done".into());
        contract.bounty_claim(0, U64(10));
        let claims = contract.get_bounty_claims("bob.near".parse().unwrap());
        assert_eq!(claims.len(), 2);
        assert_eq!(near_sdk::serde_json::to_value(&claims[0]).unwrap()["completed"], true);
        assert_eq!(near_sdk::serde_json::to_value(&claims[1]).unwrap()["completed"], false);
        assert_eq!(contract.get_bounty_number_of_claims(0), 2);
        assert!(std::panic::catch_unwind(std::panic::AssertUnwindSafe(||
            contract.bounty_done(0, None, "second done".into()))).is_err());
        assert_eq!(contract.last_proposal_id, 1);
    }
}
