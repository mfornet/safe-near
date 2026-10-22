
#[cfg(test)]
mod transfer_projection_oracle {
    use super::*;
    use near_sdk::mock::{MockAction, Receipt};
    use near_sdk::test_utils::{get_created_receipts, VMContextBuilder};
    use near_sdk::{testing_env, PromiseResult};
    use std::collections::{HashMap, VecDeque};

    fn context(predecessor: &str) -> VMContextBuilder {
        let mut context = VMContextBuilder::new();
        context.current_account_id("dao.sputnik-dao.near".parse().unwrap());
        context.predecessor_account_id(predecessor.parse().unwrap());
        context
    }

    fn callback_env(result: PromiseResult) {
        testing_env!(context("dao.sputnik-dao.near").build(),
            near_sdk::test_vm_config(), near_sdk::RuntimeFeesConfig::test(),
            HashMap::default(), vec![result]);
    }

    fn approve_transfer(token: &str, msg: Option<&str>) -> Contract {
        let voter: AccountId = "alice.near".parse().unwrap();
        testing_env!(context("alice.near").build());
        let mut contract = Contract::new(
            Config::test_config(), VersionedPolicy::Default(vec![voter.clone()]));
        let kind = ProposalKind::Transfer {
            token_id: token.into(),
            receiver_id: "bob.near".parse().unwrap(),
            amount: U128(7),
            msg: msg.map(str::to_string),
        };
        contract.proposals.insert(&0, &VersionedProposal::Latest(Proposal {
            proposer: voter,
            description: "transfer memo".into(),
            kind: kind.clone(),
            status: ProposalStatus::InProgress,
            vote_counts: HashMap::new(),
            votes: HashMap::new(),
            submission_time: U64(0),
            last_actions_log: VecDeque::new(),
        }));
        contract.last_proposal_id = 1;
        contract.locked_amount = NearToken::from_near(1);
        contract.act_proposal(0, Action::VoteApprove, kind, None);
        assert_eq!(contract.get_proposal(0).proposal.status, ProposalStatus::Approved);
        assert_eq!(contract.locked_amount, NearToken::from_near(1));
        contract
    }

    fn has_method(receipts: &[Receipt], receiver: &str, method: &[u8]) -> bool {
        receipts.iter().any(|receipt| receipt.receiver_id.as_str() == receiver &&
            receipt.actions.iter().any(|action| matches!(action,
                MockAction::FunctionCallWeight { method_name, .. } if method_name == method)))
    }

    fn has_refund(receipts: &[Receipt]) -> bool {
        receipts.iter().any(|receipt| receipt.receiver_id.as_str() == "alice.near" &&
            receipt.actions.iter().any(|action| matches!(action,
                MockAction::Transfer { deposit, .. } if *deposit == NearToken::from_near(1))))
    }

    fn ft_call_has_expected_resources(receipts: &[Receipt], method: &[u8]) -> bool {
        receipts.iter().any(|receipt| receipt.receiver_id.as_str() == "token.near" &&
            receipt.actions.iter().any(|action| matches!(action,
                MockAction::FunctionCallWeight {
                    method_name, attached_deposit, prepaid_gas, args, ..
                } if method_name == method &&
                    *attached_deposit == NearToken::from_yoctonear(1) &&
                    *prepaid_gas == GAS_FOR_FT_TRANSFER &&
                    String::from_utf8_lossy(args).contains("transfer memo"))))
    }

    #[test]
    fn native_transfer_schedules_callback_and_ignores_legacy_message() {
        let _contract = approve_transfer("", Some("legacy message"));
        let receipts = get_created_receipts();
        assert!(receipts.iter().any(|receipt| receipt.receiver_id.as_str() == "bob.near" &&
            receipt.actions.iter().any(|action| matches!(action,
                MockAction::Transfer { deposit, .. } if *deposit == NearToken::from_yoctonear(7)))));
        assert!(has_method(&receipts, "dao.sputnik-dao.near", b"on_proposal_callback"));
        assert!(!has_refund(&receipts));
    }

    #[test]
    fn ft_transfer_without_message_schedules_callback() {
        let _contract = approve_transfer("token.near", None);
        let receipts = get_created_receipts();
        assert!(has_method(&receipts, "token.near", b"ft_transfer"));
        assert!(ft_call_has_expected_resources(&receipts, b"ft_transfer"));
        assert!(has_method(&receipts, "dao.sputnik-dao.near", b"on_proposal_callback"));
        assert!(!has_refund(&receipts));
    }

    #[test]
    fn ft_transfer_call_with_message_schedules_callback() {
        let _contract = approve_transfer("token.near", Some("deposit"));
        let receipts = get_created_receipts();
        assert!(has_method(&receipts, "token.near", b"ft_transfer_call"));
        assert!(ft_call_has_expected_resources(&receipts, b"ft_transfer_call"));
        assert!(has_method(&receipts, "dao.sputnik-dao.near", b"on_proposal_callback"));
        assert!(!has_refund(&receipts));
    }

    #[test]
    fn successful_callback_releases_bond_only_then() {
        let mut contract = approve_transfer("", None);
        callback_env(PromiseResult::Successful(vec![]));
        let _ = contract.on_proposal_callback(0);
        assert_eq!(contract.get_proposal(0).proposal.status, ProposalStatus::Approved);
        assert_eq!(contract.locked_amount, NearToken::from_yoctonear(0));
        assert!(has_refund(&get_created_receipts()));
    }

    #[test]
    fn failed_callback_marks_failed_and_keeps_bond_locked() {
        let mut contract = approve_transfer("", None);
        callback_env(PromiseResult::Failed);
        let _ = contract.on_proposal_callback(0);
        assert_eq!(contract.get_proposal(0).proposal.status, ProposalStatus::Failed);
        assert_eq!(contract.locked_amount, NearToken::from_near(1));
        assert!(!has_refund(&get_created_receipts()));
    }

    #[test]
    fn successful_callback_uses_current_policy_bond() {
        let mut contract = approve_transfer("", None);
        let mut policy = contract.policy.get().unwrap().to_policy();
        policy.proposal_bond = NearToken::from_yoctonear(7);
        contract.policy.set(&VersionedPolicy::Current(policy));
        callback_env(PromiseResult::Successful(vec![]));
        let _ = contract.on_proposal_callback(0);
        assert_eq!(contract.locked_amount,
            NearToken::from_near(1).saturating_sub(NearToken::from_yoctonear(7)));
        assert!(get_created_receipts().iter().any(|receipt|
            receipt.receiver_id.as_str() == "alice.near" &&
            receipt.actions.iter().any(|action| matches!(action,
                MockAction::Transfer { deposit, .. } if *deposit == NearToken::from_yoctonear(7)))));
    }

    #[test]
    fn callback_does_not_check_stored_status() {
        let mut contract = approve_transfer("", None);
        callback_env(PromiseResult::Successful(vec![]));
        let _ = contract.on_proposal_callback(0);
        callback_env(PromiseResult::Successful(vec![]));
        let _ = contract.on_proposal_callback(0);
        assert_eq!(contract.locked_amount, NearToken::from_yoctonear(0));
        assert!(has_refund(&get_created_receipts()));
    }

    #[test]
    fn legacy_policy_blocks_success_callback_but_failure_marks_failed() {
        let mut contract = approve_transfer("", None);
        contract.policy.set(&VersionedPolicy::Default(
            vec!["alice.near".parse().unwrap()],
        ));
        callback_env(PromiseResult::Successful(vec![]));
        assert!(std::panic::catch_unwind(std::panic::AssertUnwindSafe(||
            contract.on_proposal_callback(0))).is_err());
        assert_eq!(contract.get_proposal(0).proposal.status,
            ProposalStatus::Approved);
        assert_eq!(contract.locked_amount, NearToken::from_near(1));

        callback_env(PromiseResult::Failed);
        let _ = contract.on_proposal_callback(0);
        assert_eq!(contract.get_proposal(0).proposal.status,
            ProposalStatus::Failed);
        assert_eq!(contract.locked_amount, NearToken::from_near(1));
        assert!(!has_refund(&get_created_receipts()));
    }
}
