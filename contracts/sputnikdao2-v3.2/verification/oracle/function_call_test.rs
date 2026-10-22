
#[cfg(test)]
mod function_call_projection_oracle {
    use super::*;
    use near_sdk::mock::MockAction;
    use near_sdk::test_utils::{get_created_receipts, VMContextBuilder};
    use near_sdk::{testing_env, Gas, PromiseResult};
    use std::collections::{HashMap, VecDeque};

    fn context(predecessor: &str) -> VMContextBuilder {
        let mut context = VMContextBuilder::new();
        context.current_account_id("dao.sputnik-dao.near".parse().unwrap());
        context.predecessor_account_id(predecessor.parse().unwrap());
        context
    }

    fn approve(actions: Vec<ActionCall>) -> Contract {
        let voter: AccountId = "alice.near".parse().unwrap();
        testing_env!(context("alice.near").build());
        let mut contract = Contract::new(
            Config::test_config(), VersionedPolicy::Default(vec![voter.clone()]));
        let kind = ProposalKind::FunctionCall {
            receiver_id: "worker.near".parse().unwrap(), actions,
        };
        contract.proposals.insert(&0, &VersionedProposal::Latest(Proposal {
            proposer: voter,
            description: "call".into(),
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

    fn callback_env(result: PromiseResult) {
        testing_env!(context("dao.sputnik-dao.near").build(),
            near_sdk::test_vm_config(), near_sdk::RuntimeFeesConfig::test(),
            HashMap::default(), vec![result]);
    }

    #[test]
    fn proposal_creation_accepts_empty_action_list() {
        testing_env!(context("alice.near").build());
        let mut contract = Contract::new(Config::test_config(),
            VersionedPolicy::Default(vec!["alice.near".parse().unwrap()]));
        testing_env!(context("alice.near")
            .attached_deposit(NearToken::from_near(1)).build());
        let id = contract.add_proposal(ProposalInput {
            description: "empty batch".into(),
            kind: ProposalKind::FunctionCall {
                receiver_id: "worker.near".parse().unwrap(), actions: vec![],
            },
        });
        assert_eq!(id, 0);
        assert_eq!(contract.locked_amount, NearToken::from_near(1));
    }

    #[test]
    fn ordered_actions_share_one_receiver_receipt_and_one_callback() {
        let actions = vec![
            ActionCall { method_name: "first".into(), args: vec![1, 2].into(),
                deposit: NearToken::from_yoctonear(3), gas: Gas::from_tgas(4) },
            ActionCall { method_name: "second".into(), args: vec![5].into(),
                deposit: NearToken::from_yoctonear(6), gas: Gas::from_tgas(7) },
        ];
        let _contract = approve(actions);
        let receipts = get_created_receipts();
        let worker: Vec<_> = receipts.iter().filter(|r| r.receiver_id.as_str() == "worker.near").collect();
        assert_eq!(worker.len(), 1);
        let calls: Vec<_> = worker[0].actions.iter().filter_map(|action| match action {
            MockAction::FunctionCallWeight {
                method_name, args, attached_deposit, prepaid_gas, ..
            } => Some((method_name.as_slice(), args.as_slice(), *attached_deposit, *prepaid_gas)),
            _ => None,
        }).collect();
        assert_eq!(calls, vec![
            (b"first".as_slice(), &[1, 2][..], NearToken::from_yoctonear(3), Gas::from_tgas(4)),
            (b"second".as_slice(), &[5][..], NearToken::from_yoctonear(6), Gas::from_tgas(7)),
        ]);
        let callback: Vec<_> = receipts.iter().filter(|r|
            r.receiver_id.as_str() == "dao.sputnik-dao.near" &&
            r.actions.iter().any(|a| matches!(a, MockAction::FunctionCallWeight {
                method_name, .. } if method_name == b"on_proposal_callback"))).collect();
        assert_eq!(callback.len(), 1);
        assert!(!receipts.iter().any(|r| r.receiver_id.as_str() == "alice.near"));
    }

    #[test]
    fn empty_actions_still_schedule_callback_without_immediate_refund() {
        let _contract = approve(vec![]);
        let receipts = get_created_receipts();
        assert_eq!(receipts.iter().filter(|r| r.receiver_id.as_str() == "worker.near").count(), 1);
        assert!(receipts.iter().any(|r| r.receiver_id.as_str() == "dao.sputnik-dao.near" &&
            r.actions.iter().any(|a| matches!(a, MockAction::FunctionCallWeight {
                method_name, .. } if method_name == b"on_proposal_callback"))));
        assert!(!receipts.iter().any(|r| r.receiver_id.as_str() == "alice.near"));
    }

    #[test]
    fn callback_success_and_failure_control_bond_release() {
        let mut success = approve(vec![]);
        callback_env(PromiseResult::Successful(vec![]));
        let _ = success.on_proposal_callback(0);
        assert_eq!(success.locked_amount, NearToken::from_yoctonear(0));
        assert!(get_created_receipts().iter().any(|r| r.receiver_id.as_str() == "alice.near" &&
            r.actions.iter().any(|a| matches!(a, MockAction::Transfer {
                deposit, .. } if *deposit == NearToken::from_near(1)))));

        let mut failure = approve(vec![]);
        callback_env(PromiseResult::Failed);
        let _ = failure.on_proposal_callback(0);
        assert_eq!(failure.get_proposal(0).proposal.status, ProposalStatus::Failed);
        assert_eq!(failure.locked_amount, NearToken::from_near(1));
        assert!(!get_created_receipts().iter().any(|r| r.receiver_id.as_str() == "alice.near"));
    }
}
