
#[cfg(test)]
mod execute_upgrade_projection_oracle {
    use super::*;
    use near_sdk::mock::MockAction;
    use near_sdk::test_utils::{get_created_receipts, VMContextBuilder};
    use near_sdk::testing_env;
    use std::collections::{HashMap, VecDeque};

    fn approve_kind(kind: ProposalKind, raw_blob: Option<(CryptoHash, Vec<u8>)>) ->
        (Contract, Vec<near_sdk::mock::Receipt>) {
        let voter: AccountId = "alice.near".parse().unwrap();
        let mut context = VMContextBuilder::new();
        context.current_account_id("dao.sputnik-dao.near".parse().unwrap());
        context.predecessor_account_id(voter.clone());
        testing_env!(context.build());
        let mut contract = Contract::new(
            Config::test_config(),
            VersionedPolicy::Default(vec![voter.clone()]),
        );
        if let Some((hash, code)) = raw_blob {
            env::storage_write(&hash, &code);
        }
        contract.proposals.insert(&0, &VersionedProposal::Latest(Proposal {
            proposer: voter,
            description: "upgrade".into(),
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
        let receipts = get_created_receipts();
        (contract, receipts)
    }

    fn has_method(receipts: &[near_sdk::mock::Receipt], receiver: &str, method: &[u8]) -> bool {
        receipts.iter().any(|receipt|
            receipt.receiver_id.as_str() == receiver &&
            receipt.actions.iter().any(|action| matches!(action,
                MockAction::FunctionCallWeight { method_name, .. } if method_name == method)))
    }

    fn has_bond_refund(receipts: &[near_sdk::mock::Receipt]) -> bool {
        receipts.iter().any(|receipt|
            receipt.receiver_id.as_str() == "alice.near" &&
            receipt.actions.iter().any(|action| matches!(action,
                MockAction::Transfer { deposit, .. } if *deposit == NearToken::from_near(1))))
    }

    #[test]
    fn self_upgrade_uses_parent_not_stored_factory_and_refunds_immediately() {
        let hash = Base58CryptoHash::from([7; 32]);
        let (contract, receipts) = approve_kind(ProposalKind::UpgradeSelf { hash }, None);
        assert_eq!(contract.get_factory_info().factory_id.as_str(), "alice.near");
        assert_eq!(contract.get_proposal(0).proposal.status, ProposalStatus::Approved);
        assert_eq!(contract.locked_amount, NearToken::from_yoctonear(0));
        assert!(has_method(&receipts, "sputnik-dao.near", b"update"));
        assert!(has_bond_refund(&receipts));
        assert!(!has_method(&receipts, "dao.sputnik-dao.near", b"on_proposal_callback"));
    }

    #[test]
    fn remote_upgrade_reads_raw_blob_and_refunds_before_remote_result() {
        let hash: CryptoHash = [7; 32];
        let kind = ProposalKind::UpgradeRemote {
            receiver_id: "worker.near".parse().unwrap(),
            method_name: "deploy".into(),
            hash: Base58CryptoHash::from(hash),
        };
        let (contract, receipts) = approve_kind(kind, Some((hash, vec![1, 2, 3])));
        assert_eq!(contract.get_proposal(0).proposal.status, ProposalStatus::Approved);
        assert_eq!(contract.locked_amount, NearToken::from_yoctonear(0));
        assert!(has_method(&receipts, "worker.near", b"deploy"));
        assert!(receipts.iter().any(|receipt|
            receipt.receiver_id.as_str() == "worker.near" &&
            receipt.actions.iter().any(|action| matches!(action,
                MockAction::FunctionCallWeight { args, .. } if args == &[1, 2, 3]))));
        assert!(has_bond_refund(&receipts));
        assert!(!has_method(&receipts, "dao.sputnik-dao.near", b"on_proposal_callback"));
    }

    #[test]
    fn remote_upgrade_without_raw_blob_aborts() {
        let kind = ProposalKind::UpgradeRemote {
            receiver_id: "worker.near".parse().unwrap(),
            method_name: "deploy".into(),
            hash: Base58CryptoHash::from([9; 32]),
        };
        assert!(std::panic::catch_unwind(std::panic::AssertUnwindSafe(||
            approve_kind(kind, None))).is_err());
    }
}
