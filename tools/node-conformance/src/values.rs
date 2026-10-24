//! Constructors for every type in scope. `x(g, i)` builds variant `i` of an enum (or the
//! `i`-th shape of a struct) with random fields; `N_X` is the number of variants.

use crate::rng::G;
use borsh::BorshDeserialize;
use near_crypto::{KeyType, PublicKey, Signature};
use near_primitives::account::{
    AccessKey, AccessKeyPermission, AccountContract, FunctionCallPermission, GasKeyInfo,
};
use near_primitives::action::delegate::{
    DelegateAction, DelegateActionV2, NonDelegateAction, SignedDelegateAction,
    VersionedDelegateActionPayload, VersionedSignedDelegateAction,
};
use near_primitives::action::{
    Action, AddKeyAction, CreateAccountAction, DeleteAccountAction, DeleteKeyAction,
    DeployContractAction, DeployGlobalContractAction, DeterministicStateInitAction,
    FunctionCallAction, GlobalContractDeployMode, StakeAction, TransferAction,
    TransferToGasKeyAction, UseGlobalContractAction, WithdrawFromGasKeyAction,
};
use near_primitives::deterministic_account_id::{
    DeterministicAccountStateInit, DeterministicAccountStateInitV1,
};
use near_primitives::errors::*;
use near_primitives::global_contract::GlobalContractIdentifier;
use near_primitives::merkle::{Direction, MerklePathItem};
use near_primitives::profile_data_v2::ProfileDataV2;
use near_primitives::profile_data_v3::ProfileDataV3;
use near_primitives::receipt::*;
use near_primitives::transaction::*;
use near_primitives::types::{AccountId, ShardId};
use ordered_float::NotNan;
use std::borrow::Cow;
use std::collections::BTreeMap;
use std::sync::Arc;

pub const N_BASE_ACTION: usize = 13;
pub const N_ACTION: usize = 15;
pub const N_PERMISSION: usize = 4;
pub const N_CONTRACT: usize = 4;
pub const N_GLOBAL_ID: usize = 2;
pub const N_NONCE: usize = 2;
pub const N_RECEIPT_ENUM: usize = 7;
pub const N_STATUS: usize = 4;
pub const N_METADATA: usize = 4;
pub const N_TX_ERROR: usize = 2;
pub const N_INVALID_TX: usize = 21;
pub const N_ACCESS_KEY_ERROR: usize = 8;
pub const N_ACTIONS_VALIDATION: usize = 21;
pub const N_RECEIPT_VALIDATION: usize = 9;
pub const N_STORAGE: usize = 6;
pub const N_ACTION_KIND: usize = 27;
pub const N_FUNCTION_CALL: usize = 8;
pub const N_COMPILATION: usize = 3;
pub const N_HOST: usize = 34;
pub const N_PREPARE: usize = 19;
pub const N_TRAP: usize = 9;

pub fn id_ident(g: &mut G, i: usize) -> GlobalContractIdentifier {
    match i % N_GLOBAL_ID {
        0 => GlobalContractIdentifier::CodeHash(g.hash()),
        _ => GlobalContractIdentifier::AccountId(g.account()),
    }
}

pub fn contract(g: &mut G, i: usize) -> AccountContract {
    match i % N_CONTRACT {
        0 => AccountContract::None,
        1 => AccountContract::Local(g.hash()),
        2 => AccountContract::Global(g.hash()),
        _ => AccountContract::GlobalByAccount(g.account()),
    }
}

pub fn fc_permission(g: &mut G) -> FunctionCallPermission {
    FunctionCallPermission {
        allowance: g.opt(|g| g.balance()),
        receiver_id: if g.bool() { g.account().to_string() } else { g.string(12) },
        method_names: g.vec(4, |g| g.string(10)),
    }
}

pub fn gas_key_info(g: &mut G) -> GasKeyInfo {
    GasKeyInfo { balance: g.balance(), num_nonces: g.u16() }
}

pub fn permission(g: &mut G, i: usize) -> AccessKeyPermission {
    match i % N_PERMISSION {
        0 => AccessKeyPermission::FunctionCall(fc_permission(g)),
        1 => AccessKeyPermission::FullAccess,
        2 => AccessKeyPermission::GasKeyFunctionCall(gas_key_info(g), fc_permission(g)),
        _ => AccessKeyPermission::GasKeyFullAccess(gas_key_info(g)),
    }
}

pub fn access_key(g: &mut G) -> AccessKey {
    let i = g.below(N_PERMISSION);
    AccessKey { nonce: g.u64(), permission: permission(g, i) }
}

pub fn state_init(g: &mut G) -> DeterministicAccountStateInit {
    let i = g.below(N_GLOBAL_ID);
    let code = id_ident(g, i);
    let mut data = BTreeMap::new();
    for _ in 0..g.below(4) {
        data.insert(g.bytes(8), g.bytes(24));
    }
    DeterministicAccountStateInit::V1(DeterministicAccountStateInitV1 { code, data })
}

pub fn nonce(g: &mut G, i: usize) -> TransactionNonce {
    match i % N_NONCE {
        0 => TransactionNonce::Nonce { nonce: g.u64() },
        _ => TransactionNonce::GasKeyNonce { nonce: g.u64(), nonce_index: g.u16() },
    }
}

/// A non-delegate action; `i` selects one of the 13 kinds.
pub fn base_action(g: &mut G, i: usize) -> Action {
    match i % N_BASE_ACTION {
        0 => Action::CreateAccount(CreateAccountAction {}),
        1 => Action::DeployContract(DeployContractAction { code: g.bytes(64) }),
        2 => Action::FunctionCall(Box::new(FunctionCallAction {
            method_name: g.string(16),
            args: g.bytes(64),
            gas: g.gas(),
            deposit: g.balance(),
        })),
        3 => Action::Transfer(TransferAction { deposit: g.balance() }),
        4 => Action::Stake(Box::new(StakeAction { stake: g.balance(), public_key: g.pk() })),
        5 => Action::AddKey(Box::new(AddKeyAction { public_key: g.pk(), access_key: access_key(g) })),
        6 => Action::DeleteKey(Box::new(DeleteKeyAction { public_key: g.pk() })),
        7 => Action::DeleteAccount(DeleteAccountAction { beneficiary_id: g.account() }),
        8 => Action::DeployGlobalContract(DeployGlobalContractAction {
            code: Arc::from(g.bytes(64)),
            deploy_mode: if g.bool() {
                GlobalContractDeployMode::CodeHash
            } else {
                GlobalContractDeployMode::AccountId
            },
        }),
        9 => {
            let k = g.below(N_GLOBAL_ID);
            Action::UseGlobalContract(Box::new(UseGlobalContractAction {
                contract_identifier: id_ident(g, k),
            }))
        }
        10 => Action::DeterministicStateInit(Box::new(DeterministicStateInitAction {
            state_init: state_init(g),
            deposit: g.balance(),
        })),
        11 => Action::TransferToGasKey(Box::new(TransferToGasKeyAction {
            public_key: g.pk(),
            deposit: g.balance(),
        })),
        _ => Action::WithdrawFromGasKey(Box::new(WithdrawFromGasKeyAction {
            public_key: g.pk(),
            amount: g.balance(),
        })),
    }
}

fn non_delegate(g: &mut G, max: usize) -> Vec<NonDelegateAction> {
    g.vec(max, |g| {
        let i = g.below(N_BASE_ACTION);
        NonDelegateAction::try_from(base_action(g, i)).unwrap()
    })
}

pub fn delegate_action(g: &mut G) -> (DelegateAction, near_crypto::SecretKey) {
    let ty = g.key_type();
    let sk = g.secret(ty);
    let d = DelegateAction {
        sender_id: g.account(),
        receiver_id: g.account(),
        actions: non_delegate(g, 3),
        nonce: g.u64(),
        max_block_height: g.u64(),
        public_key: sk.public_key(),
    };
    (d, sk)
}

pub fn signed_delegate(g: &mut G) -> SignedDelegateAction {
    let (d, sk) = delegate_action(g);
    let signature = g.sign(&sk, d.get_nep461_hash().as_bytes());
    SignedDelegateAction { delegate_action: d, signature }
}

pub fn signed_delegate_v2(g: &mut G) -> VersionedSignedDelegateAction {
    let ty = g.key_type();
    let sk = g.secret(ty);
    let k = g.below(N_NONCE);
    let d = DelegateActionV2 {
        sender_id: g.account(),
        receiver_id: g.account(),
        actions: non_delegate(g, 3),
        nonce: nonce(g, k),
        max_block_height: g.u64(),
        public_key: sk.public_key(),
    };
    let payload = VersionedDelegateActionPayload::V2(d);
    let signature = g.sign(&sk, payload.get_nep461_hash().as_bytes());
    VersionedSignedDelegateAction { delegate_action: payload, signature }
}

pub fn action(g: &mut G, i: usize) -> Action {
    match i % N_ACTION {
        8 => Action::Delegate(Box::new(signed_delegate(g))),
        14 => Action::DelegateV2(Box::new(signed_delegate_v2(g))),
        // The 13 other kinds keep their relative order.
        k => base_action(g, if k < 8 { k } else { k - 1 }),
    }
}

pub fn rand_action(g: &mut G) -> Action {
    let i = g.below(N_ACTION);
    action(g, i)
}

pub fn actions(g: &mut G, max: usize) -> Vec<Action> {
    g.vec(max, rand_action)
}

pub fn transaction_v0(g: &mut G) -> TransactionV0 {
    TransactionV0 {
        signer_id: g.account(),
        public_key: g.pk(),
        nonce: g.u64(),
        receiver_id: g.account(),
        block_hash: g.hash(),
        actions: actions(g, 4),
    }
}

pub fn transaction_v1(g: &mut G) -> TransactionV1 {
    let k = g.below(N_NONCE);
    TransactionV1 {
        signer_id: g.account(),
        public_key: g.pk(),
        nonce: nonce(g, k),
        receiver_id: g.account(),
        block_hash: g.hash(),
        actions: actions(g, 4),
        nonce_mode: if g.bool() { NonceMode::Monotonic } else { NonceMode::Strict },
    }
}

pub fn transaction(g: &mut G) -> Transaction {
    if g.bool() { Transaction::V0(transaction_v0(g)) } else { Transaction::V1(transaction_v1(g)) }
}

pub fn signed_transaction(g: &mut G) -> SignedTransaction {
    let ty = g.key_type();
    let sk = g.secret(ty);
    let mut t = transaction(g);
    match &mut t {
        Transaction::V0(t) => t.public_key = sk.public_key(),
        Transaction::V1(t) => t.public_key = sk.public_key(),
    }
    let (hash, _) = t.get_hash_and_size();
    SignedTransaction::new(g.sign(&sk, hash.as_ref()), t)
}

pub fn data_receivers(g: &mut G) -> Vec<DataReceiver> {
    g.vec(3, |g| DataReceiver { data_id: g.hash(), receiver_id: g.account() })
}

pub fn action_receipt(g: &mut G) -> ActionReceipt {
    ActionReceipt {
        signer_id: g.account(),
        signer_public_key: g.pk(),
        gas_price: g.balance(),
        output_data_receivers: data_receivers(g),
        input_data_ids: g.vec(3, |g| g.hash()),
        actions: actions(g, 3),
    }
}

pub fn action_receipt_v2(g: &mut G) -> ActionReceiptV2 {
    ActionReceiptV2 {
        signer_id: g.account(),
        refund_to: g.opt(|g| g.account()),
        signer_public_key: g.pk(),
        gas_price: g.balance(),
        output_data_receivers: data_receivers(g),
        input_data_ids: g.vec(3, |g| g.hash()),
        actions: actions(g, 3),
    }
}

pub fn data_receipt(g: &mut G) -> DataReceipt {
    DataReceipt { data_id: g.hash(), data: g.opt(|g| g.bytes(64)) }
}

pub fn distribution(g: &mut G, i: usize) -> GlobalContractDistributionReceipt {
    let k = g.below(N_GLOBAL_ID);
    let id = id_ident(g, k);
    let target = ShardId::new(g.u64());
    let delivered = g.vec(4, |g| ShardId::new(g.u64()));
    let code: Arc<[u8]> = Arc::from(g.bytes(64));
    if i % 2 == 0 {
        GlobalContractDistributionReceipt::new_v1(id, target, delivered, code)
    } else {
        GlobalContractDistributionReceipt::new_v2(id, target, delivered, code, g.u64())
    }
}

pub fn receipt_enum(g: &mut G, i: usize) -> ReceiptEnum {
    match i % N_RECEIPT_ENUM {
        0 => ReceiptEnum::Action(action_receipt(g)),
        1 => ReceiptEnum::Data(data_receipt(g)),
        2 => ReceiptEnum::PromiseYield(action_receipt(g)),
        3 => ReceiptEnum::PromiseResume(data_receipt(g)),
        4 => {
            let k = g.below(2);
            ReceiptEnum::GlobalContractDistribution(distribution(g, k))
        }
        5 => ReceiptEnum::ActionV2(action_receipt_v2(g)),
        _ => ReceiptEnum::PromiseYieldV2(action_receipt_v2(g)),
    }
}

pub fn receipt(g: &mut G) -> Receipt {
    let i = g.below(N_RECEIPT_ENUM);
    Receipt::V0(ReceiptV0 {
        predecessor_id: g.account(),
        receiver_id: g.account(),
        receipt_id: g.hash(),
        receipt: receipt_enum(g, i),
    })
}

pub fn state_stored(g: &mut G, i: usize) -> StateStoredReceipt<'static> {
    let metadata = StateStoredReceiptMetadata { congestion_gas: g.gas(), congestion_size: g.u64() };
    let receipt = Cow::Owned(receipt(g));
    if i % 2 == 0 {
        StateStoredReceipt::V0(StateStoredReceiptV0 { receipt, metadata })
    } else {
        StateStoredReceipt::V1(StateStoredReceiptV1 { receipt, metadata })
    }
}

pub fn receipt_or_stored(g: &mut G, i: usize) -> ReceiptOrStateStoredReceipt<'static> {
    if i % 3 == 0 {
        ReceiptOrStateStoredReceipt::Receipt(Cow::Owned(receipt(g)))
    } else {
        ReceiptOrStateStoredReceipt::StateStoredReceipt(state_stored(g, i))
    }
}

pub fn queue_indices(g: &mut G) -> TrieQueueIndices {
    TrieQueueIndices { first_index: g.u64(), next_available_index: g.u64() }
}

pub fn buffered(g: &mut G) -> BufferedReceiptIndices {
    let mut shard_buffers = BTreeMap::new();
    for _ in 0..g.below(5) {
        shard_buffers.insert(ShardId::new(g.u64()), queue_indices(g));
    }
    BufferedReceiptIndices { shard_buffers }
}

// ---- errors ----

fn two(g: &mut G) -> (u64, u64) {
    (g.u64(), g.u64())
}

pub fn storage_error(g: &mut G, i: usize) -> StorageError {
    match i % N_STORAGE {
        0 => StorageError::StorageInternalError,
        1 => StorageError::MissingTrieValue(missing_trie_value(g)),
        2 => StorageError::UnexpectedTrieValue,
        3 => StorageError::StorageInconsistentState(g.string(12)),
        4 => StorageError::FlatStorageBlockNotSupported(g.string(12)),
        _ => StorageError::MemTrieLoadingError(g.string(12)),
    }
}

pub fn missing_trie_value(g: &mut G) -> MissingTrieValue {
    let context = match g.below(4) {
        0 => MissingTrieValueContext::TrieIterator,
        1 => MissingTrieValueContext::TriePrefetchingStorage,
        2 => MissingTrieValueContext::TrieMemoryPartialStorage,
        _ => MissingTrieValueContext::TrieStorage,
    };
    MissingTrieValue { context, hash: g.hash() }
}

pub fn prepare_error(i: usize) -> PrepareError {
    use PrepareError::*;
    [
        Serialization, Deserialization, InternalMemoryDeclared, GasInstrumentation,
        StackHeightInstrumentation, Instantiate, Memory, TooManyFunctions, TooManyLocals,
        TooManyTables, TooManyTableElements, FunctionBodyTooLarge, InstrumentedCodeTooLarge,
        TooManyBlocksPerFunction, TooManyBlocksPerContract, TooManyTypes,
        TooManyParamsPerFunction, TooManyParamsPerContract, OperandStackTooLarge,
    ][i % N_PREPARE]
        .clone()
}

pub fn wasm_trap(i: usize) -> WasmTrap {
    use WasmTrap::*;
    [
        Unreachable, IncorrectCallIndirectSignature, MemoryOutOfBounds, CallIndirectOOB,
        IllegalArithmetic, MisalignedAtomicAccess, IndirectCallToNull, StackOverflow, GenericTrap,
    ][i % N_TRAP]
        .clone()
}

pub fn method_resolve(i: usize) -> MethodResolveError {
    [
        MethodResolveError::MethodEmptyName,
        MethodResolveError::MethodNotFound,
        MethodResolveError::MethodInvalidSignature,
    ][i % 3]
        .clone()
}

pub fn host_error(g: &mut G, i: usize) -> HostError {
    use HostError::*;
    let (a, b) = two(g);
    match i % N_HOST {
        0 => BadUTF16,
        1 => BadUTF8,
        2 => GasExceeded,
        3 => GasLimitExceeded,
        4 => BalanceExceeded,
        5 => EmptyMethodName,
        6 => GuestPanic { panic_msg: g.string(20) },
        7 => IntegerOverflow,
        8 => InvalidPromiseIndex { promise_idx: a },
        9 => CannotAppendActionToJointPromise,
        10 => CannotReturnJointPromise,
        11 => InvalidPromiseResultIndex { result_idx: a },
        12 => InvalidRegisterId { register_id: a },
        13 => IteratorWasInvalidated { iterator_index: a },
        14 => MemoryAccessViolation,
        15 => InvalidReceiptIndex { receipt_index: a },
        16 => InvalidIteratorIndex { iterator_index: a },
        17 => InvalidAccountId,
        18 => InvalidMethodName,
        19 => InvalidPublicKey,
        20 => ProhibitedInView { method_name: g.string(12) },
        21 => NumberOfLogsExceeded { limit: a },
        22 => KeyLengthExceeded { length: a, limit: b },
        23 => ValueLengthExceeded { length: a, limit: b },
        24 => TotalLogLengthExceeded { length: a, limit: b },
        25 => NumberPromisesExceeded { number_of_promises: a, limit: b },
        26 => NumberInputDataDependenciesExceeded {
            number_of_input_data_dependencies: a,
            limit: b,
        },
        27 => ReturnedValueLengthExceeded { length: a, limit: b },
        28 => ContractSizeExceeded { size: a, limit: b },
        29 => Deprecated { method_name: g.string(12) },
        30 => ECRecoverError { msg: g.string(12) },
        31 => AltBn128InvalidInput { msg: g.string(12) },
        32 => Ed25519VerifyInvalidInput { msg: g.string(12) },
        _ => P256VerifyInvalidInput { msg: g.string(12) },
    }
}

pub fn compilation_error(g: &mut G, i: usize) -> CompilationError {
    match i % N_COMPILATION {
        0 => CompilationError::CodeDoesNotExist { account_id: g.account() },
        1 => {
            let k = g.below(N_PREPARE);
            CompilationError::PrepareError(prepare_error(k))
        }
        _ => CompilationError::WasmerCompileError { msg: g.string(16) },
    }
}

pub fn function_call_error(g: &mut G, i: usize) -> FunctionCallError {
    match i % N_FUNCTION_CALL {
        0 => {
            let k = g.below(N_COMPILATION);
            FunctionCallError::CompilationError(compilation_error(g, k))
        }
        1 => FunctionCallError::LinkError { msg: g.string(16) },
        2 => FunctionCallError::MethodResolveError(method_resolve(g.below(3))),
        3 => FunctionCallError::WasmTrap(wasm_trap(g.below(N_TRAP))),
        4 => FunctionCallError::WasmUnknownError,
        5 => {
            let k = g.below(N_HOST);
            FunctionCallError::HostError(host_error(g, k))
        }
        6 => FunctionCallError::_EVMError,
        _ => FunctionCallError::ExecutionError(g.string(16)),
    }
}

pub fn access_key_error(g: &mut G, i: usize) -> InvalidAccessKeyError {
    use InvalidAccessKeyError::*;
    match i % N_ACCESS_KEY_ERROR {
        0 => AccessKeyNotFound { account_id: g.account(), public_key: Box::new(g.pk()) },
        1 => ReceiverMismatch { tx_receiver: g.account(), ak_receiver: g.string(12) },
        2 => MethodNameMismatch { method_name: g.string(12) },
        3 => RequiresFullAccess,
        4 => NotEnoughAllowance {
            account_id: g.account(),
            public_key: Box::new(g.pk()),
            allowance: g.balance(),
            cost: g.balance(),
        },
        5 => DepositWithFunctionCall,
        6 => DelegateActionRequiresNonGasKey,
        _ => DelegateActionRequiresGasKey,
    }
}

pub fn actions_validation(g: &mut G, i: usize) -> ActionsValidationError {
    use ActionsValidationError::*;
    let (a, b) = two(g);
    match i % N_ACTIONS_VALIDATION {
        0 => DeleteActionMustBeFinal,
        1 => TotalPrepaidGasExceeded { total_prepaid_gas: g.gas(), limit: g.gas() },
        2 => TotalNumberOfActionsExceeded { total_number_of_actions: a, limit: b },
        3 => AddKeyMethodNamesNumberOfBytesExceeded { total_number_of_bytes: a, limit: b },
        4 => AddKeyMethodNameLengthExceeded { length: a, limit: b },
        5 => IntegerOverflow,
        6 => InvalidAccountId { account_id: g.string(12) },
        7 => ContractSizeExceeded { size: a, limit: b },
        8 => FunctionCallMethodNameLengthExceeded { length: a, limit: b },
        9 => FunctionCallArgumentsLengthExceeded { length: a, limit: b },
        10 => UnsuitableStakingKey { public_key: Box::new(g.pk()) },
        11 => FunctionCallZeroAttachedGas,
        12 => DelegateActionMustBeOnlyOne,
        13 => UnsupportedProtocolFeature { protocol_feature: g.string(12), version: g.u32() },
        14 => InvalidDeterministicStateInitReceiver {
            receiver_id: g.account(),
            derived_id: g.account(),
        },
        15 => DeterministicStateInitKeyLengthExceeded { length: a, limit: b },
        16 => DeterministicStateInitValueLengthExceeded { length: a, limit: b },
        17 => GasKeyInvalidNumNonces { requested_nonces: g.u16(), limit: g.u16() },
        18 => AddGasKeyWithNonZeroBalance { balance: g.balance() },
        19 => GasKeyFunctionCallAllowanceNotAllowed,
        _ => TotalNumberOfDeployActionsExceeded { number_of_deploy_actions: a, limit: b },
    }
}

pub fn receipt_validation(g: &mut G, i: usize) -> ReceiptValidationError {
    use ReceiptValidationError::*;
    let (a, b) = two(g);
    match i % N_RECEIPT_VALIDATION {
        0 => InvalidPredecessorId { account_id: g.string(12) },
        1 => InvalidReceiverId { account_id: g.string(12) },
        2 => InvalidSignerId { account_id: g.string(12) },
        3 => InvalidDataReceiverId { account_id: g.string(12) },
        4 => ReturnedValueLengthExceeded { length: a, limit: b },
        5 => NumberInputDataDependenciesExceeded {
            number_of_input_data_dependencies: a,
            limit: b,
        },
        6 => {
            let k = g.below(N_ACTIONS_VALIDATION);
            ActionsValidation(actions_validation(g, k))
        }
        7 => ReceiptSizeExceeded { size: a, limit: b },
        _ => InvalidRefundTo { account_id: g.string(12) },
    }
}

pub fn congestion(g: &mut G) -> NotNan<f64> {
    let v = match g.below(6) {
        0 => 0.0,
        1 => 1.0,
        2 => -0.0,
        3 => f64::INFINITY,
        4 => f64::MIN_POSITIVE / 2.0,
        _ => (g.u64() % 1_000_000) as f64 / 1e6,
    };
    NotNan::new(v).unwrap()
}

pub fn invalid_tx(g: &mut G, i: usize) -> InvalidTxError {
    use InvalidTxError::*;
    let (a, b) = two(g);
    match i % N_INVALID_TX {
        0 => {
            let k = g.below(N_ACCESS_KEY_ERROR);
            InvalidAccessKeyError(access_key_error(g, k))
        }
        1 => InvalidSignerId { signer_id: g.string(12) },
        2 => SignerDoesNotExist { signer_id: g.account() },
        3 => InvalidNonce { tx_nonce: a, ak_nonce: b },
        4 => NonceTooLarge { tx_nonce: a, upper_bound: b },
        5 => InvalidReceiverId { receiver_id: g.string(12) },
        6 => InvalidSignature,
        7 => NotEnoughBalance { signer_id: g.account(), balance: g.balance(), cost: g.balance() },
        8 => LackBalanceForState { signer_id: g.account(), amount: g.balance() },
        9 => CostOverflow,
        10 => InvalidChain,
        11 => Expired,
        12 => {
            let k = g.below(N_ACTIONS_VALIDATION);
            ActionsValidation(actions_validation(g, k))
        }
        13 => TransactionSizeExceeded { size: a, limit: b },
        14 => InvalidTransactionVersion,
        15 => {
            let k = g.below(N_STORAGE);
            StorageError(storage_error(g, k))
        }
        16 => ShardCongested { shard_id: g.u32(), congestion_level: congestion(g) },
        17 => ShardStuck { shard_id: g.u32(), missed_chunks: a },
        18 => InvalidNonceIndex { tx_nonce_index: g.opt(|g| g.u16()), num_nonces: g.u16() },
        19 => NotEnoughGasKeyBalance {
            signer_id: g.account(),
            balance: g.balance(),
            cost: g.balance(),
        },
        _ => NotEnoughBalanceForDeposit {
            signer_id: g.account(),
            balance: g.balance(),
            cost: g.balance(),
            reason: if g.bool() {
                DepositCostFailureReason::NotEnoughBalance
            } else {
                DepositCostFailureReason::LackBalanceForState
            },
        },
    }
}

pub fn action_kind(g: &mut G, i: usize) -> ActionErrorKind {
    use ActionErrorKind::*;
    match i % N_ACTION_KIND {
        0 => AccountAlreadyExists { account_id: g.account() },
        1 => AccountDoesNotExist { account_id: g.account() },
        2 => CreateAccountOnlyByRegistrar {
            account_id: g.account(),
            registrar_account_id: g.account(),
            predecessor_id: g.account(),
        },
        3 => CreateAccountNotAllowed { account_id: g.account(), predecessor_id: g.account() },
        4 => ActorNoPermission { account_id: g.account(), actor_id: g.account() },
        5 => DeleteKeyDoesNotExist { account_id: g.account(), public_key: Box::new(g.pk()) },
        6 => AddKeyAlreadyExists { account_id: g.account(), public_key: Box::new(g.pk()) },
        7 => DeleteAccountStaking { account_id: g.account() },
        8 => LackBalanceForState { account_id: g.account(), amount: g.balance() },
        9 => TriesToUnstake { account_id: g.account() },
        10 => TriesToStake {
            account_id: g.account(),
            stake: g.balance(),
            locked: g.balance(),
            balance: g.balance(),
        },
        11 => InsufficientStake {
            account_id: g.account(),
            stake: g.balance(),
            minimum_stake: g.balance(),
        },
        12 => {
            let k = g.below(N_FUNCTION_CALL);
            FunctionCallError(function_call_error(g, k))
        }
        13 => {
            let k = g.below(N_RECEIPT_VALIDATION);
            NewReceiptValidationError(receipt_validation(g, k))
        }
        14 => OnlyImplicitAccountCreationAllowed { account_id: g.account() },
        15 => DeleteAccountWithLargeState { account_id: g.account() },
        16 => DelegateActionInvalidSignature,
        17 => DelegateActionSenderDoesNotMatchTxReceiver {
            sender_id: g.account(),
            receiver_id: g.account(),
        },
        18 => DelegateActionExpired,
        19 => {
            let k = g.below(N_ACCESS_KEY_ERROR);
            DelegateActionAccessKeyError(access_key_error(g, k))
        }
        20 => DelegateActionInvalidNonce { delegate_nonce: g.u64(), ak_nonce: g.u64() },
        21 => DelegateActionNonceTooLarge { delegate_nonce: g.u64(), upper_bound: g.u64() },
        22 => {
            let k = g.below(N_GLOBAL_ID);
            GlobalContractDoesNotExist { identifier: id_ident(g, k) }
        }
        23 => GasKeyDoesNotExist { account_id: g.account(), public_key: Box::new(g.pk()) },
        24 => InsufficientGasKeyBalance {
            account_id: g.account(),
            public_key: Box::new(g.pk()),
            balance: g.balance(),
            required: g.balance(),
        },
        25 => GasKeyBalanceTooHigh {
            account_id: g.account(),
            public_key: g.opt(|g| Box::new(g.pk())),
            balance: g.balance(),
        },
        _ => DelegateActionInvalidNonceIndex { nonce_index: g.u16(), num_nonces: g.u16() },
    }
}

pub fn action_error(g: &mut G) -> ActionError {
    let k = g.below(N_ACTION_KIND);
    ActionError { index: g.opt(|g| g.u64()), kind: action_kind(g, k) }
}

pub fn tx_error(g: &mut G, i: usize) -> TxExecutionError {
    match i % N_TX_ERROR {
        0 => TxExecutionError::ActionError(action_error(g)),
        _ => {
            let k = g.below(N_INVALID_TX);
            TxExecutionError::InvalidTxError(invalid_tx(g, k))
        }
    }
}

// ---- outcomes ----

pub fn profile_v2(g: &mut G) -> ProfileDataV2 {
    let mut b = 72u32.to_le_bytes().to_vec();
    for _ in 0..72 {
        b.extend(if g.below(3) == 0 { 0 } else { g.u64() }.to_le_bytes());
    }
    ProfileDataV2::try_from_slice(&b).unwrap()
}

pub fn profile_v3(g: &mut G) -> ProfileDataV3 {
    let mut b = Vec::new();
    for n in [26u32, 88] {
        b.extend(n.to_le_bytes());
        for _ in 0..n {
            b.extend(if g.below(3) == 0 { 0 } else { g.u64() }.to_le_bytes());
        }
    }
    b.extend(g.u64().to_le_bytes());
    ProfileDataV3::try_from_slice(&b).unwrap()
}

pub fn metadata(g: &mut G, i: usize) -> ExecutionMetadata {
    match i % N_METADATA {
        0 => ExecutionMetadata::V1,
        1 => ExecutionMetadata::V2(profile_v2(g)),
        2 => ExecutionMetadata::V3(Box::new(profile_v3(g))),
        _ => ExecutionMetadata::V4(Box::new(ExecutionMetadataV4 {
            profile: profile_v3(g),
            contracts: g.vec(4, |g| {
                let k = g.below(N_CONTRACT);
                contract(g, k)
            }),
        })),
    }
}

pub fn status(g: &mut G, i: usize) -> ExecutionStatus {
    match i % N_STATUS {
        0 => ExecutionStatus::Unknown,
        1 => {
            let k = g.below(N_TX_ERROR);
            ExecutionStatus::Failure(tx_error(g, k))
        }
        2 => ExecutionStatus::SuccessValue(g.bytes(48)),
        _ => ExecutionStatus::SuccessReceiptId(g.hash()),
    }
}

pub fn outcome(g: &mut G) -> ExecutionOutcome {
    let s = g.below(N_STATUS);
    let m = g.below(N_METADATA);
    ExecutionOutcome {
        logs: g.vec(3, |g| g.string(24)),
        receipt_ids: g.vec(3, |g| g.hash()),
        gas_burnt: g.gas(),
        compute_usage: None,
        tokens_burnt: g.balance(),
        executor_id: g.account(),
        status: status(g, s),
        metadata: metadata(g, m),
    }
}

pub fn outcome_with_id(g: &mut G) -> ExecutionOutcomeWithId {
    ExecutionOutcomeWithId { id: g.hash(), outcome: outcome(g) }
}

pub fn merkle_path(g: &mut G) -> Vec<MerklePathItem> {
    g.vec(6, |g| MerklePathItem {
        hash: g.hash(),
        direction: if g.bool() { Direction::Left } else { Direction::Right },
    })
}

pub fn outcome_with_id_and_proof(g: &mut G) -> ExecutionOutcomeWithIdAndProof {
    ExecutionOutcomeWithIdAndProof {
        proof: merkle_path(g),
        block_hash: g.hash(),
        outcome_with_id: outcome_with_id(g),
    }
}

pub fn outcome_with_proof(g: &mut G) -> ExecutionOutcomeWithProof {
    ExecutionOutcomeWithProof { proof: merkle_path(g), outcome: outcome(g) }
}

pub fn pk_of(g: &mut G, ty: KeyType) -> PublicKey {
    g.pk_of(ty)
}

pub fn sig_of(g: &mut G, ty: KeyType) -> Signature {
    g.sig_of(ty)
}

pub fn account_ids() -> Vec<(String, AccountId)> {
    ["aa", "a.b", "a-b_c.d", "near", "alice.near", "0s0123456789abcdef0123456789abcdef01234567"]
        .iter()
        .map(|s| (s.to_string(), s.parse().unwrap()))
        .collect()
}
