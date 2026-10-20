//! MockedExternal with the pinned runtime's ordinary function-call/access-key
//! UTF-8 method checks. Gas-key and other external behavior remains the mock.
//! All other external behavior remains the VM mock (not trie-backed Runtime).
use near_crypto::PublicKey;
use near_primitives_core::{
    hash::{CryptoHash, YieldId},
    types::{AccountId, Balance, Gas, GasWeight, Nonce, NonceIndex},
};
use near_vm_runner::logic::{
    External, HostError, StorageAccessTracker, VMLogicError, ValuePtr,
    mocks::mock_external::MockedExternal,
    types::{ActionIndex, GlobalContractDeployMode, GlobalContractIdentifier, ReceiptIndex},
};

type Result<T, E = VMLogicError> = std::result::Result<T, E>;

pub struct MethodValidatingExternal {
    pub inner: MockedExternal,
    pub validate_action_method_utf8: bool,
}

impl External for MethodValidatingExternal {
    fn storage_set<'a>(
        &'a mut self,
        access_tracker: &mut dyn StorageAccessTracker,
        key: &[u8],
        value: &[u8],
    ) -> Result<Option<Vec<u8>>> {
        self.inner.storage_set(access_tracker, key, value)
    }

    fn storage_get<'a>(
        &'a self,
        access_tracker: &mut dyn StorageAccessTracker,
        key: &[u8],
    ) -> Result<Option<Box<dyn ValuePtr + 'a>>> {
        self.inner.storage_get(access_tracker, key)
    }

    fn storage_remove(
        &mut self,
        access_tracker: &mut dyn StorageAccessTracker,
        key: &[u8],
    ) -> Result<Option<Vec<u8>>> {
        self.inner.storage_remove(access_tracker, key)
    }

    fn storage_has_key(
        &mut self,
        access_tracker: &mut dyn StorageAccessTracker,
        key: &[u8],
    ) -> Result<bool> {
        self.inner.storage_has_key(access_tracker, key)
    }

    fn generate_data_id(&mut self) -> CryptoHash {
        self.inner.generate_data_id()
    }

    fn get_recorded_storage_size(&self) -> usize {
        self.inner.get_recorded_storage_size()
    }

    fn storage_proof_size_before_receipt(&self) -> usize {
        self.inner.storage_proof_size_before_receipt()
    }

    fn validator_stake(&self, account_id: &AccountId) -> Result<Option<Balance>> {
        self.inner.validator_stake(account_id)
    }

    fn validator_total_stake(&self) -> Result<Balance> {
        self.inner.validator_total_stake()
    }

    fn chain_id(&self) -> String {
        self.inner.chain_id()
    }

    fn create_action_receipt(
        &mut self,
        receipt_indices: Vec<ReceiptIndex>,
        receiver_id: AccountId,
    ) -> Result<ReceiptIndex, VMLogicError> {
        self.inner
            .create_action_receipt(receipt_indices, receiver_id)
    }

    fn create_promise_yield_receipt(
        &mut self,
        receiver_id: AccountId,
    ) -> Result<(ReceiptIndex, CryptoHash), VMLogicError> {
        self.inner.create_promise_yield_receipt(receiver_id)
    }

    fn create_promise_yield_receipt_with_id(
        &mut self,
        receiver_id: AccountId,
        user_yield_id: YieldId,
    ) -> Result<Option<(ReceiptIndex, CryptoHash)>, VMLogicError> {
        self.inner
            .create_promise_yield_receipt_with_id(receiver_id, user_yield_id)
    }

    fn submit_promise_resume_data(
        &mut self,
        data_id: CryptoHash,
        data: Vec<u8>,
    ) -> Result<bool, VMLogicError> {
        self.inner.submit_promise_resume_data(data_id, data)
    }

    fn submit_promise_resume_data_with_yield_id(
        &mut self,
        user_yield_id: YieldId,
        data: Vec<u8>,
    ) -> Result<bool, VMLogicError> {
        self.inner
            .submit_promise_resume_data_with_yield_id(user_yield_id, data)
    }

    fn append_action_create_account(&mut self, receipt_index: ReceiptIndex) {
        self.inner.append_action_create_account(receipt_index)
    }

    fn append_action_deploy_contract(&mut self, receipt_index: ReceiptIndex, code: Vec<u8>) {
        self.inner
            .append_action_deploy_contract(receipt_index, code)
    }

    fn append_action_deploy_global_contract(
        &mut self,
        receipt_index: ReceiptIndex,
        code: Vec<u8>,
        mode: GlobalContractDeployMode,
    ) {
        self.inner
            .append_action_deploy_global_contract(receipt_index, code, mode)
    }

    fn append_action_use_global_contract(
        &mut self,
        receipt_index: ReceiptIndex,
        contract_id: GlobalContractIdentifier,
    ) {
        self.inner
            .append_action_use_global_contract(receipt_index, contract_id)
    }

    fn append_action_deterministic_state_init(
        &mut self,
        receipt_index: ReceiptIndex,
        contract_id: GlobalContractIdentifier,
        amount: Balance,
    ) -> ActionIndex {
        self.inner
            .append_action_deterministic_state_init(receipt_index, contract_id, amount)
    }

    fn set_deterministic_state_init_data_entry(
        &mut self,
        receipt_index: ReceiptIndex,
        action_index: ActionIndex,
        key: Vec<u8>,
        value: Vec<u8>,
    ) -> Result<(), VMLogicError> {
        self.inner
            .set_deterministic_state_init_data_entry(receipt_index, action_index, key, value)
    }

    fn append_action_function_call_weight(
        &mut self,
        receipt_index: ReceiptIndex,
        method_name: Vec<u8>,
        args: Vec<u8>,
        attached_deposit: Balance,
        prepaid_gas: Gas,
        gas_weight: GasWeight,
    ) -> Result<(), VMLogicError> {
        if self.validate_action_method_utf8 {
            std::str::from_utf8(&method_name).map_err(|_| HostError::InvalidMethodName)?;
        }
        self.inner.append_action_function_call_weight(
            receipt_index,
            method_name,
            args,
            attached_deposit,
            prepaid_gas,
            gas_weight,
        )
    }

    fn append_action_transfer(&mut self, receipt_index: ReceiptIndex, deposit: Balance) {
        self.inner.append_action_transfer(receipt_index, deposit)
    }

    fn append_action_transfer_to_gas_key(
        &mut self,
        receipt_index: ReceiptIndex,
        public_key: PublicKey,
        deposit: Balance,
    ) {
        self.inner
            .append_action_transfer_to_gas_key(receipt_index, public_key, deposit)
    }

    fn append_action_add_gas_key_with_full_access(
        &mut self,
        receipt_index: ReceiptIndex,
        public_key: PublicKey,
        num_nonces: NonceIndex,
    ) {
        self.inner
            .append_action_add_gas_key_with_full_access(receipt_index, public_key, num_nonces)
    }

    fn append_action_add_gas_key_with_function_call(
        &mut self,
        receipt_index: ReceiptIndex,
        public_key: PublicKey,
        num_nonces: NonceIndex,
        allowance: Option<Balance>,
        receiver_id: AccountId,
        method_names: Vec<Vec<u8>>,
    ) -> Result<(), VMLogicError> {
        self.inner.append_action_add_gas_key_with_function_call(
            receipt_index,
            public_key,
            num_nonces,
            allowance,
            receiver_id,
            method_names,
        )
    }

    fn append_action_stake(
        &mut self,
        receipt_index: ReceiptIndex,
        stake: Balance,
        public_key: PublicKey,
    ) {
        self.inner
            .append_action_stake(receipt_index, stake, public_key)
    }

    fn append_action_add_key_with_full_access(
        &mut self,
        receipt_index: ReceiptIndex,
        public_key: PublicKey,
        nonce: Nonce,
    ) {
        self.inner
            .append_action_add_key_with_full_access(receipt_index, public_key, nonce)
    }

    fn append_action_add_key_with_function_call(
        &mut self,
        receipt_index: ReceiptIndex,
        public_key: PublicKey,
        nonce: Nonce,
        allowance: Option<Balance>,
        receiver_id: AccountId,
        method_names: Vec<Vec<u8>>,
    ) -> Result<(), VMLogicError> {
        if self.validate_action_method_utf8 {
            for method in &method_names {
                std::str::from_utf8(method).map_err(|_| HostError::InvalidMethodName)?;
            }
        }
        self.inner.append_action_add_key_with_function_call(
            receipt_index,
            public_key,
            nonce,
            allowance,
            receiver_id,
            method_names,
        )
    }

    fn append_action_delete_key(&mut self, receipt_index: ReceiptIndex, public_key: PublicKey) {
        self.inner
            .append_action_delete_key(receipt_index, public_key)
    }

    fn append_action_delete_account(
        &mut self,
        receipt_index: ReceiptIndex,
        beneficiary_id: AccountId,
    ) {
        self.inner
            .append_action_delete_account(receipt_index, beneficiary_id)
    }

    fn get_receipt_receiver(&self, receipt_index: ReceiptIndex) -> &AccountId {
        self.inner.get_receipt_receiver(receipt_index)
    }

    fn set_refund_to(&mut self, receipt_index: ReceiptIndex, refund_to: AccountId) {
        self.inner.set_refund_to(receipt_index, refund_to)
    }

    fn post_quantum_keys_enabled(&self) -> bool {
        self.inner.post_quantum_keys_enabled()
    }
}
