(module
  (import "env" "promise_batch_create" (func $batch (param i64 i64) (result i64)))
  (import "env" "promise_batch_action_use_global_contract" (func $hash (param i64 i64 i64)))
  (import "env" "promise_batch_action_use_global_contract_by_account_id"
    (func $account (param i64 i64 i64)))
  (import "env" "promise_batch_action_transfer" (func $transfer (param i64 i64)))
  (import "env" "panic" (func $panic))
  (memory 1)
  (data (i32.const 0) "alice.near")
  (data (i32.const 32) "0123456789abcdef0123456789abcdef0")
  (data (i32.const 80) "A!")
  ;; 65 bytes: one over the account id length limit.
  (data (i32.const 96) "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa")
  (data (i32.const 176) "\01")
  (data (i32.const 192) "\ff\fe")
  (func $alice (result i64) i64.const 10 i64.const 0 call $batch)
  (func (export "hash") call $alice i64.const 32 i64.const 32 call $hash)
  (func (export "hash_short") call $alice i64.const 31 i64.const 32 call $hash)
  (func (export "hash_long") call $alice i64.const 33 i64.const 32 call $hash)
  (func (export "hash_oob") call $alice i64.const 32 i64.const 4294967290 call $hash)
  (func (export "account") call $alice i64.const 10 i64.const 0 call $account)
  (func (export "account_invalid") call $alice i64.const 2 i64.const 80 call $account)
  (func (export "account_too_long") call $alice i64.const 65 i64.const 96 call $account)
  (func (export "account_utf8") call $alice i64.const 2 i64.const 192 call $account)
  (func (export "target_invalid") i64.const 7 i64.const 32 i64.const 32 call $hash)
  (func (export "transfer_then_hash") (local i64)
    call $alice local.set 0
    local.get 0 i64.const 176 call $transfer
    local.get 0 i64.const 32 i64.const 32 call $hash
    local.get 0 i64.const 10 i64.const 0 call $account)
  (func (export "hash_then_panic") call $alice i64.const 32 i64.const 32 call $hash call $panic)
)
