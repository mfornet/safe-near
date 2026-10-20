(module
  (import "env" "promise_batch_create" (func $batch (param i64 i64) (result i64)))
  (import "env" "promise_batch_action_stake" (func $stake (param i64 i64 i64 i64)))
  (import "env" "promise_batch_action_transfer" (func $transfer (param i64 i64)))
  (import "env" "panic" (func $panic))
  (memory 1)
  (data (i32.const 0) "wrap.near")
  (data (i32.const 16) "alice.near")
  (data (i32.const 32) "\01")
  (data (i32.const 48) "\65")
  (data (i32.const 64) "\ff\ff\ff\ff\ff\ff\ff\ff\ff\ff\ff\ff\ff\ff\ff\ff")
  ;; 33 zero bytes at 128 are an ED25519 public key (tag plus key bytes).
  (func $self (result i64) i64.const 9 i64.const 0 call $batch)
  (func $append (param i64 i64)
    local.get 0 local.get 1 i64.const 33 i64.const 128 call $stake)
  (func (export "stake_zero") call $self i64.const 96 call $append)
  (func (export "stake_one") call $self i64.const 32 call $append)
  (func (export "stake_over_balance") call $self i64.const 48 call $append)
  (func (export "stake_max") call $self i64.const 64 call $append)
  (func (export "stake_other") i64.const 10 i64.const 16 call $batch i64.const 32 call $append)
  (func (export "stake_twice") (local i64)
    call $self local.set 0
    local.get 0 i64.const 32 call $append
    local.get 0 i64.const 48 call $append)
  (func (export "stake_then_panic") call $self i64.const 32 call $append call $panic)
  (func (export "transfer_then_stake") (local i64)
    call $self local.set 0
    local.get 0 i64.const 32 call $transfer
    local.get 0 i64.const 32 call $append)
)
