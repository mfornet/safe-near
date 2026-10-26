;; Imports host functions nearcore links only from protocol 85 (chain_id, p256_verify, a gas
;; key host). Before that, every call fails to link; from 85, `chain` returns the chain id.
(module
  (import "env" "chain_id" (func $chain_id (param i64)))
  (import "env" "p256_verify" (func $p256 (param i64 i64 i64 i64 i64 i64) (result i64)))
  (import "env" "promise_batch_action_transfer_to_gas_key" (func $gas_key (param i64 i64 i64 i64)))
  (import "env" "value_return" (func $value_return (param i64 i64)))
  (import "env" "read_register" (func $read_register (param i64 i64)))
  (import "env" "register_len" (func $register_len (param i64) (result i64)))
  (memory 1)
  (func (export "chain")
    (call $chain_id (i64.const 0))
    (call $read_register (i64.const 0) (i64.const 0))
    (call $value_return (call $register_len (i64.const 0)) (i64.const 0)))
  (func (export "noop")))
