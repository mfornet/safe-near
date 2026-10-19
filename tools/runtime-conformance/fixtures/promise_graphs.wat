(module
  (import "env" "value_return" (func $value (param i64 i64)))
  (import "env" "promise_batch_create" (func $create (param i64 i64) (result i64)))
  (import "env" "promise_batch_then" (func $then (param i64 i64 i64) (result i64)))
  (import "env" "promise_and" (func $and (param i64 i64) (result i64)))
  (import "env" "promise_return" (func $return (param i64)))
  (import "env" "promise_batch_action_transfer" (func $transfer (param i64 i64)))
  (memory 1)
  (data (i32.const 0) "alice.near")
  (data (i32.const 16) "bob.near")
  (data (i32.const 32) "wrap.near")
  (data (i32.const 48) "\01")
  (data (i32.const 96) "carol.near")
  (func $batch (param i64 i64) (result i64) (local i64)
    local.get 0 local.get 1 call $create local.tee 2
    i64.const 48 call $transfer
    local.get 2)
  (func $pair (result i64)
    i32.const 64 i64.const 10 i64.const 0 call $batch i64.store
    i32.const 72 i64.const 8 i64.const 16 call $batch i64.store
    i64.const 64 i64.const 2 call $and)
  (func $callback (param i64) (result i64) (local i64)
    local.get 0 i64.const 9 i64.const 32 call $then local.tee 1
    i64.const 48 call $transfer
    local.get 1)
  (func (export "value_after_receipt")
    i64.const 10 i64.const 0 call $batch call $return
    i64.const 10 i64.const 0 call $value)
  (func (export "receipt_after_value")
    i64.const 10 i64.const 0 call $value
    i64.const 10 i64.const 0 call $batch call $return)
  (func (export "join")
    call $pair call $callback call $return)
  (func (export "nested_join")
    i32.const 64 call $pair i64.store
    i32.const 72 i64.const 10 i64.const 96 call $batch i64.store
    i64.const 64 i64.const 2 call $and call $callback call $return)
  (func (export "duplicate_join")
    call $pair drop
    i32.const 64 i64.const 0 i64.store
    i32.const 72 i64.const 0 i64.store
    i32.const 80 i64.const 1 i64.store
    i64.const 64 i64.const 3 call $and call $callback call $return)
  (func (export "empty_join")
    i64.const 64 i64.const 0 call $and call $callback call $return)
  (func (export "return_join")
    call $pair call $return)
  (func (export "append_join")
    call $pair i64.const 48 call $transfer)
  (func (export "join_invalid")
    i32.const 64 i64.const 99 i64.store
    i64.const 64 i64.const 1 call $and drop)
  (func (export "return_invalid")
    i64.const 99 call $return)
  (func (export "then_invalid")
    i64.const 99 call $callback drop)

  (func (export "join_limit")
    i64.const 10 i64.const 0 call $batch drop
    i64.const 512 i64.const 128 call $and call $callback call $return)
  (func (export "join_exceeded")
    i64.const 10 i64.const 0 call $batch drop
    i64.const 512 i64.const 129 call $and drop)
  (func $limit_pair
    i64.const 10 i64.const 0 call $batch drop
    i32.const 2048 i64.const 512 i64.const 128 call $and i64.store
    i32.const 2056 i64.const 0 i64.store
    i32.const 2064 i64.const 999 i64.store)
  (func (export "nested_exceeded")
    call $limit_pair
    i64.const 2048 i64.const 2 call $and drop)
  (func (export "limit_before_invalid")
    call $limit_pair
    i64.const 2048 i64.const 3 call $and drop)
  (func (export "invalid_before_limit")
    call $limit_pair
    i32.const 2048 i64.const 999 i64.store
    i64.const 2048 i64.const 3 call $and drop)
  (func (export "many_empty_joins")
    i64.const 512 i64.const 0 call $and drop
    i64.const 512 i64.const 129 call $and call $callback call $return)
  (func (export "join_count_overflow")
    i64.const 0 i64.const -1 call $and drop)
  (func (export "join_memory_oob")
    i64.const 4294967295 i64.const 1 call $and drop)
)
