(module
  (import "env" "promise_batch_create" (func $batch (param i64 i64) (result i64)))
  (import "env" "promise_batch_then" (func $callback (param i64 i64 i64) (result i64)))
  (import "env" "promise_create" (func $create (param i64 i64 i64 i64 i64 i64 i64 i64) (result i64)))
  (import "env" "promise_then" (func $then (param i64 i64 i64 i64 i64 i64 i64 i64 i64) (result i64)))
  (import "env" "promise_and" (func $and (param i64 i64) (result i64)))
  (import "env" "promise_return" (func $return (param i64)))
  (memory 1)
  (data (i32.const 0) "alice.near")
  (data (i32.const 96) "go")
  (data (i32.const 128) "A!")
  (data (i32.const 160) "\ff\ff")
  (func $fill (param i32)
    block
      loop
        local.get 0 i32.eqz br_if 1
        i64.const 512 i64.const 0 call $and drop
        local.get 0 i32.const 1 i32.sub local.set 0
        br 0
      end
    end)
  (func $normal_create (result i64)
    i64.const 10 i64.const 0 i64.const 2 i64.const 96
    i64.const 0 i64.const 0 i64.const 64 i64.const 0 call $create)
  (func (export "normal_create") call $normal_create call $return)
  (func (export "normal_then")
    i64.const 10 i64.const 0 call $batch
    i64.const 10 i64.const 0 i64.const 2 i64.const 96
    i64.const 0 i64.const 0 i64.const 64 i64.const 0 call $then call $return)
  (func (export "count_limit")
    i32.const 1023 call $fill
    i64.const 10 i64.const 0 call $batch call $return)
  (func (export "join_count_limit") i32.const 1024 call $fill)
  (func (export "join_count_exceeded") i32.const 1025 call $fill)
  (func (export "batch_count_exceeded")
    i32.const 1024 call $fill
    i64.const 10 i64.const 0 call $batch drop)
  (func (export "callback_count_exceeded")
    i32.const 1024 call $fill
    i64.const 0 i64.const 10 i64.const 0 call $callback drop)
  (func (export "create_count_exceeded")
    i32.const 1024 call $fill call $normal_create drop)
  (func (export "then_count_exceeded")
    i32.const 1024 call $fill
    i64.const 0 i64.const 10 i64.const 0 i64.const 2 i64.const 96
    i64.const 0 i64.const 0 i64.const 64 i64.const 0 call $then drop)
  (func (export "create_bad_method_at_capacity")
    i32.const 1024 call $fill
    i64.const 10 i64.const 0 i64.const 2 i64.const 4294967295
    i64.const 0 i64.const 0 i64.const 64 i64.const 0 call $create drop)
  (func (export "then_invalid_base_at_capacity")
    i32.const 1024 call $fill
    i64.const 9999 i64.const 10 i64.const 0 i64.const 2 i64.const 96
    i64.const 0 i64.const 0 i64.const 64 i64.const 0 call $then drop)
  (func (export "account_oob_at_capacity")
    i32.const 1024 call $fill
    i64.const 10 i64.const 4294967295 call $batch drop)
  (func (export "account_invalid_at_capacity")
    i32.const 1024 call $fill
    i64.const 2 i64.const 128 call $batch drop)
  (func (export "account_badutf8_at_capacity")
    i32.const 1024 call $fill
    i64.const 2 i64.const 160 call $batch drop)
  (func (export "join_invalid_at_capacity")
    i32.const 1024 call $fill
    i32.const 512 i64.const 9999 i64.store
    i64.const 512 i64.const 1 call $and drop)

  (data (i32.const 256) "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa")
  (data (i32.const 400) "ab..cd")
  (data (i32.const 450) "\c3\a9")
  (func (export "direct_then")
    i64.const 0 i64.const 10 i64.const 0 i64.const 2 i64.const 96
    i64.const 0 i64.const 0 i64.const 64 i64.const 0 call $then drop)
  (func (export "invalid_account") i64.const 2 i64.const 128 call $batch drop)
  (func (export "short_account") i64.const 1 i64.const 0 call $batch drop)
  (func (export "long_account") i64.const 65 i64.const 256 call $batch drop)
  (func (export "double_separator") i64.const 6 i64.const 400 call $batch drop)
  (func (export "utf8_account") i64.const 2 i64.const 450 call $batch drop)
  (func (export "max_account") i64.const 64 i64.const 256 call $batch call $return)
  (func (export "min_account") i64.const 2 i64.const 0 call $batch call $return)

  (func (export "zero_join_oob") i64.const 4294967295 i64.const 0 call $and drop)
  (func (export "zero_join_oob_at_capacity")
    i32.const 1024 call $fill
    i64.const 4294967295 i64.const 0 call $and drop)
)
