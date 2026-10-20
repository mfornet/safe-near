(module
 (import "env" "promise_batch_create" (func $batch (param i64 i64) (result i64)))
 (import "env" "promise_batch_action_add_key_with_function_call" (func $key (param i64 i64 i64 i64 i64 i64 i64 i64 i64)))
 (memory 1)
 (data (i32.const 0) "alice.near")
 (data (i32.const 16) "wrap.near")
 (data (i32.const 256) "aa,bbb")
 (data (i32.const 320) "aa")
 (data (i32.const 384) "aa,bbb,cc")
 (data (i32.const 448) "\ce\bb,\f0\9f\98\80")
 (func $append (param i64 i64)
  i64.const 9 i64.const 16 call $batch
  i64.const 33 i64.const 128 i64.const 7 i64.const 96
  i64.const 10 i64.const 0 local.get 0 local.get 1 call $key)
 (func (export "empty") i64.const 0 i64.const 256 call $append)
 (func (export "single") i64.const 2 i64.const 320 call $append)
 (func (export "two") i64.const 6 i64.const 256 call $append)
 (func (export "three") i64.const 9 i64.const 384 call $append)
 (func (export "unicode") i64.const 7 i64.const 448 call $append)
 (data (i32.const 112) "\01")
 (data (i32.const 512) "\ff\ff\ff\ff\ff\ff\ff\ff\ff\ff\ff\ff\ff\ff\ff\ff")
 (func (export "two_finite")
  i64.const 9 i64.const 16 call $batch i64.const 33 i64.const 128 i64.const 7 i64.const 112
  i64.const 10 i64.const 0 i64.const 6 i64.const 256 call $key)
 (func (export "single_max")
  i64.const 9 i64.const 16 call $batch i64.const 33 i64.const 128 i64.const 7 i64.const 512
  i64.const 10 i64.const 0 i64.const 2 i64.const 320 call $key)
)
