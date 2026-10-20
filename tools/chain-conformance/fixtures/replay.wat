(module
  (import "env" "promise_batch_create" (func $create (param i64 i64) (result i64)))
  (import "env" "promise_batch_action_deploy_contract" (func $deploy (param i64 i64 i64)))
  (memory 1)
  (data (i32.const 0) "alice.near")
  (data (i32.const 32) "\00asm\01\00\00\00")
  (func (export "ping"))
  (func (export "deploy")
    i64.const 10 i64.const 0 call $create
    i64.const 8 i64.const 32 call $deploy))
