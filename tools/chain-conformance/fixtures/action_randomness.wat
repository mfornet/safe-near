(module
  (import "env" "random_seed" (func $random_seed (param i64)))
  (import "env" "read_register" (func $read_register (param i64 i64)))
  (import "env" "value_return" (func $return (param i64 i64)))
  (import "env" "log_utf8" (func $log (param i64 i64)))
  (import "env" "promise_create" (func $create (param i64 i64 i64 i64 i64 i64 i64 i64) (result i64)))
  (import "env" "promise_then" (func $then (param i64 i64 i64 i64 i64 i64 i64 i64 i64) (result i64)))
  (import "env" "promise_return" (func $promise_return (param i64)))
  (memory (export "memory") 1)
  (data (i32.const 64) "0123456789abcdef")
  (data (i32.const 256) "callee.near")
  (data (i32.const 288) "captured.near")
  (data (i32.const 320) "seed")
  (func $seed (export "seed") (local $i i32)
    i64.const 0 call $random_seed
    i64.const 0 i64.const 0 call $read_register
    (block $done
      (loop $again
        local.get $i i32.const 32 i32.ge_u br_if $done
        i32.const 96 local.get $i i32.const 1 i32.shl i32.add
        i32.const 64 local.get $i i32.load8_u i32.const 4 i32.shr_u i32.add i32.load8_u i32.store8
        i32.const 97 local.get $i i32.const 1 i32.shl i32.add
        i32.const 64 local.get $i i32.load8_u i32.const 15 i32.and i32.add i32.load8_u i32.store8
        local.get $i i32.const 1 i32.add local.set $i
        br $again))
    i64.const 64 i64.const 96 call $log
    i64.const 32 i64.const 0 call $return)
  (func (export "spawn_seed") (local $promise i64)
    call $seed
    i64.const 11 i64.const 256 i64.const 4 i64.const 320 i64.const 0 i64.const 0
    i64.const 352 i64.const 50000000000000 call $create local.set $promise
    local.get $promise i64.const 13 i64.const 288 i64.const 4 i64.const 320
    i64.const 0 i64.const 0 i64.const 352 i64.const 50000000000000 call $then
    call $promise_return))
