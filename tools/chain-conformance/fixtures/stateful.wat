(module
  (type $pair (func (param i64 i64) (result i64)))
  (import "env" "storage_write" (func $write (param i64 i64 i64 i64 i64) (result i64)))
  (import "env" "storage_read" (func $read (param i64 i64 i64) (result i64)))
  (import "env" "storage_remove" (func $remove (param i64 i64 i64) (result i64)))
  (import "env" "register_len" (func $len (param i64) (result i64)))
  (import "env" "read_register" (func $register (param i64 i64)))
  (import "env" "value_return" (func $return (param i64 i64)))
  (import "env" "panic_utf8" (func $panic (param i64 i64)))
  (import "env" "promise_create" (func $create (param i64 i64 i64 i64 i64 i64 i64 i64) (result i64)))
  (import "env" "promise_then" (func $then (param i64 i64 i64 i64 i64 i64 i64 i64 i64) (result i64)))
  (import "env" "promise_return" (func $promise_return (param i64)))
  (import "env" "promise_result" (func $result (param i64 i64) (result i64)))
  (memory 1)
  (data (i32.const 0) "k")
  (data (i32.const 8) "v\ff")
  (data (i32.const 16) "rolled-back")
  (data (i32.const 32) "panic")
  (data (i32.const 64) "callee.near")
  (data (i32.const 96) "read")
  (data (i32.const 104) "fail")
  (data (i32.const 128) "captured.near")
  (data (i32.const 160) "callback")
  (func $pick (type $pair) (param $first i64) (param $second i64) (result i64)
    local.get $second)
  (func (export "typed_names")
    i32.const 256 i64.const 11 i64.const 22 call $pick i64.store
    i64.const 8 i64.const 256 call $return)
  (func (export "write")
    i64.const 1 i64.const 0 i64.const 2 i64.const 8 i64.const 0 call $write drop)
  (func $register_return
    i64.const 0 i64.const 400 call $register
    i64.const 0 call $len i64.const 400 call $return)
  (func (export "read")
    i64.const 1 i64.const 0 i64.const 0 call $read i64.const 0 i64.ne
    if call $register_return end)
  (func (export "remove")
    i64.const 1 i64.const 0 i64.const 0 call $remove drop)
  (func (export "panic_after_write")
    i64.const 1 i64.const 0 i64.const 11 i64.const 16 i64.const 0 call $write drop
    i64.const 5 i64.const 32 call $panic)
  (func $spawn (param $method i64) (local $p i64)
    i64.const 11 i64.const 64 i64.const 4 local.get $method i64.const 0 i64.const 0
    i64.const 208 i64.const 30000000000000 call $create local.set $p
    local.get $p i64.const 13 i64.const 128 i64.const 8 i64.const 160
    i64.const 0 i64.const 0 i64.const 208 i64.const 30000000000000 call $then
    call $promise_return)
  (func (export "spawn") i64.const 96 call $spawn)
  (func (export "spawn_fail") i64.const 104 call $spawn)
  (func (export "fail") i64.const 5 i64.const 32 call $panic)
  (func (export "callback")
    i64.const 0 i64.const 0 call $result i64.const 1 i64.eq
    if call $register_return else i64.const 5 i64.const 32 call $panic end))
