(module
  (import "env" "promise_create" (func $create (param i64 i64 i64 i64 i64 i64 i64 i64) (result i64)))
  (import "env" "promise_then" (func $then (param i64 i64 i64 i64 i64 i64 i64 i64 i64) (result i64)))
  (import "env" "promise_return" (func $return (param i64)))
  (import "env" "promise_result" (func $result (param i64 i64) (result i64)))
  (import "env" "storage_write" (func $write (param i64 i64 i64 i64 i64) (result i64)))
  (import "env" "value_return" (func $value (param i64 i64)))
  (import "env" "panic_utf8" (func $panic (param i64 i64)))
  (memory 2)
  (data (i32.const 0) "wrap.near")
  (data (i32.const 16) "near_deposit")
  (data (i32.const 32) "near_withdraw")
  (data (i32.const 48) "observer.near")
  (data (i32.const 64) "callback")
  (data (i32.const 80) "{}")
  (data (i32.const 96) "\7b\22\61\6d\6f\75\6e\74\22\3a\22\31\30\30\30\30\30\30\30\30\30\30\30\30\30\30\30\30\30\30\30\30\30\30\22\7d")
  (data (i32.const 160) "\00\00\00\a1\ed\cc\ce\1b\c2\d3\00\00\00\00\00\00")
  (data (i32.const 176) "\01")
  (data (i32.const 224) "ok")
  (data (i32.const 232) "large")
  (func (export "deposit")
    i64.const 9 i64.const 0 i64.const 12 i64.const 16
    i64.const 2 i64.const 80 i64.const 160 i64.const 100000000000000
    call $create call $return)
  (func $withdraw (param $callbackGas i64) (local $p i64)
    i64.const 9 i64.const 0 i64.const 13 i64.const 32
    i64.const 36 i64.const 96 i64.const 176 i64.const 60000000000000
    call $create local.set $p
    local.get $p i64.const 13 i64.const 48 i64.const 8 i64.const 64
    i64.const 2 i64.const 80 i64.const 192 local.get $callbackGas
    call $then call $return)
  (func (export "withdraw") i64.const 20000000000000 call $withdraw)
  (func (export "withdraw_low_gas") i64.const 1 call $withdraw)
  (func (export "callback")
    i32.const 256 i64.const 0 i64.const 0 call $result i32.wrap_i64 i32.store8
    i64.const 8 i64.const 64 i64.const 1 i64.const 256 i64.const 7 call $write drop
    i64.const 1 i64.const 256 call $value)
  (data (i32.const 336) "caller.near")
  (data (i32.const 352) "poor.near")
  (data (i32.const 368) "value")
  (data (i32.const 384) "panic")
  (data (i32.const 400) "write_too_much")
  (func $probe (param $receiverLen i64) (param $receiverPtr i64) (param $methodLen i64) (param $methodPtr i64) (local $p i64)
    local.get $receiverLen local.get $receiverPtr local.get $methodLen local.get $methodPtr
    i64.const 2 i64.const 80 i64.const 192 i64.const 60000000000000
    call $create local.set $p
    local.get $p i64.const 13 i64.const 48 i64.const 8 i64.const 64
    i64.const 2 i64.const 80 i64.const 192 i64.const 20000000000000
    call $then call $return)
  (func (export "probe_value")
    i64.const 11 i64.const 336 i64.const 5 i64.const 368 call $probe)
  (func (export "probe_panic")
    i64.const 11 i64.const 336 i64.const 5 i64.const 384 call $probe)
  (func (export "probe_storage")
    i64.const 9 i64.const 352 i64.const 14 i64.const 400 call $probe)
  (func (export "value") i64.const 2 i64.const 224 call $value)
  (func (export "write_too_much")
    i64.const 5 i64.const 232 i64.const 100000 i64.const 4096 i64.const 7 call $write drop
    i64.const 2 i64.const 224 call $value)
  (func (export "panic") i64.const 2 i64.const 224 call $panic)
)
