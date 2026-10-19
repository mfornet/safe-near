(module
  (import "env" "value_return" (func $return (param i64 i64)))
  (import "env" "panic_utf8" (func $panic (param i64 i64)))
  (import "env" "used_gas" (func $used_gas (result i64)))
  (import "env" "storage_write" (func $write (param i64 i64 i64 i64 i64) (result i64)))
  (import "env" "storage_iter_prefix" (func $iterator (param i64 i64) (result i64)))
  (import "env" "predecessor_account_id" (func $predecessor (param i64)))
  (import "env" "promise_results_count" (func $results_count (result i64)))
  (memory 1)
  (data (i32.const 16) "boom")
  (func (export "memory_size")
    i32.const 0
    memory.size
    i32.store
    i64.const 4
    i64.const 0
    call $return)
  (func (export "memory_grow")
    i32.const 0
    i32.const 1
    memory.grow
    i32.store
    i64.const 4
    i64.const 0
    call $return)
  (func (export "after_grow")
    i32.const 1
    memory.grow
    drop
    i32.const 0
    memory.size
    i32.store
    i64.const 4
    i64.const 0
    call $return)
  (func (export "panic")
    i64.const 4
    i64.const 16
    call $panic
    unreachable)
  (func (export "out_of_bounds")
    i32.const 67108864
    i32.load8_u
    drop)
  (func (export "divide_by_zero")
    i32.const 1
    i32.const 0
    i32.div_u
    drop)
  (func (export "unreachable") unreachable)
  (func (export "wrong_signature") (param i32))
  (func (export "loop_backedge") (local $i i32)
    i32.const 10
    local.set $i
    block $exit
      loop $again
        local.get $i
        i32.eqz
        br_if $exit
        local.get $i
        i32.const 1
        i32.sub
        local.set $i
        br $again
      end
    end)
  (func (export "loop_conditional_backedge") (local $i i32)
    i32.const 10
    local.set $i
    loop $again
      local.get $i
      i32.const 1
      i32.sub
      local.tee $i
      br_if $again
    end)
  (func (export "used_gas")
    i32.const 0
    call $used_gas
    i64.store
    i64.const 8
    i64.const 0
    call $return)
  (func (export "write")
    i64.const 1
    i64.const 16
    i64.const 1
    i64.const 17
    i64.const 0
    call $write
    drop)
  (func (export "iterator")
    i64.const 0
    i64.const 0
    call $iterator
    drop)
  (func (export "predecessor") i64.const 0 call $predecessor)
  (func (export "results_count") call $results_count drop)
  (func (export "empty")))
