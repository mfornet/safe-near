;; The stack module of Iris-Wasm (theories/iris/examples/stack/), written as
;; text: the same types, functions, table and memory, in the same order, so
;; that the binary the logic reasons about is the module Iris-Wasm verified.
;; Loads and stores use alignment 2^0, as Iris-Wasm's `BI_load T_i32 None 0 0`.
;;
;; A stack lives in its own 64 KiB page starting at address v: the cell at v
;; holds the address of the top element; elements grow upwards from v + 4.
(module
  (type (func (result i32)))
  (type (func (param i32) (result i32)))
  (type (func (param i32 i32)))
  (table 1 funcref)
  (memory 0)

  ;; new_stack: grow memory by a page and make it an empty stack.
  (func (type 0) (local i32)
    i32.const 1
    memory.grow
    local.tee 0
    i32.const -1
    i32.eq
    if (result i32)
      i32.const -1
    else
      local.get 0
      i32.const 65536
      i32.mul
      local.tee 0
      local.get 0
      i32.store align=1
      local.get 0
    end)

  ;; is_empty
  (func (type 1)
    local.get 0 i32.const 65536 i32.rem_u if unreachable end
    local.get 0 i32.load align=1 drop
    local.get 0
    local.get 0
    i32.load align=1
    i32.eq)

  ;; is_full
  (func (type 1)
    local.get 0 i32.const 65536 i32.rem_u if unreachable end
    local.get 0 i32.load align=1 drop
    i32.const 1
    i32.const 0
    local.get 0
    i32.load align=1
    i32.const 65536
    i32.rem_u
    i32.const 65532
    i32.eq
    select)

  ;; pop
  (func (type 1) (local i32)
    local.get 0 i32.const 65536 i32.rem_u if unreachable end
    local.get 0 i32.load align=1 drop
    local.get 0
    local.get 0
    i32.load align=1
    i32.eq
    if unreachable end
    local.get 0
    i32.load align=1
    local.tee 1
    i32.load align=1
    local.get 0
    local.get 1
    i32.const 4
    i32.sub
    i32.store align=1)

  ;; push
  (func (type 2) (local i32)
    local.get 0 i32.const 65536 i32.rem_u if unreachable end
    local.get 0 i32.load align=1 drop
    i32.const 1
    i32.const 0
    local.get 0
    i32.load align=1
    i32.const 65536
    i32.rem_u
    i32.const 65532
    i32.eq
    select
    if unreachable end
    local.get 0
    i32.load align=1
    i32.const 4
    i32.add
    local.tee 2
    local.get 1
    i32.store align=1
    local.get 0
    local.get 2
    i32.store align=1)

  ;; stack_map
  (func (type 2) (local i32 i32)
    local.get 0 i32.const 65536 i32.rem_u if unreachable end
    local.get 0 i32.load align=1 drop
    local.get 0
    i32.load align=1
    local.set 3
    local.get 0
    local.set 2
    block
      loop
        local.get 2
        local.get 3
        i32.eq
        br_if 1
        local.get 2
        i32.const 4
        i32.add
        local.tee 2
        local.get 2
        i32.load align=1
        local.get 1
        call_indirect (type 1)
        i32.store align=1
        br 0
      end
    end)

  ;; stack_length
  (func (type 1)
    local.get 0 i32.const 65536 i32.rem_u if unreachable end
    local.get 0 i32.load align=1 drop
    local.get 0
    i32.load align=1
    local.get 0
    i32.sub
    i32.const 4
    i32.div_u)

  (export "new_stack" (func 0))
  (export "is_empty" (func 1))
  (export "is_full" (func 2))
  (export "pop" (func 3))
  (export "push" (func 4))
  (export "stack_map" (func 5))
  (export "stack_length" (func 6))
  (export "table" (table 0)))
