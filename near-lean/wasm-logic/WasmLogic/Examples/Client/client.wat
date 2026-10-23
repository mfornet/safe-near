;; The client of Iris-Wasm's stack module (theories/iris/examples/stack/
;; stack_client.v), written as text: the same types, imports, global, element
;; segment and functions, in the same order. It imports the stack's functions
;; and table, puts `square` in table entry 0, and its start function `main`
;; makes a stack, pushes 4 and 6, squares every element with stack_map, pops
;; 36 and 16 and stores their difference, 20, in the exported global
;; `answer`; or stores -1 if no stack could be made.
(module
  (type (func))
  (type (func (result i32)))
  (type (func (param i32) (result i32)))
  (type (func (param i32 i32)))
  (import "stack" "new_stack" (func $new_stack (type 1)))
  (import "stack" "is_empty" (func $is_empty (type 2)))
  (import "stack" "is_full" (func $is_full (type 2)))
  (import "stack" "pop" (func $pop (type 2)))
  (import "stack" "push" (func $push (type 3)))
  (import "stack" "stack_map" (func $stack_map (type 3)))
  (import "stack" "stack_length" (func $stack_length (type 2)))
  (import "stack" "table" (table 1 funcref))
  (global $answer (mut i32) (i32.const 0))
  (export "answer" (global $answer))
  (start $main)
  (elem (i32.const 0) func $square)

  (func $main (type 0) (local i32)
    call $new_stack
    local.tee 0
    i32.const -1
    i32.eq
    if
      i32.const -1
      global.set $answer
      return
    end
    local.get 0
    i32.const 4
    call $push
    local.get 0
    i32.const 6
    call $push
    local.get 0
    i32.const 0
    call $stack_map
    local.get 0
    call $pop
    local.get 0
    call $pop
    i32.sub
    global.set $answer)

  (func $square (type 2)
    local.get 0
    local.get 0
    i32.mul))
