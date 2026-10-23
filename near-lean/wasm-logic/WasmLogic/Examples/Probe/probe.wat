;; A second client of the stack module (../Stack/stack.wat), for the stack
;; functions Iris-Wasm's client does not call. Its start function makes a
;; stack and records in the global `answer`, as decimal digits:
;; is_empty before a push (1), is_empty after pushing 4 (0, tens),
;; is_full (0, hundreds) and stack_length (1, thousands): 1001. It stores -1
;; if no stack could be made.
(module
  (type (func))
  (type (func (result i32)))
  (type (func (param i32) (result i32)))
  (type (func (param i32 i32)))
  (import "stack" "new_stack" (func $new_stack (type 1)))
  (import "stack" "is_empty" (func $is_empty (type 2)))
  (import "stack" "is_full" (func $is_full (type 2)))
  (import "stack" "push" (func $push (type 3)))
  (import "stack" "stack_length" (func $stack_length (type 2)))
  (global $answer (mut i32) (i32.const 0))
  (export "answer" (global $answer))
  (start $main)

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
    call $is_empty
    local.get 0
    i32.const 4
    call $push
    local.get 0
    call $is_empty
    i32.const 10
    i32.mul
    i32.add
    local.get 0
    call $is_full
    i32.const 100
    i32.mul
    i32.add
    local.get 0
    call $stack_length
    i32.const 1000
    i32.mul
    i32.add
    global.set $answer))
