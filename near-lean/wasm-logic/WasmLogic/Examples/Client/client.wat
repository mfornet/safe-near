;; A client of the stack module (../Stack/stack.wat), after Iris-Wasm's
;; client examples: it makes a stack, pushes 4 then 6, pops twice and
;; returns the first value popped minus the second, 6 - 4 = 2, or -1 if
;; there is no memory left for a stack.
(module
  (import "stack" "new_stack" (func $new_stack (result i32)))
  (import "stack" "push" (func $push (param i32 i32)))
  (import "stack" "pop" (func $pop (param i32) (result i32)))
  (func (export "main") (result i32) (local $s i32)
    call $new_stack
    local.tee $s
    i32.const -1
    i32.eq
    if (result i32)
      i32.const -1
    else
      local.get $s
      i32.const 4
      call $push
      local.get $s
      i32.const 6
      call $push
      local.get $s
      call $pop
      local.get $s
      call $pop
      i32.sub
    end))
