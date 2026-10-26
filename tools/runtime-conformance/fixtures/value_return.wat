(module
  (import "env" "value_return" (func $return (param i64 i64)))
  (memory 1)
  (data (i32.const 0) "abc")
  (func (export "small") i64.const 3 i64.const 0 call $return)
  (func (export "oob") i64.const 16 i64.const 68719476720 call $return)
  ;; nearcore prepares 64 pages, max_length_returned_data bytes; one more page fits one byte over.
  (func (export "at_limit") i32.const 1 memory.grow drop i64.const 4194304 i64.const 0 call $return)
  (func (export "over_limit") i32.const 1 memory.grow drop i64.const 4194305 i64.const 0 call $return)
)
