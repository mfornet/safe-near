(module
  (import "env" "storage_write" (func $write (param i64 i64 i64 i64 i64) (result i64)))
  (memory 1)
  (data (i32.const 0) "k")
  (data (i32.const 8) "new")
  (func (export "write")
    i64.const 1 i64.const 0 i64.const 3 i64.const 8 i64.const 0 call $write drop))
