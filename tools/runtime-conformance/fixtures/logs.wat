(module
  (import "env" "log_utf8" (func $log8 (param i64 i64)))
  (import "env" "log_utf16" (func $log16 (param i64 i64)))
  (memory 1)
  (data (i32.const 0) "hello")
  (data (i32.const 16) "\ff\fe")
  (data (i32.const 32) "h\00i\00")
  (data (i32.const 48) "\e9\00")
  (data (i32.const 64) "\00\d8a\00")
  ;; 20000 bytes of 'a' at 1024, filled on demand.
  (func $fill i32.const 1024 i32.const 97 i32.const 20000 memory.fill)
  (func (export "hello") i64.const 5 i64.const 0 call $log8)
  (func (export "many") (local i32)
    loop
      i64.const 1 i64.const 0 call $log8
      local.get 0 i32.const 1 i32.add local.tee 0
      i32.const 101 i32.lt_u br_if 0
    end)
  (func (export "running_total") (local i32)
    call $fill
    loop
      i64.const 2000 i64.const 1024 call $log8
      local.get 0 i32.const 1 i32.add local.tee 0
      i32.const 9 i32.lt_u br_if 0
    end)
  (func (export "too_long") call $fill i64.const 16385 i64.const 1024 call $log8)
  (func (export "at_limit") call $fill i64.const 16384 i64.const 1024 call $log8)
  (func (export "bad_utf8") i64.const 2 i64.const 16 call $log8)
  (func (export "oob") i64.const 8 i64.const 68719476720 call $log8)
  (func (export "utf16") i64.const 4 i64.const 32 call $log16)
  (func (export "utf16_non_ascii") i64.const 2 i64.const 48 call $log16)
  (func (export "utf16_odd") i64.const 3 i64.const 32 call $log16)
  (func (export "utf16_surrogate") i64.const 4 i64.const 64 call $log16)
  (func (export "utf16_oob") i64.const 8 i64.const 68719476720 call $log16)
  (func (export "utf16_running_total") (local i32)
    call $fill
    loop
      i64.const 2000 i64.const 1024 call $log16
      local.get 0 i32.const 1 i32.add local.tee 0
      i32.const 17 i32.lt_u br_if 0
    end)
)
