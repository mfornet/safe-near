(module
  (import "env" "sha256" (func $sha256 (param i64 i64 i64)))
  (import "env" "keccak256" (func $keccak256 (param i64 i64 i64)))
  (import "env" "keccak512" (func $keccak512 (param i64 i64 i64)))
  (import "env" "ripemd160" (func $ripemd160 (param i64 i64 i64)))
  (import "env" "read_register" (func $read (param i64 i64)))
  (import "env" "value_return" (func $return (param i64 i64)))
  (memory 1)
  (data (i32.const 0) "abc")
  ;; 1000 bytes of 'q' at 1024, written on demand: several blocks of every hash.
  (func $fill i32.const 1024 i32.const 113 i32.const 1000 memory.fill)
  ;; Hash `len` bytes at `ptr` with `op`, then return register 0.
  (func $finish i64.const -1 i64.const 0 call $return)
  (func (export "sha256_empty") i64.const 0 i64.const 0 i64.const 0 call $sha256 call $finish)
  (func (export "sha256_abc") i64.const 3 i64.const 0 i64.const 0 call $sha256 call $finish)
  (func (export "sha256_long") call $fill i64.const 1000 i64.const 1024 i64.const 0 call $sha256 call $finish)
  (func (export "keccak256_empty") i64.const 0 i64.const 0 i64.const 0 call $keccak256 call $finish)
  (func (export "keccak256_abc") i64.const 3 i64.const 0 i64.const 0 call $keccak256 call $finish)
  (func (export "keccak256_long") call $fill i64.const 1000 i64.const 1024 i64.const 0 call $keccak256 call $finish)
  (func (export "keccak512_empty") i64.const 0 i64.const 0 i64.const 0 call $keccak512 call $finish)
  (func (export "keccak512_abc") i64.const 3 i64.const 0 i64.const 0 call $keccak512 call $finish)
  (func (export "keccak512_long") call $fill i64.const 1000 i64.const 1024 i64.const 0 call $keccak512 call $finish)
  (func (export "ripemd160_empty") i64.const 0 i64.const 0 i64.const 0 call $ripemd160 call $finish)
  (func (export "ripemd160_abc") i64.const 3 i64.const 0 i64.const 0 call $ripemd160 call $finish)
  (func (export "ripemd160_long") call $fill i64.const 1000 i64.const 1024 i64.const 0 call $ripemd160 call $finish)
  ;; Hash the previous digest from register 0.
  (func (export "chained") i64.const 3 i64.const 0 i64.const 0 call $sha256
    i64.const -1 i64.const 0 i64.const 1 call $keccak256
    i64.const -1 i64.const 1 i64.const 2 call $ripemd160
    i64.const -1 i64.const 2 call $return)
  (func (export "oob") i64.const 8 i64.const 68719476720 i64.const 0 call $sha256)
  (func (export "bad_register") i64.const -1 i64.const 9 i64.const 0 call $keccak512)
)
