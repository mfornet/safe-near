import NearVM
import Wasm.Wat

/-!
# Cryptographic host functions under `NearVM.run`

The primitives are replaced by a recording stub (`stub`), so these tests check what the VM itself
decides: the order of reads and charges, the argument errors and their messages, which
results are written to a register and the gas of writing them, and the return values. They run
Wasm modules, as `vm-tests` does for storage.
-/

open Wasm Wasm.Near

namespace CryptoHosts

private def hex2 (b : UInt8) : String :=
  let digits := Nat.toDigits 16 b.toNat
  String.join ((if digits.length < 2 then '0' :: digits else digits).map String.singleton)

private def esc (bytes : List UInt8) : String :=
  String.join (bytes.map fun b => "\\" ++ hex2 b)

/-- Primitives with recognisable outputs: a digest is its input length repeated, `ecrecover`
recovers a key for `v = 1` only, the verifiers accept a message that starts with `1` (`ed25519`) or
a key that starts with `2` (`p256`), `alt_bn128` rejects an input that starts with `255`, and the
`bls12381` sums return the behaviour version they were given (`none` for an input starting with `1`). -/
def stub : HostCrypto where
  sha256 m := List.replicate 32 (UInt8.ofNat m.length)
  keccak256 m := List.replicate 32 (UInt8.ofNat m.length + 1)
  keccak512 m := List.replicate 64 (UInt8.ofNat m.length)
  ripemd160 m := List.replicate 20 (UInt8.ofNat m.length)
  ecrecover _ _ v _ := if v == 1 then some (List.replicate 64 7) else none
  ed25519Verify _ msg _ := msg.head? == some 1
  p256Verify _ _ key := key.head? == some 2
  altBn128G1Multiexp d := if d.head? == some 255 then .error "bad point" else .ok (List.replicate 64 9)
  altBn128G1Sum d := if d.head? == some 255 then .error "bad point" else .ok (List.replicate 64 8)
  altBn128PairingCheck d := if d.head? == some 255 then .error "bad point" else .ok true
  bls12381P1Sum version d := .ok (if d.getD 1 0 == 1 then none else some (List.replicate 96 (UInt8.ofNat version)))
  bls12381P2Sum _ _ := .ok (some (List.replicate 192 2))
  bls12381G1Multiexp _ _ := .ok (some (List.replicate 96 3))
  bls12381G2Multiexp _ _ := .ok (some (List.replicate 192 4))
  bls12381MapFpToG1 _ d := .ok (some (List.replicate (2 * d.length) 5))
  bls12381MapFp2ToG2 _ d := .ok (some (List.replicate (2 * d.length) 6))
  bls12381P1Decompress _ d := .ok (some (List.replicate (2 * d.length) 7))
  bls12381P2Decompress _ _ := .error "no root"
  bls12381PairingCheck _ := .ok 2

private def build (name : String) (nparams : Nat) (hasResult : Bool) (mem : List UInt8)
    (args : List Int) (output : String) : IO Module := do
  let params := String.intercalate " " (List.replicate nparams "i64")
  let result := if hasResult then " (result i64)" else ""
  let pushed := String.intercalate " "
    (args.map fun a => s!"i64.const {if a ≥ 2 ^ 63 then a - 2 ^ 64 else a}")
  -- `status`: store the returned value at 1000 and return it; `register`: return register 1
  let body :=
    if output == "status" then s!"i32.const 1000 {pushed} call $f i64.store i64.const 8 i64.const 1000 call $ret"
    else s!"{pushed} call $f {if hasResult then "drop" else ""} i64.const -1 i64.const 1 call $ret"
  let text := s!"(module (import \"env\" \"{name}\" (func $f (param {params}){result}))
    (import \"env\" \"value_return\" (func $ret (param i64 i64)))
    (memory 1) (data (i32.const 0) \"{esc mem}\") (func (export \"test\") {body}))"
  match ← Wat.compile text with
  | .ok module => pure module
  | .error error => throw (IO.userError s!"crypto fixture {name}: {error}")

private def context : VMContext :=
  { currentAccountId := "crypto.near".toUTF8.toList
    signerAccountId := "alice.near".toUTF8.toList
    signerAccountPk := 0 :: List.replicate 32 1
    predecessorAccountId := "alice.near".toUTF8.toList
    input := [], prepaidGas := 300 * 10 ^ 12 }

private def cost (outcome : VMOutcome) (name : String) : Nat :=
  ((outcome.gasProfile.ext.find? (·.1 == name)).map (·.2)).getD 0

private def value (outcome : VMOutcome) : Option (List UInt8) :=
  match outcome.returnData with
  | .value bytes => some bytes
  | _ => none

private def le64 (n : Nat) : List UInt8 := (List.range 8).map fun i => UInt8.ofNat (n / 256 ^ i % 256)

private def failsWith (outcome : VMOutcome) (message : HostError) : Bool :=
  outcome.aborted == some (.hostError message)

def check (cfg : RuntimeConfig) (check : String → Bool → IO Unit) : IO Unit := do
  let price := cfg.wasm.extCosts.cost
  let withStub := { cfg with hostCrypto := some stub }
  let exec (module : Module) (config : RuntimeConfig := withStub) : VMOutcome :=
    run config module 0 "test" context []
  let bytes (n : Nat) : List UInt8 := (List.range n).map fun i => UInt8.ofNat (i % 200)
  let mem0 := bytes 200
  -- Digests: the bytes are read and paid, the digest is written to the register and paid.
  for (name, size, per, expected) in
      [("sha256", 32, "sha256_byte", List.replicate 32 (3 : UInt8)),
       ("keccak256", 32, "keccak256_byte", List.replicate 32 (4 : UInt8)),
       ("keccak512", 64, "keccak512_byte", List.replicate 64 (3 : UInt8))] do
    let o := exec (← build name 3 false mem0 [3, 0, 1] "register")
    check s!"{name}: digest in the register, bytes and register paid"
      (value o == some expected && cost o s!"{name}_base" == price s!"{name}_base" &&
        cost o per == 3 * price per && cost o "read_memory_byte" == 3 * price "read_memory_byte" &&
        cost o "write_register_byte" == size * price "write_register_byte")
  let o := exec (← build "ripemd160" 3 false mem0 [100, 0, 1] "register")
  check "ripemd160: (len + 8) / 64 + 1 blocks"
    (value o == some (List.replicate 20 100) && cost o "ripemd160_block" == 2 * price "ripemd160_block" &&
      cost o "write_register_byte" == 20 * price "write_register_byte")
  let o := exec (← build "sha256" 3 false mem0 [10, 1099511627776, 1] "register")
  check "sha256: out-of-bounds read pays the read, not the digest"
    (failsWith o .memoryAccessViolation && cost o "read_memory_byte" == 10 * price "read_memory_byte" &&
      cost o "sha256_byte" == 0 && cost o "write_register_base" == 0)
  let o := exec (← build "sha256" 3 false mem0 [2 ^ 64 - 1, 5, 1] "register")
  check "sha256: a missing input register is reported before any byte is paid"
    (failsWith o (.invalidRegisterId 5) && cost o "sha256_base" == price "sha256_base" && cost o "sha256_byte" == 0)
  let o := exec (← build "sha256" 3 false mem0 [2 ^ 64 - 2, 0, 1] "register")
  check "sha256: a length whose price overflows u64 is IntegerOverflow"
    (failsWith o .integerOverflow && cost o "read_memory_byte" == 0)
  let restricted := { withStub with wasm := { withStub.wasm with limits :=
    { withStub.wasm.limits with maxRegisterSize := 16 } } }
  let o := exec (← build "sha256" 3 false mem0 [3, 0, 1] "register") restricted
  check "sha256: a digest larger than a register is a memory access violation"
    (failsWith o .memoryAccessViolation)
  let o := exec (← build "sha256" 3 false mem0 [3, 0, 1] "register") cfg
  check "sha256: without cryptography the call is unsupported"
    (o.issue? == some (.unsupportedHost "sha256"))

  -- ecrecover(hash_len, hash_ptr, sig_len, sig_ptr, v, malleability_flag, register_id)
  let ec (args : List Int) := build "ecrecover" 7 true mem0 args "status"
  let o := exec (← ec [32, 0, 64, 32, 1, 0, 1])
  check "ecrecover: success returns 1; signature and hash are read; 64 bytes are written"
    (value o == some (le64 1) && cost o "ecrecover_base" == price "ecrecover_base" &&
      cost o "read_memory_byte" == (64 + 32 + 8) * price "read_memory_byte" &&
      cost o "write_register_byte" == 64 * price "write_register_byte")
  let o := exec (← build "ecrecover" 7 true mem0 [32, 0, 64, 32, 1, 1, 1] "register")
  check "ecrecover: the key goes to the register"
    (value o == some (List.replicate 64 7) && cost o "write_register_byte" == 64 * price "write_register_byte")
  let o := exec (← ec [32, 0, 64, 32, 0, 1, 1])
  check "ecrecover: an invalid signature returns 0 and writes nothing"
    (value o == some (le64 0) && cost o "write_register_base" == 0)
  let o := exec (← ec [32, 0, 63, 32, 1, 0, 1])
  check "ecrecover: signature length error precedes the hash read"
    (failsWith o (.ecRecoverError "The length of the signature: 63, exceeds the limit of 64 bytes") &&
      cost o "read_memory_byte" == 63 * price "read_memory_byte")
  let o := exec (← ec [32, 0, 64, 32, 4, 0, 1])
  check "ecrecover: v must be below 4, checked before the hash is read"
    (failsWith o (.ecRecoverError "V recovery byte 0 through 3 are valid but was provided 4") &&
      cost o "read_memory_byte" == 64 * price "read_memory_byte")
  let o := exec (← ec [31, 0, 64, 32, 1, 0, 1])
  check "ecrecover: hash length error"
    (failsWith o (.ecRecoverError "The length of the hash: 31, exceeds the limit of 32 bytes") &&
      cost o "read_memory_byte" == (64 + 31) * price "read_memory_byte")
  let o := exec (← ec [32, 0, 64, 32, 1, 2, 1])
  check "ecrecover: the malleability flag is checked after both reads"
    (failsWith o (.ecRecoverError "Malleability flag needs to be 0 or 1, but is instead 2") &&
      cost o "read_memory_byte" == (64 + 32) * price "read_memory_byte")

  -- ed25519_verify(sig_len, sig_ptr, msg_len, msg_ptr, pk_len, pk_ptr); the message at 64 starts with 1
  let sigMsgKey := List.replicate 63 3 ++ [3] ++ [1, 2, 3, 4, 5] ++ List.replicate 32 4
  let ed (mem : List UInt8) (args : List Int) := build "ed25519_verify" 6 true mem args "status"
  let o := exec (← ed sigMsgKey [64, 0, 5, 64, 32, 69])
  check "ed25519_verify: success; the message bytes are paid"
    (value o == some (le64 1) && cost o "ed25519_verify_byte" == 5 * price "ed25519_verify_byte" &&
      cost o "read_memory_byte" == (64 + 5 + 32 + 8) * price "read_memory_byte")
  let highBits := List.replicate 63 3 ++ [0xE0] ++ [1, 2, 3, 4, 5] ++ List.replicate 32 4
  let o := exec (← ed highBits [64, 0, 5, 64, 32, 69])
  check "ed25519_verify: a signature with the top bits set is 0 before the message is read"
    (value o == some (le64 0) && cost o "ed25519_verify_byte" == 0 &&
      cost o "read_memory_byte" == (64 + 8) * price "read_memory_byte")
  let o := exec (← ed sigMsgKey [63, 0, 5, 64, 32, 69])
  check "ed25519_verify: signature length"
    (failsWith o (.ed25519VerifyInvalidInput "invalid signature length"))
  let o := exec (← ed sigMsgKey [64, 0, 5, 64, 31, 69])
  check "ed25519_verify: key length is checked after the message is paid"
    (failsWith o (.ed25519VerifyInvalidInput "invalid public key length") &&
      cost o "ed25519_verify_byte" == 5 * price "ed25519_verify_byte")

  -- p256_verify: the signature is `r || s`, both in [1, n - 1]; the key at 69 is 33 bytes
  let p256mem (sig : List UInt8) := sig ++ [1, 2, 3, 4, 5] ++ [2] ++ List.replicate 32 4
  let pv (mem : List UInt8) (args : List Int) := build "p256_verify" 6 true mem args "status"
  let sigOk := List.replicate 31 0 ++ [1] ++ List.replicate 31 0 ++ [1]
  let o := exec (← pv (p256mem sigOk) [64, 0, 5, 64, 33, 69])
  check "p256_verify: success; the message bytes are paid"
    (value o == some (le64 1) && cost o "p256_verify_base" == price "p256_verify_base" &&
      cost o "p256_verify_byte" == 5 * price "p256_verify_byte")
  let o := exec (← pv (p256mem (List.replicate 64 0)) [64, 0, 5, 64, 33, 69])
  check "p256_verify: a signature outside [1, n - 1] is 0 before the message is read"
    (value o == some (le64 0) && cost o "p256_verify_byte" == 0)
  let o := exec (← pv (p256mem (List.replicate 64 255)) [64, 0, 5, 64, 33, 69])
  check "p256_verify: r and s must be below the group order"
    (value o == some (le64 0) && cost o "p256_verify_byte" == 0)
  let o := exec (← pv (p256mem sigOk) [64, 0, 5, 64, 32, 69])
  check "p256_verify: key length"
    (failsWith o (.p256VerifyInvalidInput "invalid public key length"))
  let o := exec (← pv (p256mem sigOk) [65, 0, 5, 64, 33, 69])
  check "p256_verify: signature length"
    (failsWith o (.p256VerifyInvalidInput "invalid signature length"))

  -- alt_bn128
  let g1 := bytes 96
  let o := exec (← build "alt_bn128_g1_multiexp" 3 false g1 [96, 0, 1] "register")
  check "alt_bn128_g1_multiexp: elements are paid, the result is written and paid"
    (value o == some (List.replicate 64 9) &&
      cost o "alt_bn128_g1_multiexp_base" == price "alt_bn128_g1_multiexp_base" &&
      cost o "alt_bn128_g1_multiexp_element" == price "alt_bn128_g1_multiexp_element" &&
      cost o "write_register_byte" == 64 * price "write_register_byte")
  let o := exec (← build "alt_bn128_g1_multiexp" 3 false g1 [95, 0, 1] "register")
  check "alt_bn128_g1_multiexp: an inexact length is an error before the elements are paid"
    (failsWith o (.altBn128InvalidInput "slice of size 95 cannot be precisely split into chunks of size 96") &&
      cost o "alt_bn128_g1_multiexp_element" == 0)
  let o := exec (← build "alt_bn128_g1_multiexp" 3 false (255 :: bytes 95) [96, 0, 1] "register")
  check "alt_bn128_g1_multiexp: an invalid element is an error; the register is not paid"
    (failsWith o (.altBn128InvalidInput "bad point") &&
      cost o "alt_bn128_g1_multiexp_element" == price "alt_bn128_g1_multiexp_element" &&
      cost o "write_register_base" == 0)
  let o := exec (← build "alt_bn128_g1_sum" 3 false (bytes 130) [130, 0, 1] "register")
  check "alt_bn128_g1_sum: two 65-byte elements"
    (value o == some (List.replicate 64 8) && cost o "alt_bn128_g1_sum_element" == 2 * price "alt_bn128_g1_sum_element")
  let o := exec (← build "alt_bn128_pairing_check" 2 true (bytes 192) [192, 0] "status")
  check "alt_bn128_pairing_check: returns 1 and pays one element"
    (value o == some (le64 1) &&
      cost o "alt_bn128_pairing_check_element" == price "alt_bn128_pairing_check_element")
  let o := exec (← build "alt_bn128_pairing_check" 2 true (bytes 191) [191, 0] "status")
  check "alt_bn128_pairing_check: inexact length"
    (failsWith o (.altBn128InvalidInput "slice of size 191 cannot be precisely split into chunks of size 192") &&
      cost o "alt_bn128_pairing_check_element" == 0)

  -- bls12381
  let bls (name : String) (n : Nat) (hasRegister : Bool) (mem : List UInt8) (args : List Int) (output : String) :=
    build name n hasRegister mem args output
  let sumItem := (0 : UInt8) :: bytes 96
  let o := exec (← bls "bls12381_p1_sum" 3 true sumItem [97, 0, 1] "register")
  check "bls12381_p1_sum: status 0, the version 0 result is written and paid"
    (value o == some (List.replicate 96 0) &&
      cost o "bls12381_p1_sum_element" == price "bls12381_p1_sum_element" &&
      cost o "write_register_byte" == 96 * price "write_register_byte")
  let fixed := { withStub with wasm := { withStub.wasm with bls12381NotInGroupFix := true } }
  let o := exec (← bls "bls12381_p1_sum" 3 true sumItem [97, 0, 1] "register") fixed
  check "bls12381_p1_sum: bls12381_not_in_group_fix selects behaviour version 1"
    (value o == some (List.replicate 96 1))
  let o := exec (← bls "bls12381_p1_sum" 3 true sumItem [97, 0, 1] "status")
  check "bls12381_p1_sum: returns status 0 (the register is not read)"
    (value o == some (le64 0))
  let invalid := [(0 : UInt8), 1] ++ bytes 95
  let o := exec (← bls "bls12381_p1_sum" 3 true invalid [97, 0, 1] "status")
  check "bls12381_p1_sum: an invalid point is status 1 and nothing is written"
    (value o == some (le64 1) && cost o "write_register_base" == 0)
  let o := exec (← bls "bls12381_p1_sum" 3 true (bytes 98) [98, 0, 1] "status")
  check "bls12381_p1_sum: the elements are paid from the length before the length error"
    (failsWith o (.bls12381InvalidInput "Incorrect input length for bls12381_p1_sum: 98 is not divisible by 97") &&
      cost o "bls12381_p1_sum_element" == price "bls12381_p1_sum_element")
  let o := exec (← bls "bls12381_g1_multiexp" 3 true (bytes 129) [129, 0, 1] "status")
  check "bls12381_g1_multiexp: the length error names the p1 function"
    (failsWith o (.bls12381InvalidInput "Incorrect input length for bls12381_p1_multiexp: 129 is not divisible by 128"))
  let o := exec (← bls "bls12381_g2_multiexp" 3 true (bytes 225) [225, 0, 1] "status")
  check "bls12381_g2_multiexp: the length error names the p2 function"
    (failsWith o (.bls12381InvalidInput "Incorrect input length for bls12381_p2_multiexp: 225 is not divisible by 224"))
  let o := exec (← bls "bls12381_map_fp_to_g1" 3 true (bytes 49) [49, 0, 1] "status")
  check "bls12381_map_fp_to_g1: length error"
    (failsWith o (.bls12381InvalidInput "Incorrect input length for bls12381_map_fp_to_g1: 49 is not divisible by 48"))
  let o := exec (← bls "bls12381_map_fp2_to_g2" 3 true (bytes 96) [96, 0, 1] "register")
  check "bls12381_map_fp2_to_g2: one element, 192 bytes written"
    (value o == some (List.replicate 192 6) &&
      cost o "bls12381_map_fp2_to_g2_element" == price "bls12381_map_fp2_to_g2_element")
  let o := exec (← bls "bls12381_p1_decompress" 3 true (bytes 96) [96, 0, 1] "register")
  check "bls12381_p1_decompress: two elements"
    (value o == some (List.replicate 192 7) &&
      cost o "bls12381_p1_decompress_element" == 2 * price "bls12381_p1_decompress_element")
  let o := exec (← bls "bls12381_p2_decompress" 3 true (bytes 96) [96, 0, 1] "status")
  check "bls12381_p2_decompress: a primitive error is a BLS12381InvalidInput"
    (failsWith o (.bls12381InvalidInput "no root"))
  let o := exec (← bls "bls12381_p1_sum" 3 true (bytes 97) [2 ^ 64 - 1, 5, 1] "status")
  check "bls12381_p1_sum: a register input overflows the element price before anything is read"
    (failsWith o .integerOverflow && cost o "bls12381_p1_sum_base" == price "bls12381_p1_sum_base" &&
      cost o "bls12381_p1_sum_element" == 0)
  let o := exec (← bls "bls12381_pairing_check" 2 true (bytes 576) [576, 0] "status")
  check "bls12381_pairing_check: two elements, status from the primitive"
    (value o == some (le64 2) && cost o "bls12381_pairing_element" == 2 * price "bls12381_pairing_element")
  let o := exec (← bls "bls12381_pairing_check" 2 true (bytes 289) [289, 0] "status")
  check "bls12381_pairing_check: the elements are paid on the bytes read, then the length error"
    (failsWith o (.bls12381InvalidInput "Incorrect input length for bls12381_pairing_check: 289 is not divisible by 288") &&
      cost o "bls12381_pairing_element" == price "bls12381_pairing_element")

end CryptoHosts
