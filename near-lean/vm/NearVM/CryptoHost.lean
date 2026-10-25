import NearVM.Charge

/-!
# Cryptographic host functions: arguments, gas and errors

`near_vm_runner::logic::VMLogic::{sha256, keccak256, keccak512, ripemd160, ecrecover,
ed25519_verify, p256_verify, alt_bn128_*, bls12381_*}` split into what the VM decides and what the
cryptography decides. The VM reads the arguments (from memory or a register), pays for them in the
order the Rust code does, validates lengths and flags, and raises its structured errors; only on
well-formed arguments does it ask `NearState.crypto` for the primitive. `cryptoEval` returns all of
that for one call:

* `charges`: what is paid before the primitive runs, up to the point where the call ends;
* `error`: the error that ends the call at that point, if any;
* `compute`: the outcome of the primitive (not run when `error` is set).

`Metered.chargesBefore` reads the first, and the host function (`Host.cryptoHostFn`) raises the
second and runs the third, so the order of reads, charges and checks is written
once. The gas of writing the result register depends on the outcome and is charged afterwards
(`NearState.registerWrite`).

nearcore divergence: the injected primitive (`HostCrypto`) replaces `sha2`, `sha3`, `ripemd`,
`secp256k1`, `ed25519-dalek`, `p256`, `zeropool-bn` and `blst`; the messages of the `alt_bn128`
errors for an invalid point (which include the offending bytes) are those of the primitive.
-/

namespace Wasm.Near

/-- One `ExtCosts` charge: the name and the count. The charges of a cryptographic host function
are all of this form, which keeps them free of action fees and receipt reservations. -/
def ext1 (name : String) (times : Nat := 1) : String × Nat :=
  (name, times)

/-- `readSpan` as ext-cost pairs. -/
def readSpanP (st : HostStore NearState) (len ptr : UInt64) : List (String × Nat) :=
  if len = u64Max then
    match st.host.registers ptr.toNat with
    | none => []
    | some bytes => [ext1 "read_register_base", ext1 "read_register_byte" bytes.length]
  else [ext1 "read_memory_base", ext1 "read_memory_byte" len.toNat]

/-- The charges as the metered wrapper applies them. -/
def extCharges (cs : List (String × Nat)) : List Charge :=
  cs.map fun (name, times) => .ext name times

/-- What a cryptographic host function does once its arguments are validated. -/
inductive CryptoOutcome where
  | trap (error : HostError)
  /-- Return `results`; write the bytes to the register when given. -/
  | done (results : List Value) (write : Option (UInt64 × List UInt8))

/-- The charges, argument error and outcome of one call of a cryptographic host function. -/
structure CryptoEval where
  charges : List (String × Nat)
  error : Option HostError := none
  compute : Unit → CryptoOutcome := fun _ => .done [] none

/-- The call ends with `error` after paying `acc`. -/
def cryptoStop (acc : List (String × Nat)) (error : HostError) : CryptoEval :=
  { charges := acc, error := some error }

/-- `GasCounter::pay_per` multiplies the cost by the count as a checked `u64`; the host
function fails with `IntegerOverflow` before burning anything when the product does not fit. -/
def payPerOverflows (st : HostStore NearState) (cost : String) (times : Nat) : Bool :=
  decide (st.host.extCosts.cost cost * times ≥ 2 ^ 64)

/-- Read the `(len, ptr)` argument (`get_memory_or_register`): its charges join `acc`, and a
failed read ends the call. -/
def cryptoRead (st : HostStore NearState) (len ptr : UInt64) (acc : List (String × Nat))
    (k : List UInt8 → List (String × Nat) → CryptoEval) : CryptoEval :=
  if len != u64Max && payPerOverflows st "read_memory_byte" len.toNat then
    cryptoStop (acc ++ [ext1 "read_memory_base"]) .integerOverflow
  else
    let acc := acc ++ readSpanP st len ptr
    match getMemOrReg st ptr len with
    | none => cryptoStop acc (spanReadError len ptr)
    | some bytes => k bytes acc

/-- Run the primitive, or report the host function as unsupported without one. -/
def withCrypto (st : HostStore NearState) (name : String) (k : HostCrypto → CryptoOutcome) :
    CryptoOutcome :=
  match st.host.crypto with
  | none => .trap (.unsupported name)
  | some crypto => k crypto

/-- `sha256`, `keccak256`, `keccak512`, `ripemd160`: the function's base cost, the read, then the
cost of the bytes (or blocks). None of the cryptographic host functions pays the generic `base`
cost, unlike most others: their own base cost stands in for it. -/
def digestEval (name : String) (st : HostStore NearState) (args : List Value)
    (per : Nat → List (String × Nat)) (hash : HostCrypto → List UInt8 → List UInt8) : CryptoEval :=
  let a := argU64 args
  cryptoRead st (a 0) (a 1) [ext1 (name ++ "_base")] fun value acc =>
    { charges := acc ++ per value.length
      compute := fun _ =>
        withCrypto st name fun crypto => .done [] (some (a 2, hash crypto value)) }

/-- `ecrecover(hash_len, hash_ptr, sig_len, sig_ptr, v, malleability_flag, register_id)`: the
signature is read and checked first, then `v`, then the hash, then the flag. -/
def ecrecoverEval (st : HostStore NearState) (args : List Value) : CryptoEval :=
  let a := argU64 args
  cryptoRead st (a 2) (a 3) [ext1 "ecrecover_base"] fun sig acc =>
    if sig.length != 64 then
      cryptoStop acc
        (.ecRecoverError
          s!"The length of the signature: {sig.length}, exceeds the limit of 64 bytes")
    else
      if a 4 ≥ 4 then
        cryptoStop acc
          (.ecRecoverError s!"V recovery byte 0 through 3 are valid but was provided {(a 4).toNat}")
      else
        cryptoRead st (a 0) (a 1) acc fun hash acc =>
          if hash.length != 32 then
            cryptoStop acc
              (.ecRecoverError
                s!"The length of the hash: {hash.length}, exceeds the limit of 32 bytes")
          else
            if a 5 != 0 && a 5 != 1 then
              cryptoStop acc
                (.ecRecoverError
                  s!"Malleability flag needs to be 0 or 1, but is instead {(a 5).toNat}")
            else
              { charges := acc
                compute := fun _ =>
                  withCrypto st "ecrecover" fun crypto =>
                    match crypto.ecrecover hash sig (a 4).toNat (a 5 != 0) with
                    | some key => .done [.i64 1] (some (a 6, key))
                    | none => .done [.i64 0] none }

/-- The order of the P-256 group. -/
def p256Order : Nat :=
  0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551

/-- The number a big-endian byte string spells. -/
def beNat (bytes : List UInt8) : Nat :=
  bytes.foldl (fun acc byte => acc * 256 + byte.toNat) 0

/-- `Signature::from_slice`: `r` and `s` are numbers in `[1, n - 1]`. -/
def p256SignatureWellFormed (sig : List UInt8) : Bool :=
  let r := beNat (sig.take 32)
  let s := beNat (sig.drop 32)
  0 < r && r < p256Order && 0 < s && s < p256Order

/-- `ed25519_verify(sig_len, sig_ptr, msg_len, msg_ptr, pk_len, pk_ptr)`. A signature whose top
three bits are set is rejected before the message is read, so the message bytes are not paid. -/
def ed25519Eval (st : HostStore NearState) (args : List Value) : CryptoEval :=
  let a := argU64 args
  cryptoRead st (a 0) (a 1) [ext1 "ed25519_verify_base"] fun sig acc =>
    if sig.length != 64 then cryptoStop acc (.ed25519VerifyInvalidInput "invalid signature length")
    else
      if (sig.getD 63 0) &&& 0xE0 != 0 then
        { charges := acc, compute := fun _ => .done [.i64 0] none }
      else
        cryptoRead st (a 2) (a 3) acc fun message acc =>
          cryptoRead st (a 4) (a 5) (acc ++ [ext1 "ed25519_verify_byte" message.length])
            fun key acc =>
            if key.length != 32 then
              cryptoStop acc (.ed25519VerifyInvalidInput "invalid public key length")
            else
              { charges := acc
                compute := fun _ =>
                  withCrypto st "ed25519_verify" fun crypto =>
                    .done [.i64 (if crypto.ed25519Verify sig message key then 1 else 0)] none }

/-- `p256_verify`: as `ed25519_verify`, a signature that does not parse ends the call with `0`
before the message is read. -/
def p256Eval (st : HostStore NearState) (args : List Value) : CryptoEval :=
  let a := argU64 args
  cryptoRead st (a 0) (a 1) [ext1 "p256_verify_base"] fun sig acc =>
    if sig.length != 64 then cryptoStop acc (.p256VerifyInvalidInput "invalid signature length")
    else
      if !p256SignatureWellFormed sig then
        { charges := acc, compute := fun _ => .done [.i64 0] none }
      else
        cryptoRead st (a 2) (a 3) acc fun message acc =>
          cryptoRead st (a 4) (a 5) (acc ++ [ext1 "p256_verify_byte" message.length]) fun key acc =>
            if key.length != 33 then
              cryptoStop acc (.p256VerifyInvalidInput "invalid public key length")
            else
              { charges := acc
                compute := fun _ =>
                  withCrypto st "p256_verify" fun crypto =>
                    .done [.i64 (if crypto.p256Verify sig message key then 1 else 0)] none }

/-- The error of `stdx::as_chunks_exact` when the input is not a multiple of the element size. -/
def inexactChunking (length size : Nat) : HostError :=
  .altBn128InvalidInput
    s!"slice of size {length} cannot be precisely split into chunks of size {size}"

/-- `alt_bn128_g1_multiexp` and `alt_bn128_g1_sum`: the input is split into elements, the elements
are paid for, then the primitive decodes and computes; its result goes to the register. -/
def altBn128RegisterEval (name : String) (size : Nat) (st : HostStore NearState) (args : List Value)
    (op : HostCrypto → List UInt8 → Except String (List UInt8)) : CryptoEval :=
  let a := argU64 args
  cryptoRead st (a 0) (a 1) [ext1 (name ++ "_base")] fun data acc =>
    if data.length % size != 0 then cryptoStop acc (inexactChunking data.length size)
    else
      { charges := acc ++ [ext1 (name ++ "_element") (data.length / size)]
        compute := fun _ =>
          withCrypto st name fun crypto =>
            match op crypto data with
            | .ok out => .done [] (some (a 2, out))
            | .error message => .trap (.altBn128InvalidInput message) }

/-- `alt_bn128_pairing_check(value_len, value_ptr)`. -/
def altBn128PairingEval (st : HostStore NearState) (args : List Value) : CryptoEval :=
  let a := argU64 args
  cryptoRead st (a 0) (a 1) [ext1 "alt_bn128_pairing_check_base"] fun data acc =>
    if data.length % 192 != 0 then cryptoStop acc (inexactChunking data.length 192)
    else
      { charges := acc ++ [ext1 "alt_bn128_pairing_check_element" (data.length / 192)]
        compute := fun _ =>
          withCrypto st "alt_bn128_pairing_check" fun crypto =>
            match crypto.altBn128PairingCheck data with
            | .ok holds => .done [.i64 (if holds then 1 else 0)] none
            | .error message => .trap (.altBn128InvalidInput message) }

/-- The `bls12381_*` functions that write a register: the elements are paid for from the length
argument before the input is read, `fnName` is the name in the length error. The primitive returns
`none` (status `1`) for an invalid point. -/
def blsRegisterEval (name fnName : String) (size : Nat) (st : HostStore NearState)
    (args : List Value) (op : HostCrypto → Nat → List UInt8 → Except String (Option (List UInt8))) :
    CryptoEval :=
  let a := argU64 args
  let head := [ext1 (name ++ "_base")]
  if payPerOverflows st (name ++ "_element") ((a 0).toNat / size) then
    cryptoStop head .integerOverflow
  else
    let paid := head ++ [ext1 (name ++ "_element") ((a 0).toNat / size)]
    cryptoRead st (a 0) (a 1) paid fun data acc =>
      if data.length % size != 0 then
        cryptoStop acc
          (.bls12381InvalidInput
            s!"Incorrect input length for {fnName}: {data.length} is not divisible by {size}")
      else
        { charges := acc
          compute := fun _ =>
            withCrypto st name fun crypto =>
              match op crypto st.host.config.blsVersion data with
              | .ok (some out) => .done [.i64 0] (some (a 2, out))
              | .ok none => .done [.i64 1] none
              | .error message => .trap (.bls12381InvalidInput message) }

/-- `bls12381_pairing_check`: the elements are counted on the bytes read. -/
def blsPairingEval (st : HostStore NearState) (args : List Value) : CryptoEval :=
  let a := argU64 args
  cryptoRead st (a 0) (a 1) [ext1 "bls12381_pairing_base"] fun data acc =>
    let acc := acc ++ [ext1 "bls12381_pairing_element" (data.length / 288)]
    if data.length % 288 != 0 then
      cryptoStop acc
        (.bls12381InvalidInput
          s!"Incorrect input length for bls12381_pairing_check: {data.length} is not divisible by 288")
    else
      { charges := acc
        compute := fun _ =>
          withCrypto st "bls12381_pairing_check" fun crypto =>
            match crypto.bls12381PairingCheck data with
            | .ok status => .done [.i64 (UInt64.ofNat status)] none
            | .error message => .trap (.bls12381InvalidInput message) }

/-- The cryptographic host functions. -/
def cryptoHostNames : List String :=
  ["sha256", "keccak256", "keccak512", "ripemd160", "ecrecover", "ed25519_verify", "p256_verify",
    "alt_bn128_g1_multiexp", "alt_bn128_g1_sum", "alt_bn128_pairing_check", "bls12381_p1_sum",
    "bls12381_p2_sum", "bls12381_g1_multiexp", "bls12381_g2_multiexp", "bls12381_map_fp_to_g1",
    "bls12381_map_fp2_to_g2", "bls12381_p1_decompress", "bls12381_p2_decompress",
    "bls12381_pairing_check"]

/-- One call of the cryptographic host function `name`; `none` for any other name. -/
def cryptoEval (name : String) (st : HostStore NearState) (args : List Value) : Option CryptoEval :=
  match name with
  | "sha256" => some (digestEval name st args (fun n => [ext1 "sha256_byte" n]) (·.sha256))
  | "keccak256" => some (digestEval name st args (fun n => [ext1 "keccak256_byte" n]) (·.keccak256))
  | "keccak512" => some (digestEval name st args (fun n => [ext1 "keccak512_byte" n]) (·.keccak512))
  | "ripemd160" =>
    some
      (digestEval name st args (fun n => [ext1 "ripemd160_block" ((n + 8) / 64 + 1)]) (·.ripemd160))
  | "ecrecover" => some (ecrecoverEval st args)
  | "ed25519_verify" => some (ed25519Eval st args)
  | "p256_verify" => some (p256Eval st args)
  | "alt_bn128_g1_multiexp" => some (altBn128RegisterEval name 96 st args (·.altBn128G1Multiexp))
  | "alt_bn128_g1_sum" => some (altBn128RegisterEval name 65 st args (·.altBn128G1Sum))
  | "alt_bn128_pairing_check" => some (altBn128PairingEval st args)
  | "bls12381_p1_sum" => some (blsRegisterEval name name 97 st args (·.bls12381P1Sum))
  | "bls12381_p2_sum" => some (blsRegisterEval name name 193 st args (·.bls12381P2Sum))
  | "bls12381_g1_multiexp" =>
    some (blsRegisterEval name "bls12381_p1_multiexp" 128 st args (·.bls12381G1Multiexp))
  | "bls12381_g2_multiexp" =>
    some (blsRegisterEval name "bls12381_p2_multiexp" 224 st args (·.bls12381G2Multiexp))
  | "bls12381_map_fp_to_g1" => some (blsRegisterEval name name 48 st args (·.bls12381MapFpToG1))
  | "bls12381_map_fp2_to_g2" => some (blsRegisterEval name name 96 st args (·.bls12381MapFp2ToG2))
  | "bls12381_p1_decompress" => some (blsRegisterEval name name 48 st args (·.bls12381P1Decompress))
  | "bls12381_p2_decompress" => some (blsRegisterEval name name 96 st args (·.bls12381P2Decompress))
  | "bls12381_pairing_check" => some (blsPairingEval st args)
  | _ => none

end Wasm.Near
