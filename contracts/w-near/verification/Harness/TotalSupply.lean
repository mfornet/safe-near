import Harness.Builtins

/-!
# Contracts on `ft_total_supply`'s path (milestone M3)

The functions `ft_total_supply` (296) calls directly, stated and stressed
before any proof:

| Index | Rust name | Contract |
|---|---|---|
| 779 | `<Vec<T> as Deref>::deref` | `vecDeref` |
| 155 | `Option<Contract>::unwrap_or_default` (the default panics) | `stateOrPanic` |

Costs are counted from the bodies, as in `Harness/Builtins.lean`.
-/

namespace WNear.Testing

open Wasm Wasm.Near

/-! ## `Vec::deref` (779)

`deref(out, vec)`: the slice `(ptr, len)` of the `Vec` `(ptr, cap, len)` at
`vec`, written to the 8 bytes at `out`. The length is written before the
pointer is read, so the length's slot must not overlap the pointer word
(overlapping the capacity or the length is harmless: misstatement log, 3). -/

def vecDeref : Contract Unit where
  name := "Vec::deref"
  func := 779
  pre h i :=
    let (out, vec) := (u32Arg i.args 0, u32Arg i.args 1)
    if out + 8 > h.memSize i.store || vec + 12 > h.memSize i.store then some "beyond memory"
    else if overlap (out + 4) 4 vec 4 then some "the length's slot overlaps the pointer"
    else none
  footprint _ i := [(u32Arg i.args 0, 8)]
  post h i r :=
    let (out, vec) := (u32Arg i.args 0, u32Arg i.args 1)
    (ended r).or <|
    if h.readNat r.after out 4 != h.readNat r.before vec 4 then some "pointer is wrong"
    else if h.readNat r.after (out + 4) 4 != h.readNat r.before (vec + 8) 4 then some "length is wrong"
    else none
  -- Activation 9 (two i32 parameters); 8 instructions.
  cost h _ := op h 17
  ghostOf _ _ := some ()

/-! ## The state, or the not-initialized panic (155)

`unwrap_or_default(out, opt)` on the `Option<Contract>` that `state_read`
leaves at `opt`: when its tag word (offset 24) is zero the contract is not
initialized, and `Contract::default` panics with that message; otherwise
the 40 bytes at `opt` are copied to `out`.

The ghost says the environment is set up (`set_blockchain_interface` ran,
as every method does first): `env::panic` reaches the host through it, and
without it Rust's `unwrap` on `None` traps instead (misstatement log, 4). -/

/-- The panic `Contract::default` raises (31 bytes at 1050868). -/
def notInitialized : String := "The contract is not initialized"

def stateOrPanic : Contract Bool where
  name := "state_read().unwrap_or_default()"
  func := 155
  pre h i :=
    let (out, opt) := (u32Arg i.args 0, u32Arg i.args 1)
    if !i.ghost then some "the environment is not set up"
    else if out + 40 > h.memSize i.store || opt + 40 > h.memSize i.store then some "beyond memory"
    else if overlap out 40 opt 40 then some "out overlaps the option"
    else none
  footprint _ i := [(u32Arg i.args 0, 40)]
  stack := 64
  post h i r :=
    let (out, opt) := (u32Arg i.args 0, u32Arg i.args 1)
    if h.readNat r.before (opt + 24) 4 == 0 then
      match r.ending with
      | .trapped (.hostError (.guestPanic msg)) =>
        if msg == notInitialized then none else some s!"panics with {msg}"
      | e => some s!"none: {e.describe}"
    else
      (ended r).or <|
      if h.read r.after out 40 != h.read r.before opt 40 then some "state not copied" else none
  -- Activation 9; the test 3; the call 4, `memcpy` of 40 bytes 16 + 18 * 40; `drop` 1.
  -- The panic path aborts the call: no claim on its gas.
  cost h i :=
    if h.readNat i.store (u32Arg i.args 1 + 24) 4 == 0 then 10 ^ 18 else op h (17 + 16 + 18 * 40)
  -- Call sites run inside a method, after its setup.
  ghostOf _ _ := some true

/-! ## `U128::from` (566) and `FungibleToken::ft_total_supply` (414) -/

/-- `from(out, lo, hi)`: the `u128` `lo + 2^64 hi` in the 16 bytes at `out`. -/
def u128From : Contract Unit where
  name := "U128::from"
  func := 566
  pre h i := if u32Arg i.args 0 + 16 > h.memSize i.store then some "beyond memory" else none
  footprint _ i := [(u32Arg i.args 0, 16)]
  post h i r :=
    (ended r).or <|
    if h.readNat r.after (u32Arg i.args 0) 16 != u64Arg i.args 1 + 2 ^ 64 * u64Arg i.args 2 then
      some "wrong value" else none
  -- Activation 11 (an i32 and two i64 parameters); 6 instructions.
  cost h _ := op h 17
  ghostOf _ _ := some ()

/-- `ft_total_supply(out, ft)`: the `u128` total supply, the first field of
the `FungibleToken` at `ft`, in the 16 bytes at `out`. -/
def ftTotalSupply : Contract Unit where
  name := "FungibleToken::ft_total_supply"
  func := 414
  pre h i :=
    let (out, ft) := (u32Arg i.args 0, u32Arg i.args 1)
    if out + 16 > h.memSize i.store || ft + 16 > h.memSize i.store then some "beyond memory" else none
  footprint _ i := [(u32Arg i.args 0, 16)]
  stack := 16
  post h i r :=
    (ended r).or <|
    if h.readNat r.after (u32Arg i.args 0) 16 != h.readNat r.before (u32Arg i.args 1) 16 then
      some "wrong total supply" else none
  -- Activation 11; the frame 5 and its release 4; the two loads 7; the call 1
  -- and `U128::from` 17; the copy 3 + 6 + 3.
  cost h _ := op h 57
  ghostOf _ _ := some ()

/-! ## `Result::expect` (158)

`expect(out, res, loc)` on a `Result` whose tag is the word at `res`: `Ok`
(tag not 1) copies the 12 payload bytes at `res + 4` to `out`; `Err` panics
through `unwrap_failed`, which formats the error value. The contract is for
`Ok` only: on `ft_total_supply`'s path `expect` follows `to_vec` of a
`U128`, which never fails, and an `Err` needs the error's representation
(misstatement log, 5). The ghost is the environment, as for `stateOrPanic`. -/

def resultExpect : Contract Bool where
  name := "Result::expect"
  func := 158
  pre h i :=
    let (out, res) := (u32Arg i.args 0, u32Arg i.args 1)
    if !i.ghost then some "the environment is not set up"
    else if out + 12 > h.memSize i.store || res + 16 > h.memSize i.store then some "beyond memory"
    else if h.readNat i.store res 4 == 1 then some "an Err"
    else if overlap out 8 (res + 12) 4 then some "out overlaps the payload's last word"
    else none
  footprint _ i := [(u32Arg i.args 0, 12)]
  stack := 64
  post h i r :=
    let (out, res) := (u32Arg i.args 0, u32Arg i.args 1)
    if h.readNat r.before res 4 == 1 then
      match r.ending with
      | .trapped (.hostError (.guestPanic _)) => none
      | e => some s!"Err: {e.describe}"
    else
      (ended r).or <|
      if h.read r.after out 12 != h.read r.before (res + 4) 12 then some "payload not copied" else none
  -- Ok: activation 10; the frame 5 and its release 4; the tag test 5; the copy 4 + 8.
  cost h i := if h.readNat i.store (u32Arg i.args 1) 4 == 1 then 10 ^ 18 else op h 36
  ghostOf _ _ := some true

/-! ## `env::state_read` (219)

`state_read(out)`: the `Option<Contract>` decoded from the storage value at
key `"STATE"`, in the 40 bytes at `out`. The layout, from 155 and 414:
`total_supply : u128` at 0, `account_storage_usage : u64` at 16, and the
`LookupMap` prefix as a `Vec<u8>` `(ptr, cap, len)` at 24, whose pointer
word is `Option`'s niche: zero for `None`. The Borsh encoding is the
prefix (`u32` length, bytes), the supply, the usage. -/

def stateKey : List UInt8 := "STATE".toUTF8.toList

/-- The Borsh decoding of the state: prefix, supply, usage. -/
def decodeState (bs : List UInt8) : Option (List UInt8 × Nat × Nat) :=
  let le (xs : List UInt8) := xs.foldr (fun b acc => acc * 256 + b.toNat) 0
  if bs.length < 4 then none else
  let n := le (bs.take 4)
  let rest := bs.drop 4
  if rest.length != n + 24 then none else
  some (rest.take n, le ((rest.drop n).take 16), le ((rest.drop (n + 16)).take 8))

def stateRead : Contract Bool where
  name := "env::state_read"
  func := 219
  pre h i :=
    if !i.ghost then some "the environment is not set up"
    else if u32Arg i.args 0 + 40 > h.memSize i.store then some "beyond memory"
    else match i.store.host.storage stateKey with
      | some bs => if (decodeState bs).isNone then some "the state does not decode" else none
      | none => none
  -- The heap (the decoded prefix and the value read), and the result.
  footprint _ i := [(u32Arg i.args 0, 40), (heapBase, 2 ^ 32 - heapBase), (freeListHead, 4)]
  stack := 1024
  grows := true
  post h i r :=
    let out := u32Arg i.args 0
    (ended r).or <|
    match i.store.host.storage stateKey with
    | none => if h.readNat r.after (out + 24) 4 != 0 then some "absent state is not None" else none
    | some bs =>
      match decodeState bs with
      | none => some "precondition"
      | some (pre, supply, usage) =>
        let ptr := h.readNat r.after (out + 24) 4
        if ptr == 0 then some "present state is None"
        else if h.readNat r.after out 16 != supply then some "wrong total supply"
        else if h.readNat r.after (out + 16) 8 != usage then some "wrong storage usage"
        else if h.readNat r.after (out + 32) 4 != pre.length then some "wrong prefix length"
        else if h.read r.after ptr pre.length != pre then some "wrong prefix"
        else none
  -- No claim yet: the storage host costs are stated with M7.
  cost _ _ := 10 ^ 18
  ghostOf _ _ := some true

end WNear.Testing
