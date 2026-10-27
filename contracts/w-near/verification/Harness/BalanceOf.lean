import Harness.TotalSupply

/-!
# Contracts on `ft_balance_of`'s path

`ft_balance_of` (297) calls, beyond `ft_total_supply`'s callees:
`env::input` (527), `Option::expect` (157), `serde_json::from_slice` (65),
the `FungibleToken` lookup (293), `env::value_return` (545) and the drop of
a `Vec<u8>` (68). Contracts stated and stressed here:

| Index | Rust name | Contract |
|---|---|---|
| 545 | `env::value_return` | `valueReturn` |
| 527 | `env::input` | `envInput` |
| 157 | `Option<Vec<u8>>::expect` | `optionExpect` |

The ghost of each is the environment, as on `ft_total_supply`'s path.
-/

namespace WNear.Testing

open Wasm Wasm.Near

/-- `value_return(ptr, len)`: the `len` bytes at `ptr` become the call's
return data. -/
def valueReturn : Contract Bool where
  name := "env::value_return"
  func := 545
  pre h i :=
    let (ptr, len) := (u32Arg i.args 0, u32Arg i.args 1)
    if !i.ghost then some "the environment is not set up"
    else if ptr + len > h.memSize i.store then some "beyond memory"
    else if len > 4 * 1024 * 1024 then some "beyond the return limit"
    else none
  footprint _ _ := []
  stack := 64
  hostEffects := true
  post h i r :=
    let (ptr, len) := (u32Arg i.args 0, u32Arg i.args 1)
    (ended r).or <|
    if r.after.host.returnData != some (h.read r.before ptr len) then some "wrong return data"
    else if r.after.host.logs != r.before.host.logs then some "logged"
    else none
  -- No claim yet: host costs are stated with the host contracts (M7).
  cost _ _ := 10 ^ 18
  ghostOf _ _ := some true

/-- `input(out)`: a `Vec<u8>` `(ptr, cap, len)` at `out` holding the call's
input. -/
def envInput : Contract Bool where
  name := "env::input"
  func := 527
  pre h i :=
    if !i.ghost then some "the environment is not set up"
    else if u32Arg i.args 0 + 12 > h.memSize i.store then some "beyond memory"
    else none
  footprint _ i := [(u32Arg i.args 0, 12), (heapBase, 2 ^ 32 - heapBase), (freeListHead, 4)]
  stack := 256
  grows := true
  hostEffects := true
  post h i r :=
    let out := u32Arg i.args 0
    (ended r).or <|
    let input := r.before.host.context.input
    let ptr := h.readNat r.after out 4
    let len := h.readNat r.after (out + 8) 4
    if len != input.length then some s!"length {len}, input {input.length}"
    else if h.read r.after ptr len != input then some "wrong bytes"
    else if r.after.host.returnData != r.before.host.returnData then some "return data changed"
    else none
  cost _ _ := 10 ^ 18
  ghostOf _ _ := some true

/-- `expect(out, opt, loc)` on an `Option<Vec<u8>>` whose niche is the
pointer word at `opt`: `Some` copies the 12 bytes to `out`; `None` panics
with a 42-byte message. -/
def optionExpect : Contract Bool where
  name := "Option<Vec<u8>>::expect"
  func := 157
  pre h i :=
    let (out, opt) := (u32Arg i.args 0, u32Arg i.args 1)
    if !i.ghost then some "the environment is not set up"
    else if out + 12 > h.memSize i.store || opt + 12 > h.memSize i.store then some "beyond memory"
    else if overlap out 8 (opt + 8) 4 then some "out overlaps the length"
    else none
  footprint _ i := [(u32Arg i.args 0, 12)]
  stack := 256
  post h i r :=
    let (out, opt) := (u32Arg i.args 0, u32Arg i.args 1)
    if h.readNat r.before opt 4 == 0 then
      match r.ending with
      | .trapped (.hostError (.guestPanic _)) => none
      | e => some s!"None: {e.describe}"
    else
      (ended r).or <|
      if h.read r.after out 12 != h.read r.before opt 12 then some "not copied" else none
  -- Some: activation 10 (three i32 parameters, 12 bytes); the test 3; the copy 4 + 8.
  cost h i := if h.readNat i.store (u32Arg i.args 1) 4 == 0 then 10 ^ 18 else op h 25
  ghostOf _ _ := some true

/-! ## `Contract::ft_balance_of` (293)

`ft_balance_of(out, contract, account)`: the `u128` balance of the
`AccountId` (a `String` `(ptr, cap, len)` at `account`, taken by value and
dropped) in the 16 bytes at `out`. The balance is the storage value at
the `LookupMap` key, the prefix (the `Vec` at `contract + 24`) followed by
the Borsh `String`; absent, it is zero. -/

def leNat (bs : List UInt8) : Nat := bs.foldr (fun b acc => acc * 256 + b.toNat) 0

/-- The storage key of the account at `account`, under the contract at `contract`. -/
def balanceKey (h : Harness) (s : Store NearState) (contract account : Nat) : List UInt8 :=
  let pre := h.read s (h.readNat s (contract + 24) 4) (h.readNat s (contract + 32) 4)
  let len := h.readNat s (account + 8) 4
  pre ++ (List.range 4).map (fun i => UInt8.ofNat (len / 256 ^ i)) ++ h.read s (h.readNat s account 4) len

def balanceOf : Contract Bool where
  name := "Contract::ft_balance_of"
  func := 293
  pre h i :=
    let (out, contract, account) := (u32Arg i.args 0, u32Arg i.args 1, u32Arg i.args 2)
    if !i.ghost then some "the environment is not set up"
    else if out + 16 > h.memSize i.store || contract + 40 > h.memSize i.store ||
        account + 12 > h.memSize i.store then some "beyond memory"
    else match i.store.host.storage (balanceKey h i.store contract account) with
      | some v => if v.length != 16 then some "the balance does not decode" else none
      | none => none
  footprint _ i := [(u32Arg i.args 0, 16), (heapBase, 2 ^ 32 - heapBase), (freeListHead, 4)]
  stack := 1024
  grows := true
  post h i r :=
    let (out, contract, account) := (u32Arg i.args 0, u32Arg i.args 1, u32Arg i.args 2)
    (ended r).or <|
    let expected := match i.store.host.storage (balanceKey h i.store contract account) with
      | some v => leNat v
      | none => 0
    if h.readNat r.after out 16 != expected then
      some s!"balance {h.readNat r.after out 16}, expected {expected}" else none
  -- No claim yet: the storage host costs are stated with M7.
  cost _ _ := 10 ^ 18
  ghostOf _ _ := some true

end WNear.Testing
