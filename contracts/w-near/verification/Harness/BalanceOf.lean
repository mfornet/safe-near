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

end WNear.Testing
