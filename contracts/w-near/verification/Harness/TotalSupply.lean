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

end WNear.Testing
