import Harness.TotalSupply
import Model.Args
import Model.State
import Model.Contract

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

/-- The four little-endian bytes of `n`. -/
def leBytes32 (n : Nat) : List UInt8 := (List.range 4).map fun i => UInt8.ofNat (n / 256 ^ i)

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

/-! ## `serde_json::from_slice` of `ft_balance_of`'s arguments (65)

`from_slice(out, ptr, len)`: the `Result` of parsing the `len` bytes at
`ptr` as `{"account_id": AccountId}`, in the 16 bytes at `out`: `Err` (tag
word 1), or `Ok` with the account id `String` `(ptr, cap, len)` at
`out + 4`. It accepts exactly the inputs the model's `Call.decode` does,
with the same account: the binary's side of `Parses` for this method. -/

def fromSliceBalanceOf : Contract Bool where
  name := "serde_json::from_slice::<ft_balance_of args>"
  func := 65
  pre h i :=
    let (out, ptr, len) := (u32Arg i.args 0, u32Arg i.args 1, u32Arg i.args 2)
    if !i.ghost then some "the environment is not set up"
    else if out + 16 > h.memSize i.store || ptr + len > h.memSize i.store then some "beyond memory"
    else none
  footprint _ i := [(u32Arg i.args 0, 16), (heapBase, 2 ^ 32 - heapBase), (freeListHead, 4)]
  stack := 4096
  grows := true
  post h i r :=
    let (out, ptr, len) := (u32Arg i.args 0, u32Arg i.args 1, u32Arg i.args 2)
    (ended r).or <|
    let ok := h.readNat r.after out 4 != 1
    match WNear.Call.decode "ft_balance_of" (h.read r.before ptr len) with
    | some (.ftBalanceOf a) =>
      if !ok then some s!"rejects what the model parses as {a.val}"
      else
        let bs := h.read r.after (h.readNat r.after (out + 4) 4) (h.readNat r.after (out + 12) 4)
        if bs != a.val.toUTF8.toList then some s!"parses another account than {a.val}" else none
    | _ => if ok then some "accepts what the model rejects" else none
  -- No claim yet: the gas per argument byte is stated with M6.
  cost _ _ := 10 ^ 18
  ghostOf _ _ := some true

/-! ## `Contract::storage_minimum_balance` (230)

`storage_minimum_balance(out, contract)`: the `u128` minimum, the
`account_storage_usage` (the `u64` at `contract + 16`) times the storage
price per byte, through `storage_balance_bounds` (418), whose checked
multiplication never overflows here (`u64` times `10^19`). The model's
`State.storageMin`. -/

def storageMinimum : Contract Bool where
  name := "Contract::storage_minimum_balance"
  func := 230
  pre h i :=
    let (out, contract) := (u32Arg i.args 0, u32Arg i.args 1)
    if !i.ghost then some "the environment is not set up"
    else if out + 16 > h.memSize i.store || contract + 40 > h.memSize i.store then some "beyond memory"
    else none
  footprint _ i := [(u32Arg i.args 0, 16)]
  stack := 1024
  post h i r :=
    let (out, contract) := (u32Arg i.args 0, u32Arg i.args 1)
    (ended r).or <|
    let expected := h.readNat r.before (contract + 16) 8 * WNear.storagePricePerByte
    if h.readNat r.after out 16 != expected then
      some s!"minimum {h.readNat r.after out 16}, expected {expected}" else none
  -- No claim yet: `storage_byte_cost` goes through the environment.
  cost _ _ := 10 ^ 18
  ghostOf _ _ := some true

/-! ## `Contract::ft_metadata` (308), through its serializer (102)

`ft_metadata(out, contract)`: the `FungibleTokenMetadata` at `out`. Its
in-memory layout is checked through the method's own serializer: a
`Vec::with_capacity(128)` (94) at 8000, a serializer pointing at it at
8100, then `serialize` (102), which returns 0 and leaves in the `Vec`
exactly the model's JSON of `metadata`. -/

def ftMetadata : Contract Bool where
  name := "Contract::ft_metadata, serialized"
  func := 308
  pre h i :=
    let (out, contract) := (u32Arg i.args 0, u32Arg i.args 1)
    if !i.ghost then some "the environment is not set up"
    else if out + 128 > h.memSize i.store || contract + 40 > h.memSize i.store then some "beyond memory"
    else none
  footprint _ i := [(u32Arg i.args 0, 128), (heapBase, 2 ^ 32 - heapBase), (freeListHead, 4)]
  stack := 1024
  grows := true
  post h i r :=
    (ended r).or <|
    let v := h.call r.after 94 [i32 8000, i32 128]
    match ended v, h.write v.after 8100 (leBytes32 8000) with
    | some e, _ => some s!"with_capacity: {e}"
    | _, .error e => some e
    | none, .ok s =>
      let ser := h.call s 102 [i32 (u32Arg i.args 0), i32 8100]
      match ended ser, returnsU32 ser with
      | some e, _ => some s!"serialize: {e}"
      | none, some 0 =>
        let json := h.read ser.after (h.readNat ser.after 8000 4) (h.readNat ser.after 8008 4)
        let expected := (WNear.Ret.metadata WNear.metadata).json.toUTF8.toList
        if json != expected then some s!"serializes to {String.fromUTF8! ⟨json.toArray⟩}" else none
      | none, _ => some "serialize failed"
  cost _ _ := 10 ^ 18
  ghostOf _ _ := some true

/-! ## `FungibleToken::storage_balance_bounds` (418), through its serializer (108)

`storage_balance_bounds(out, ft)`: the bounds `{min, max}` at `out`,
checked as `ft_metadata` is: serialized by `StorageBalanceBounds::serialize`
(108) into a fresh `Vec`, they are the model's JSON of
`storageBalanceBounds`, both bounds the usage at `ft + 16` times the price
per byte. -/

def storageBounds : Contract Bool where
  name := "FungibleToken::storage_balance_bounds, serialized"
  func := 418
  pre h i :=
    let (out, ft) := (u32Arg i.args 0, u32Arg i.args 1)
    if !i.ghost then some "the environment is not set up"
    else if out + 64 > h.memSize i.store || ft + 40 > h.memSize i.store then some "beyond memory"
    else none
  footprint _ i := [(u32Arg i.args 0, 64)]
  stack := 1024
  post h i r :=
    (ended r).or <|
    let v := h.call r.after 94 [i32 8000, i32 128]
    match ended v, h.write v.after 8100 (leBytes32 8000) with
    | some e, _ => some s!"with_capacity: {e}"
    | _, .error e => some e
    | none, .ok s =>
      let ser := h.call s 108 [i32 (u32Arg i.args 0), i32 8100]
      match ended ser, returnsU32 ser with
      | some e, _ => some s!"serialize: {e}"
      | none, some 0 =>
        let json := h.read ser.after (h.readNat ser.after 8000 4) (h.readNat ser.after 8008 4)
        let m := h.readNat r.before (u32Arg i.args 1 + 16) 8 * WNear.storagePricePerByte
        let expected := (WNear.Ret.storageBalanceBounds { min := m, max := some m }).json.toUTF8.toList
        if json != expected then some s!"serializes to {String.fromUTF8! ⟨json.toArray⟩}" else none
      | none, _ => some "serialize failed"
  cost _ _ := 10 ^ 18
  ghostOf _ _ := some true

end WNear.Testing
