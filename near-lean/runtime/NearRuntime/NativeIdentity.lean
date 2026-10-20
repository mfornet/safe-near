import NearRuntime.Sha256

/-! Native receipt/action/data identities at the pinned protocol boundary.
Model Nat IDs still name objects; these functions derive their native hash
identities from explicit ancestry rather than hashing the counter or receipt. -/
namespace Near.NativeIdentity
abbrev Hash := List UInt8

private def u64 (value : Nat) : Except String Hash := do
  unless value < 2 ^ 64 do throw "identity integer exceeds u64"
  return (List.range 8).map fun i => UInt8.ofNat (value / 2 ^ (8 * i) % 256)

def checkedHash (hash : Hash) : Except String Hash :=
  if hash.length == 32 then pure hash else throw "invalid identity hash width"

private def indexed (base : Hash) (height salt : Nat) : Except String Hash := do
  return Sha256.hash ((← checkedHash base) ++ (← u64 height) ++ (← u64 salt))

def transactionReceipt (transaction : Hash) (height : Nat) : Except String Hash :=
  indexed transaction height 0

def receipt (parent : Hash) (height index : Nat) : Except String Hash :=
  indexed parent height index

def action (parent : Hash) (height index : Nat) : Except String Hash := do
  let _ ← u64 index
  indexed parent height (2 ^ 64 - 1 - index)

def data (actionHash : Hash) (height index : Nat) : Except String Hash :=
  indexed actionHash height index

theorem transactionReceipt_eq (base : Hash) (height : Nat) :
    transactionReceipt base height = receipt base height 0 := rfl

theorem data_eq (base : Hash) (height index : Nat) :
    data base height index = receipt base height index := rfl

/-- Runtime VM randomness is derived separately from the action and block seed. -/
def randomSeed (actionHash seed : Hash) : Except String Hash := do
  return Sha256.hash ((← checkedHash actionHash) ++ (← checkedHash seed))

abbrev Bindings := List (Nat × Hash)

/-- IDs are explicit logical names; no fallback hash is supplied for an unknown ID. -/
def resolve (bindings : Bindings) (id : Nat) : Except String Hash := do
  let some (_, hash) := bindings.find? (·.1 == id) | throw "native identity is unavailable"
  checkedHash hash

def validate (bindings : Bindings) : Except String Unit := do
  let ids := bindings.map Prod.fst
  let hashes := bindings.map Prod.snd
  unless ids.eraseDups.length == ids.length do throw "duplicate model identity"
  unless hashes.eraseDups.length == hashes.length do throw "aliased native identity"
  for (_, hash) in bindings do let _ ← checkedHash hash

end Near.NativeIdentity
