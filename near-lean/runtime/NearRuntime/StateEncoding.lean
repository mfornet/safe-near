import NearRuntime.State
import NearRuntime.Sha256
import NearVM.AccountId

/-! Queue-free selected-account state at the pinned native Borsh boundary.
This constructs a synthetic genesis, not an original shard state. Receipt/data
IDs are model counters rather than native hashes, so nonempty queues fail closed.
The external Wasm decoder remains responsible for bytes-to-module correspondence. -/
namespace Near.StateEncoding

private def little (width value : Nat) : Bytes :=
  (List.range width).map fun i => UInt8.ofNat (value / 2 ^ (8 * i) % 256)

private def unsigned (width value : Nat) : Except String Bytes :=
  if value < 2 ^ (8 * width) then pure (little width value)
  else throw s!"integer exceeds u{8 * width}"

private def vector (bytes : Bytes) : Except String Bytes := do
  return (← unsigned 4 bytes.length) ++ bytes

private def string (text : String) : Except String Bytes := vector text.toUTF8.toList

private def digits : Nat → Nat → List Char
  | 0, _ => []
  | fuel + 1, value =>
    if value == 0 then [] else
      "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz".toList[value % 58]! ::
        digits fuel (value / 58)

/-- Canonical base58 for binding native code hash names to actual Wasm bytes. -/
def base58 (bytes : Bytes) : String :=
  let value := bytes.foldl (fun n b => n * 256 + b.toNat) 0
  String.ofList (List.replicate (bytes.takeWhile (· == 0)).length '1' ++
    (digits (bytes.length * 2 + 1) value).reverse)

private def accountId (id : AccountId) : Except String Bytes := do
  let bytes := id.toUTF8.toList
  unless Wasm.Near.validAccountIdBytes bytes do throw "invalid account id"
  return bytes

/-- Ordinary Ed25519/secp256k1 public keys already carry their native Borsh tag.
Gas-key handles and other key families are outside the represented runtime. -/
def publicKey (key : PublicKey) : Except String Bytes :=
  if (key.head? == some 0 && key.length == 33) ||
      (key.head? == some 1 && key.length == 65) then pure key
  else throw "unsupported public key encoding"

def accessKey (key : AccessKey) : Except String Bytes := do
  let nonce ← unsigned 8 key.nonce
  match key.permission with
  | .fullAccess => return nonce ++ [1]
  | .functionCall allowance receiver methods =>
    let allowance ← match allowance with
      | none => pure [0]
      | some amount => (fun encoded => [1] ++ encoded) <$> unsigned 16 amount
    let count ← unsigned 4 methods.length
    let names ← methods.mapM string
    -- Native FunctionCallPermission.receiver_id is String, not AccountId.
    return nonce ++ [0] ++ allowance ++ (← string receiver) ++ count ++ names.flatten

private def unique [BEq α] (name : String) (values : List α) : Except String Unit := do
  unless values.eraseDups.length == values.length do throw s!"duplicate {name}"

/-- Encode actual runtime records. Code payloads must be present, size-matched,
and SHA256-bound to the model's canonical hash name. No native output is input.
`nextId` is manipulator metadata and has no native trie column. -/
def encode (state : ChainState) (codes : List (String × Bytes)) : Except String (List (Bytes × Bytes)) := do
  unless state.postponed.isEmpty && state.pendingDataCount.isEmpty && state.postponedByData.isEmpty &&
      state.receivedData.isEmpty && state.delayed.isEmpty do
    throw "native receipt/data identity encoding is unavailable"
  unique "account" (state.accounts.map Prod.fst)
  unique "access key" (state.accessKeys.map Prod.fst)
  unique "storage account" (state.storage.map Prod.fst)
  unique "catalogue hash" (codes.map Prod.fst)
  for (name, bytes) in codes do
    unless base58 (Sha256.hash bytes) == name do throw "code hash does not bind catalogue bytes"
  let mut entries := []
  for (id, account) in state.accounts do
    let id ← accountId id
    let code ← account.code.mapM fun code => do
      let some bytes := Assoc.lookup codes code.hash | throw "code bytes absent from catalogue"
      unless bytes.length == code.size do throw "code size disagrees with catalogue bytes"
      return bytes
    let hash := code.elim (List.replicate 32 0) Sha256.hash
    let value := (← unsigned 16 account.amount) ++ (← unsigned 16 account.locked) ++ hash ++
      (← unsigned 8 account.storageUsage)
    entries := entries ++ [([0] ++ id, value)]
    if let some bytes := code then entries := entries ++ [([1] ++ id, bytes)]
  for ((id, pk), key) in state.accessKeys do
    unless Assoc.contains state.accounts id do throw "access key account is absent"
    let id ← accountId id
    entries := entries ++ [([2] ++ id ++ [2] ++ (← publicKey pk), ← accessKey key)]
  for (id, rows) in state.storage do
    unless Assoc.contains state.accounts id do throw "storage account is absent"
    let id ← accountId id
    unique "storage key" (rows.map Prod.fst)
    entries := entries ++ rows.map fun (key, value) => ([9] ++ id ++ [44] ++ key, value)
  unique "encoded state key" (entries.map Prod.fst)
  return entries

/-- The manipulator's future ID counter is not a native state record. -/
theorem encode_nextId (state : ChainState) (codes : List (String × Bytes)) (nextId : Nat) :
    encode { state with nextId } codes = encode state codes := rfl

end Near.StateEncoding
