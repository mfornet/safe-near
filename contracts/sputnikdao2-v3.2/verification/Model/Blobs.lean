import Model.Policy
import Model.Upgrade

namespace SputnikDAO2

-- One fixed SHA-256 digest's raw key and owner-index entry. The digest,
-- LookupMap prefix and Borsh encoding are outside this projection.
structure BlobSlot where
  rawBytes : Option CodeBytes
  owner : Option String
  deriving Repr, DecidableEq

def hasBlob (slot : BlobSlot) : Bool := slot.rawBytes.isSome

def blobStorageCost (byteCost length : Nat) : Nat :=
  min (byteCost * (length + 32)) maxU128

-- Raw `store_blob` first loads contract STATE and input, checks the raw hash
-- key, charges `len + 32`, then writes bytes and the owner index. The return
-- value is the hash's JSON/base58 encoding, not modeled here.
def storeBlob (slot : BlobSlot) (stateLoaded : Bool)
    (caller : String) (input : Option CodeBytes)
    (attached byteCost : Nat) : Option BlobSlot := Id.run do
  if !stateLoaded then return none
  let some bytes := input | return none
  if slot.rawBytes.isSome then return none
  if attached < blobStorageCost byteCost bytes.length then return none
  return some ⟨some bytes, some caller⟩

-- `remove_blob` removes the index before checking caller and raw bytes; an
-- abort rolls those writes back. LookupMap.remove leaves its removed owner
-- value in the EVICTED register. A raw-key miss does not clear that register,
-- so the source refunds based on the stale owner-value length in that case.
-- `ownerValueLen` is the Borsh-serialized index value length, supplied by the
-- storage refinement. The refund uses the CURRENT storage price.
def removeBlob (slot : BlobSlot) (stateLoaded : Bool)
    (caller : String) (byteCost ownerValueLen : Nat) :
    Option (BlobSlot × Nat) := Id.run do
  if !stateLoaded then return none
  let some owner := slot.owner | return none
  if caller != owner then return none
  let evictedLen :=
    match slot.rawBytes with
    | some bytes => bytes.length
    | none => ownerValueLen
  return some (⟨none, none⟩, blobStorageCost byteCost evictedLen)

end SputnikDAO2
