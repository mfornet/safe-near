import Model.ExportWrapper
import Model.Blobs
import Model.BlobKeySeparation

namespace SputnikDAO2

structure RawBlobContext where
  predecessor : String
  attachedDeposit : Nat
  deriving Repr, DecidableEq

-- One digest's two-key image. This says nothing about other trie keys,
-- hash preimages, or serialization of the full Contract root.
def blobSlotRawImage (raw : BountyRawTrie)
    (digest : BountyBytes) (slot : BlobSlot) : Prop :=
  raw digest = slot.rawBytes ∧
    raw (daoBlobOwnerKey digest) =
      slot.owner.map bountyBorshString

/-! Manual `store_blob` is not passed through the generated call wrapper.
`sha256` is an external hash oracle; byte-level digest correctness and the
JSON/base58 return value are separate obligations. The projected Contract
root and raw trie must later be joined by a storage-image relation. -/

def runStoreBlobExport (raw : BountyRawTrie)
    (ctx : RawBlobContext) (state : Option BlobSlot)
    (input : Option BountyBytes) (sha256 : BountyBytes → BountyBytes)
    (byteCost : Nat) (encodeRoot : BlobSlot → BountyBytes) :
    Option (BountyRawTrie × BountyBytes) := do
  let before ← state
  let bytes ← input
  let digest := sha256 bytes
  if digest.length != 32 then none else pure ()
  if (raw digest).isSome then none else pure ()
  let after ← storeBlob before true ctx.predecessor (some bytes)
    ctx.attachedDeposit byteCost
  let afterRaw ← daoRawBlobInsert raw digest bytes
    (bountyBorshString ctx.predecessor)
  some (bountyRawWrite afterRaw daoRootKey (encodeRoot after), digest)

/-! Composition of the generated `remove_blob` wrapper with the source's
owner check, raw-key removal, and refund calculation. `state` is the decoded
blob-slot projection of Contract state; `encodeRoot` supplies complete root
serialization. `ownerValueLen` is the evicted owner index's serialized byte
length, including the source's stale-register case on raw-key miss. -/

def runRemoveBlobExport (raw : BountyRawTrie)
    (ctx : CallWrapperContext) (state : Option BlobSlot)
    (digest : BountyBytes) (byteCost ownerValueLen : Nat)
    (encodeRoot : BlobSlot → BountyBytes) :
    Option (BountyRawTrie × Nat) := do
  if digest.length != 32 then none else pure ()
  let before ← state
  let (after, refund) ← removeBlob before true ctx.predecessor
    byteCost ownerValueLen
  let final ← runGeneratedCallWrapper raw "remove_blob"
    { ctx with stateDecoded := state.isSome }
    (some (daoRawBlobRemove raw digest, encodeRoot after))
  some (final, refund)

end SputnikDAO2
