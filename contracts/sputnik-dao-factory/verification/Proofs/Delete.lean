import Proofs.Authorization
import Proofs.Trie

namespace SputnikFactory

/-- The delete helper can erase provisional code before discovering a missing
METADATA header. Its exported caller must rely on transactional rollback. -/
theorem delete_body_missing_metadata (cfg : Config) (header : SetHeader)
    (raw : Raw) (env : Env) (target defaultHash : Hash)
    (hdefault : read raw defaultKey = some defaultHash.val)
    (hdifferent : defaultHash ≠ target)
    (hmetadata : read raw metadataKey = none)
    (howner : (getOwner env.current).run raw = .ok (env.predecessor, raw)) :
    (body cfg header env (.deleteContract target)).run raw =
      .error .metadataMissing := by
  let after := remove raw target.val
  have hownerKey : ownerKey ≠ target.val := by
    intro he
    have hlen := congrArg List.length he
    simp [ownerKey, target.property] at hlen
  have hmetadataKey : metadataKey ≠ target.val := by
    intro he
    have hlen := congrArg List.length he
    simp [metadataKey, target.property] at hlen
  have hreadOwner : read after ownerKey = read raw ownerKey :=
    read_remove_other raw target.val ownerKey hownerKey
  have hownerAfter : (getOwner env.current).run after =
      .ok (env.predecessor, after) :=
    getOwner_depends_only_on_owner_key raw after env.current env.predecessor
      hreadOwner howner
  have hreadMetadata : read after metadataKey = none := by
    rw [read_remove_other raw target.val metadataKey hmetadataKey]
    exact hmetadata
  have hhash : Borsh.hash defaultHash.val = some defaultHash := by
    simp [Borsh.hash, defaultHash.property]
  simp [body, loadDefault, loadMap, deletionMetadata, assertOwner,
    hdefault, hhash, hdifferent, hownerAfter, hreadMetadata,
    after, require, expect, load, erase,
    Bind.bind, Pure.pure, Tx.run_bind, Tx.bind, Tx.run, Except.bind]

theorem delete_entry_missing_metadata (cfg : Config) (header : SetHeader)
    (raw : Raw) (env : Env) (target defaultHash : Hash)
    (hstate : read raw stateKey = some (Borsh.encodeSet header))
    (hindex : header.indexPrefix.length < 256 ^ 4)
    (hlen : header.elements.length < 256 ^ 8)
    (hprefix : header.elements.keyPrefix.length < 256 ^ 4)
    (hdefault : read raw defaultKey = some defaultHash.val)
    (hdifferent : defaultHash ≠ target)
    (hmetadata : read raw metadataKey = none)
    (howner : (getOwner env.current).run raw = .ok (env.predecessor, raw)) :
    step cfg raw env (.deleteContract target) = .error .metadataMissing := by
  have hbody := delete_body_missing_metadata cfg header raw env target defaultHash
    hdefault hdifferent hmetadata howner
  have hdecode := exact_set_encode header hindex hlen hprefix
  simp [step, entry, loadFactory, assertOwner, hstate, hdecode, howner,
    Call.private, Call.rejectDeposit, Call.isNew, Call.ownerOnly,
    require, expect, load, Bind.bind, Pure.pure, Tx.run_bind, hbody,
    Tx.bind, Tx.run, Except.bind]

end SputnikFactory
