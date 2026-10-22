import Proofs.Authorization
import Proofs.StorageProjection

namespace SputnikFactory

/-- An owner-authorized update writes only the raw OWNER record. The source
signature takes `&self`, so the SDK wrapper does not reject an attached deposit
in ordinary transaction context. -/
theorem set_owner_entry (cfg : Config) (raw : Raw) (env : Env)
    (header : SetHeader) (replacement : Account)
    (hstate : read raw stateKey = some (Borsh.encodeSet header))
    (hindex : header.indexPrefix.length < 256 ^ 4)
    (hlen : header.elements.length < 256 ^ 8)
    (hprefix : header.elements.keyPrefix.length < 256 ^ 4)
    (howner : (getOwner env.current).run raw = .ok (env.predecessor, raw)) :
    step cfg raw env (.setOwner replacement) =
      .ok ⟨write raw ownerKey replacement.toUTF8.data.toList, [], .unit⟩ := by
  have hdecode := exact_set_encode header hindex hlen hprefix
  simp [step, entry, loadFactory, assertOwner, hstate, hdecode, howner,
    body, done, Call.private, Call.rejectDeposit, Call.isNew,
    Call.ownerOnly, Call.saveHeader, require, expect, load, save,
    Bind.bind, Pure.pure, Tx.run_bind, Tx.bind, Tx.run, Except.bind]

theorem get_owner_after_write (raw : Raw) (current replacement : Account)
    (hvalid : validAccount replacement = true) :
    (getOwner current).run
      (write raw ownerKey replacement.toUTF8.data.toList) =
      .ok (replacement, write raw ownerKey replacement.toUTF8.data.toList) := by
  have hutf8 := string_utf8_roundtrip replacement
  simp only [String.toUTF8_eq_toByteArray] at hutf8 ⊢
  simp [getOwner, read_write_self, hutf8, hvalid,
    load, require, expect, Bind.bind, Pure.pure,
    Tx.bind, Tx.run]

/-- Setting a valid owner changes the result of the exported owner getter.
Validity is explicit because the pure Call type does not enforce JSON AccountId
argument validation; concrete wrapper refinement must discharge it. -/
theorem set_owner_then_getter (cfg : Config) (raw : Raw) (env : Env)
    (header : SetHeader) (replacement : Account)
    (hstate : read raw stateKey = some (Borsh.encodeSet header))
    (hindex : header.indexPrefix.length < 256 ^ 4)
    (hlen : header.elements.length < 256 ^ 8)
    (hprefix : header.elements.keyPrefix.length < 256 ^ 4)
    (howner : (getOwner env.current).run raw = .ok (env.predecessor, raw))
    (hvalid : validAccount replacement = true) :
    let after := write raw ownerKey replacement.toUTF8.data.toList
    step cfg raw env (.setOwner replacement) = .ok ⟨after, [], .unit⟩ ∧
    step cfg after env .getOwner =
      .ok ⟨after, [], .account replacement⟩ := by
  dsimp
  constructor
  · exact set_owner_entry cfg raw env header replacement hstate hindex hlen
      hprefix howner
  · have hstate' : read
        (write raw ownerKey replacement.toUTF8.data.toList) stateKey =
        some (Borsh.encodeSet header) := by
      rw [read_write_other _ _ _ _ (by decide : stateKey ≠ ownerKey)]
      exact hstate
    have hdecode := exact_set_encode header hindex hlen hprefix
    have hnew := get_owner_after_write raw env.current replacement hvalid
    simp only [String.toUTF8_eq_toByteArray] at hstate' hnew ⊢
    simp [step, entry, loadFactory, hstate', hdecode, body, hnew,
      done, Call.private, Call.rejectDeposit, Call.isNew,
      Call.ownerOnly, Call.saveHeader, require, expect, load,
      Bind.bind, Pure.pure, Tx.run_bind, Tx.bind, Tx.run, Except.bind]

/-- After a valid owner change, the prior predecessor cannot execute another
owner-only method in the same factory context. -/
theorem set_owner_revokes_prior_predecessor (cfg : Config) (raw : Raw)
    (env : Env) (header : SetHeader) (replacement : Account) (call : Call)
    (hownerOnly : call.ownerOnly = true)
    (hstate : read raw stateKey = some (Borsh.encodeSet header))
    (hindex : header.indexPrefix.length < 256 ^ 4)
    (hlen : header.elements.length < 256 ^ 8)
    (hprefix : header.elements.keyPrefix.length < 256 ^ 4)
    (howner : (getOwner env.current).run raw = .ok (env.predecessor, raw))
    (hvalid : validAccount replacement = true)
    (hprior : env.predecessor ≠ replacement) :
    let after := write raw ownerKey replacement.toUTF8.data.toList
    step cfg raw env (.setOwner replacement) = .ok ⟨after, [], .unit⟩ ∧
    step cfg after env call = .error .owner := by
  dsimp
  constructor
  · exact set_owner_entry cfg raw env header replacement hstate hindex hlen
      hprefix howner
  · have hstate' : read
        (write raw ownerKey replacement.toUTF8.data.toList) stateKey =
        some (Borsh.encodeSet header) := by
      rw [read_write_other _ _ _ _ (by decide : stateKey ≠ ownerKey)]
      exact hstate
    have hnew := get_owner_after_write raw env.current replacement hvalid
    exact owner_only_rejects_other cfg _ env call header replacement hownerOnly
      hstate' hindex hlen hprefix hnew hprior

/-- The default setter checks raw key presence. The value at that key is not
decoded as Wasm, nor is a metadata or global-code record required. -/
theorem set_default_entry (cfg : Config) (raw : Raw) (env : Env)
    (header : SetHeader) (hash : Hash) (bytes : Bytes)
    (hstate : read raw stateKey = some (Borsh.encodeSet header))
    (hindex : header.indexPrefix.length < 256 ^ 4)
    (hlen : header.elements.length < 256 ^ 8)
    (hprefix : header.elements.keyPrefix.length < 256 ^ 4)
    (howner : (getOwner env.current).run raw = .ok (env.predecessor, raw))
    (hcode : read raw hash.val = some bytes) :
    step cfg raw env (.setDefault hash) =
      .ok ⟨write raw defaultKey hash.val, [], .unit⟩ := by
  have hdecode := exact_set_encode header hindex hlen hprefix
  simp [step, entry, loadFactory, assertOwner, hstate, hdecode, howner,
    body, hcode, done, Call.private, Call.rejectDeposit, Call.isNew,
    Call.ownerOnly, Call.saveHeader, require, expect, load, save,
    Bind.bind, Pure.pure, Tx.run_bind, Tx.bind, Tx.run, Except.bind]

theorem set_default_missing_raw_key (cfg : Config) (raw : Raw) (env : Env)
    (header : SetHeader) (hash : Hash)
    (hstate : read raw stateKey = some (Borsh.encodeSet header))
    (hindex : header.indexPrefix.length < 256 ^ 4)
    (hlen : header.elements.length < 256 ^ 8)
    (hprefix : header.elements.keyPrefix.length < 256 ^ 4)
    (howner : (getOwner env.current).run raw = .ok (env.predecessor, raw))
    (hmissing : read raw hash.val = none) :
    step cfg raw env (.setDefault hash) = .error .codeMissing := by
  have hdecode := exact_set_encode header hindex hlen hprefix
  simp [step, entry, loadFactory, assertOwner, hstate, hdecode, howner,
    body, hmissing, Call.private, Call.rejectDeposit, Call.isNew,
    Call.ownerOnly, Call.saveHeader, require, expect, load,
    Bind.bind, Pure.pure, Tx.run_bind, Tx.bind, Tx.run, Except.bind]

theorem set_default_then_getter (cfg : Config) (raw : Raw) (env : Env)
    (header : SetHeader) (hash : Hash) (bytes : Bytes)
    (hstate : read raw stateKey = some (Borsh.encodeSet header))
    (hindex : header.indexPrefix.length < 256 ^ 4)
    (hlen : header.elements.length < 256 ^ 8)
    (hprefix : header.elements.keyPrefix.length < 256 ^ 4)
    (howner : (getOwner env.current).run raw = .ok (env.predecessor, raw))
    (hcode : read raw hash.val = some bytes) :
    let after := write raw defaultKey hash.val
    step cfg raw env (.setDefault hash) = .ok ⟨after, [], .unit⟩ ∧
    step cfg after env .defaultHash = .ok ⟨after, [], .hash hash⟩ := by
  dsimp
  constructor
  · exact set_default_entry cfg raw env header hash bytes hstate hindex hlen
      hprefix howner hcode
  · have hstate' : read (write raw defaultKey hash.val) stateKey =
        some (Borsh.encodeSet header) := by
      rw [read_write_other _ _ _ _ (by decide : stateKey ≠ defaultKey)]
      exact hstate
    have hdecode := exact_set_encode header hindex hlen hprefix
    have hhash : Borsh.hash hash.val = some hash := by
      simp [Borsh.hash, hash.property]
    simp [step, entry, loadFactory, hstate', hdecode, body,
      loadDefault, read_write_self, hhash, done,
      Call.private, Call.rejectDeposit, Call.isNew,
      Call.ownerOnly, Call.saveHeader, require, expect, load,
      Bind.bind, Pure.pure, Tx.bind, Tx.run]

end SputnikFactory
