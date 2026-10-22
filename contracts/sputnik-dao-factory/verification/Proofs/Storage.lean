import Spec.Storage
import Proofs.Borsh
import Proofs.Transactions

namespace SputnikFactory

theorem initialized_empty_dao_layout :
    Spec.DaoLayout
      (write [] stateKey (Borsh.encodeSet initialSet)) [] := by
  constructor
  · simp
  · change read (write [] stateKey (Borsh.encodeSet initialSet)) stateKey =
      some (Borsh.encodeSet initialSet)
    exact read_write_self [] stateKey (Borsh.encodeSet initialSet)
  · intro account
    have hne : daoIndexKey account ≠ stateKey := by
      intro he
      have hlen := congrArg List.length he
      simp [dao_index_key_length, stateKey] at hlen
      omega
    rw [read_write_other [] stateKey (daoIndexKey account)
      (Borsh.encodeSet initialSet) hne]
    simp [Spec.findAccount, read]
  · intro index hindex
    simp at hindex

theorem new_establishes_empty_dao_layout (cfg : Config) (env : Env)
    (out : Outcome) (hdeposit : env.deposit = 0)
    (hstep : step cfg [] env .new = .ok out) :
    Spec.DaoLayout out.raw [] := by
  rw [init_empty cfg env hdeposit] at hstep
  cases hstep
  exact initialized_empty_dao_layout

/-- Canonical set representation excludes code bytes at an index key for an
account absent from the vector. This premise is not preserved by arbitrary
hash-key writes, which is why DAO coherence must be conditional. -/
theorem absent_dao_collision_has_no_raw_code (raw : Raw) (order : List Account)
    (layout : Spec.DaoLayout raw order) (account : Account) (hash : Hash)
    (habsent : Spec.findAccount order account = none)
    (halias : codeKey hash = daoIndexKey account) :
    read raw (codeKey hash) = none := by
  rw [halias, layout.index, habsent]
  rfl

theorem initialized_empty_metadata_layout :
    Spec.MetadataLayout
      (write [] metadataKey (Borsh.encodeMap initialMap)) [] := by
  constructor
  · simp
  · change read (write [] metadataKey (Borsh.encodeMap initialMap)) metadataKey =
      some (Borsh.encodeMap initialMap)
    exact read_write_self [] metadataKey (Borsh.encodeMap initialMap)
  · intro hash
    have hne : mapIndexKey initialMap hash ≠ metadataKey := by
      intro he
      have hlen := congrArg List.length he
      simp [mapIndexKey, initialMap, metadataKey, hash.property] at hlen
    rw [read_write_other [] metadataKey (mapIndexKey initialMap hash)
      (Borsh.encodeMap initialMap) hne]
    simp [Spec.findHash, read]
  · intro index hindex
    simp at hindex
  · intro index hindex
    simp at hindex

/-- The metadata getter is empty only when the map header is present and
decodable; `new` alone does not create that header. -/
theorem empty_metadata_getter (cfg : Config) (raw : Raw) (env : Env)
    (hstate : read raw stateKey = some (Borsh.encodeSet initialSet))
    (hmetadata : read raw metadataKey = some (Borsh.encodeMap initialMap)) :
    step cfg raw env .getMetadata = .ok ⟨raw, [], .metadata []⟩ := by
  have hs : Borsh.exact Borsh.setHeader (Borsh.encodeSet initialSet) =
      some initialSet := by decide
  have hm : Borsh.exact Borsh.mapHeader (Borsh.encodeMap initialMap) =
      some initialMap := by decide
  simp [step, entry, loadFactory, loadMap, hstate, hmetadata, hs, hm,
    body, mapLength, done, Call.private, Call.rejectDeposit,
    Call.isNew, Call.ownerOnly, Call.saveHeader, require, expect, load,
    Bind.bind, Pure.pure, Tx.bind, Tx.run]
  simp [initialMap, metadataAt, Pure.pure, Tx.bind, Tx.run]

theorem metadata_getter_requires_header (cfg : Config) (raw : Raw) (env : Env)
    (hstate : read raw stateKey = some (Borsh.encodeSet initialSet))
    (hmissing : read raw metadataKey = none) :
    step cfg raw env .getMetadata = .error .metadataMissing := by
  have hs : Borsh.exact Borsh.setHeader (Borsh.encodeSet initialSet) =
      some initialSet := by decide
  simp [step, entry, loadFactory, loadMap, hstate, hmissing, hs,
    body, Call.private, Call.rejectDeposit, Call.isNew, Call.ownerOnly,
    Call.saveHeader, require, expect, load,
    Bind.bind, Pure.pure, Tx.bind, Tx.run]

/-- Canonical DAO layout makes the exported count equal the explicit vector
order's length. This is conditional on the u64 serialization bound. -/
theorem dao_count_matches_layout (cfg : Config) (raw : Raw) (env : Env)
    (order : List Account) (hlayout : Spec.DaoLayout raw order)
    (hlen : order.length < 256 ^ 8) :
    step cfg raw env .daoCount = .ok ⟨raw, [], .count order.length⟩ := by
  have hdecode :
      Borsh.exact Borsh.setHeader (Borsh.encodeSet (Spec.daoHeader order)) =
        some (Spec.daoHeader order) := by
    apply exact_set_encode
    · simp [Spec.daoHeader, initialSet]
    · simpa [Spec.daoHeader] using hlen
    · simp [Spec.daoHeader, initialSet]
  simp [step, entry, loadFactory, hlayout.state, hdecode,
    body, done, Call.private, Call.rejectDeposit, Call.isNew,
    Call.ownerOnly, Call.saveHeader, require, expect, load,
    Bind.bind, Pure.pure, Tx.bind, Tx.run]
  rfl

end SputnikFactory
