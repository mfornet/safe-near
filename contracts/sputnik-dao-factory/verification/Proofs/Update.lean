import Proofs.Authorization
import Proofs.DaoAliasGetter

namespace SputnikFactory

/-- `update` reads the effective owner before checking either allowed caller.
Successful calls then use raw membership and code-key reads and schedule one
weighted receiver call; they do not mutate factory storage. -/
theorem update_body_success (cfg : Config) (header : SetHeader)
    (raw : Raw) (env : Env) (account : Account) (hash : Hash)
    (owner : Account) (code marker : Bytes)
    (howner : (getOwner env.current).run raw = .ok (owner, raw))
    (hauth : env.predecessor = owner ∨ env.predecessor = account)
    (hmember : read raw (setIndexKey header account) = some marker)
    (hcode : read raw hash.val = some code) :
    (body cfg header env (.update account hash)).run raw =
      .ok (⟨header,
        [⟨account, [.functionCall "update" code 0 0 1], none⟩],
        .promise 0⟩, raw) := by
  simp [body, howner, hauth, setContains, hmember, hcode,
    require, expect, load, done, Bind.bind, Pure.pure,
    Tx.run_bind, Tx.bind, Tx.run, Except.bind]

theorem update_entry_receipt (cfg : Config) (header : SetHeader)
    (raw : Raw) (env : Env) (account : Account) (hash : Hash)
    (owner : Account) (code marker : Bytes)
    (hstate : read raw stateKey = some (Borsh.encodeSet header))
    (hindex : header.indexPrefix.length < 256 ^ 4)
    (hlen : header.elements.length < 256 ^ 8)
    (hprefix : header.elements.keyPrefix.length < 256 ^ 4)
    (howner : (getOwner env.current).run raw = .ok (owner, raw))
    (hauth : env.predecessor = owner ∨ env.predecessor = account)
    (hmember : read raw (setIndexKey header account) = some marker)
    (hcode : read raw hash.val = some code) :
    step cfg raw env (.update account hash) =
      .ok ⟨raw, [⟨account, [.functionCall "update" code 0 0 1], none⟩],
        .promise 0⟩ := by
  have hdecode := exact_set_encode header hindex hlen hprefix
  have hbody := update_body_success cfg header raw env account hash owner code
    marker howner hauth hmember hcode
  simp [step, entry, loadFactory, hstate, hdecode, hbody,
    Call.private, Call.rejectDeposit, Call.isNew, Call.ownerOnly,
    Call.saveHeader, require, expect, load, Bind.bind, Pure.pure,
    Tx.run_bind, Tx.bind, Tx.run, Except.bind]

theorem update_body_denied (cfg : Config) (header : SetHeader)
    (raw : Raw) (env : Env) (account : Account) (hash : Hash)
    (owner : Account)
    (howner : (getOwner env.current).run raw = .ok (owner, raw))
    (hnotOwner : env.predecessor ≠ owner)
    (hnotDao : env.predecessor ≠ account) :
    (body cfg header env (.update account hash)).run raw =
      .error .updateAuthority := by
  simp [body, howner, hnotOwner, hnotDao, require,
    Bind.bind, Pure.pure, Tx.run_bind, Tx.bind, Tx.run, Except.bind]

theorem update_body_missing_member (cfg : Config) (header : SetHeader)
    (raw : Raw) (env : Env) (account : Account) (hash : Hash)
    (owner : Account)
    (howner : (getOwner env.current).run raw = .ok (owner, raw))
    (hauth : env.predecessor = owner ∨ env.predecessor = account)
    (hmissing : read raw (setIndexKey header account) = none) :
    (body cfg header env (.update account hash)).run raw =
      .error .daoMissing := by
  simp [body, howner, hauth, setContains, hmissing, require,
    load, Bind.bind, Pure.pure, Tx.run_bind, Tx.bind, Tx.run, Except.bind]

theorem update_body_missing_code (cfg : Config) (header : SetHeader)
    (raw : Raw) (env : Env) (account : Account) (hash : Hash)
    (owner : Account) (marker : Bytes)
    (howner : (getOwner env.current).run raw = .ok (owner, raw))
    (hauth : env.predecessor = owner ∨ env.predecessor = account)
    (hmember : read raw (setIndexKey header account) = some marker)
    (hmissing : read raw hash.val = none) :
    (body cfg header env (.update account hash)).run raw =
      .error .codeMissing := by
  simp [body, howner, hauth, setContains, hmember, hmissing,
    require, expect, load, Bind.bind, Pure.pure, Tx.run_bind,
    Tx.bind, Tx.run, Except.bind]

theorem update_entry_body_error (cfg : Config) (header : SetHeader)
    (raw : Raw) (env : Env) (account : Account) (hash : Hash)
    (panic : Panic)
    (hstate : read raw stateKey = some (Borsh.encodeSet header))
    (hindex : header.indexPrefix.length < 256 ^ 4)
    (hlen : header.elements.length < 256 ^ 8)
    (hprefix : header.elements.keyPrefix.length < 256 ^ 4)
    (hbody : (body cfg header env (.update account hash)).run raw =
      .error panic) :
    step cfg raw env (.update account hash) = .error panic := by
  have hdecode := exact_set_encode header hindex hlen hprefix
  simp [step, entry, loadFactory, hstate, hdecode, hbody,
    Call.private, Call.rejectDeposit, Call.isNew, Call.ownerOnly,
    Call.saveHeader, require, expect, load, Bind.bind, Pure.pure,
    Tx.run_bind, Tx.bind, Tx.run, Except.bind]

theorem update_entry_denied (cfg : Config) (header : SetHeader)
    (raw : Raw) (env : Env) (account : Account) (hash : Hash)
    (owner : Account)
    (hstate : read raw stateKey = some (Borsh.encodeSet header))
    (hindex : header.indexPrefix.length < 256 ^ 4)
    (hlen : header.elements.length < 256 ^ 8)
    (hprefix : header.elements.keyPrefix.length < 256 ^ 4)
    (howner : (getOwner env.current).run raw = .ok (owner, raw))
    (hnotOwner : env.predecessor ≠ owner)
    (hnotDao : env.predecessor ≠ account) :
    step cfg raw env (.update account hash) = .error .updateAuthority :=
  update_entry_body_error cfg header raw env account hash .updateAuthority
    hstate hindex hlen hprefix
    (update_body_denied cfg header raw env account hash owner howner
      hnotOwner hnotDao)

theorem update_entry_missing_member (cfg : Config) (header : SetHeader)
    (raw : Raw) (env : Env) (account : Account) (hash : Hash)
    (owner : Account)
    (hstate : read raw stateKey = some (Borsh.encodeSet header))
    (hindex : header.indexPrefix.length < 256 ^ 4)
    (hlen : header.elements.length < 256 ^ 8)
    (hprefix : header.elements.keyPrefix.length < 256 ^ 4)
    (howner : (getOwner env.current).run raw = .ok (owner, raw))
    (hauth : env.predecessor = owner ∨ env.predecessor = account)
    (hmissing : read raw (setIndexKey header account) = none) :
    step cfg raw env (.update account hash) = .error .daoMissing :=
  update_entry_body_error cfg header raw env account hash .daoMissing
    hstate hindex hlen hprefix
    (update_body_missing_member cfg header raw env account hash owner howner
      hauth hmissing)

theorem update_entry_missing_code (cfg : Config) (header : SetHeader)
    (raw : Raw) (env : Env) (account : Account) (hash : Hash)
    (owner : Account) (marker : Bytes)
    (hstate : read raw stateKey = some (Borsh.encodeSet header))
    (hindex : header.indexPrefix.length < 256 ^ 4)
    (hlen : header.elements.length < 256 ^ 8)
    (hprefix : header.elements.keyPrefix.length < 256 ^ 4)
    (howner : (getOwner env.current).run raw = .ok (owner, raw))
    (hauth : env.predecessor = owner ∨ env.predecessor = account)
    (hmember : read raw (setIndexKey header account) = some marker)
    (hmissing : read raw hash.val = none) :
    step cfg raw env (.update account hash) = .error .codeMissing :=
  update_entry_body_error cfg header raw env account hash .codeMissing
    hstate hindex hlen hprefix
    (update_body_missing_code cfg header raw env account hash owner marker
      howner hauth hmember hmissing)

theorem alias_only_owner_missing : read aliasOnlyRaw ownerKey = none := by decide

theorem alias_only_owner_is_current (current : Account)
    (hvalid : validAccount current = true) :
    (getOwner current).run aliasOnlyRaw = .ok (current, aliasOnlyRaw) := by
  have hutf8 := string_utf8_roundtrip current
  simp only [String.toUTF8_eq_toByteArray] at hutf8 ⊢
  simp [getOwner, alias_only_owner_missing, hutf8, hvalid,
    load, expect, require, Bind.bind, Pure.pure, Tx.bind, Tx.run]

/-- In a constructed raw state, the same code/DAO key alias satisfies both
`update` existence checks while the DAO vector remains empty. The scheduled
payload is the four raw bytes, not validated Wasm. This is a model witness,
not a claim that the state is reachable through public transactions. -/
theorem update_alias_without_registered_dao (cfg : Config) (env : Env)
    (hauth : env.predecessor = env.current)
    (hvalid : validAccount env.current = true) :
    step cfg aliasOnlyRaw env (.update collisionAccount collisionHash) =
      .ok ⟨aliasOnlyRaw,
        [⟨collisionAccount,
          [.functionCall "update" [0, 97, 115, 109] 0 0 1], none⟩],
        .promise 0⟩ := by
  have hstate : read aliasOnlyRaw stateKey =
      some (Borsh.encodeSet initialSet) := by decide
  have howner : (getOwner env.current).run aliasOnlyRaw =
      .ok (env.current, aliasOnlyRaw) :=
    alias_only_owner_is_current env.current hvalid
  have hmember : read aliasOnlyRaw (setIndexKey initialSet collisionAccount) =
      some [0, 97, 115, 109] := by
    simpa [setIndexKey, initialSet, daoIndexKey] using alias_only_membership
  have hcode : read aliasOnlyRaw collisionHash.val =
      some [0, 97, 115, 109] := by decide
  exact update_entry_receipt cfg initialSet aliasOnlyRaw env collisionAccount
    collisionHash env.current [0, 97, 115, 109] [0, 97, 115, 109]
    hstate (by decide) (by decide) (by decide) howner (Or.inl hauth)
    hmember hcode

end SputnikFactory
