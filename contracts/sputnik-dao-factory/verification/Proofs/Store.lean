import Model.Methods
import Proofs.Borsh
import Proofs.Transactions

namespace SputnikFactory

theorem saturating_mul_bounded (left right : Nat) :
    saturatingMul left right ≤ maxAmount := by
  exact Nat.min_le_right _ _

theorem store_cost_bounded (cfg : Config) (before after : Raw) :
    storeCost cfg before after ≤ maxAmount :=
  saturating_mul_bounded _ _

/-- Local code insertion and the global deployment action are both selected
only after the source's storage-deposit check succeeds. Global publication
itself is asynchronous and remains outside this call's guarantee. -/
theorem store_body_success (cfg : Config) (header : SetHeader) (raw : Raw)
    (env : Env) (bytes : Bytes)
    (hinput : env.input = some bytes)
    (hmissing : read raw (cfg.sha256 bytes).val = none)
    (hcost : storeCost cfg raw (write raw (cfg.sha256 bytes).val bytes) ≤ env.deposit) :
    (body cfg header env .store).run raw =
      .ok (⟨header,
        [⟨env.current, [.deployGlobal bytes], none⟩],
        .hash (cfg.sha256 bytes)⟩,
        write raw (cfg.sha256 bytes).val bytes) := by
  simp [body, snapshot, hinput, hmissing, hcost,
    require, expect, done, load, save,
    Bind.bind, Pure.pure, Tx.bind, Tx.run]

theorem store_body_underfunded (cfg : Config) (header : SetHeader) (raw : Raw)
    (env : Env) (bytes : Bytes)
    (hinput : env.input = some bytes)
    (hmissing : read raw (cfg.sha256 bytes).val = none)
    (hcost : env.deposit < storeCost cfg raw (write raw (cfg.sha256 bytes).val bytes)) :
    (body cfg header env .store).run raw = .error .insufficientDeposit := by
  have hnot : ¬storeCost cfg raw (write raw (cfg.sha256 bytes).val bytes) ≤
      env.deposit := Nat.not_le.mpr hcost
  simp [body, snapshot, hinput, hmissing, hnot,
    require, expect, done, load, save,
    Bind.bind, Pure.pure, Tx.bind, Tx.run]

/-- The exported store call aborts after its modeled provisional write when
underfunded. The atomic evaluator returns no committed trie or receipt. -/
theorem store_entry_underfunded (cfg : Config) (header : SetHeader) (raw : Raw)
    (env : Env) (bytes : Bytes)
    (hstate : read raw stateKey = some (Borsh.encodeSet header))
    (hindex : header.indexPrefix.length < 256 ^ 4)
    (hlen : header.elements.length < 256 ^ 8)
    (hprefix : header.elements.keyPrefix.length < 256 ^ 4)
    (howner : (getOwner env.current).run raw = .ok (env.predecessor, raw))
    (hinput : env.input = some bytes)
    (hmissing : read raw (cfg.sha256 bytes).val = none)
    (hcost : env.deposit < storeCost cfg raw (write raw (cfg.sha256 bytes).val bytes)) :
    step cfg raw env .store = .error .insufficientDeposit := by
  have hbody := store_body_underfunded cfg header raw env bytes hinput hmissing hcost
  have hdecode := exact_set_encode header hindex hlen hprefix
  simp [step, entry, loadFactory, assertOwner, hstate, hdecode, howner,
    Call.private, Call.rejectDeposit, Call.isNew, Call.ownerOnly,
    require, expect, load, Bind.bind, Pure.pure, Tx.run_bind, hbody,
    Tx.bind, Tx.run, Except.bind]

theorem store_entry_success (cfg : Config) (header : SetHeader) (raw : Raw)
    (env : Env) (bytes : Bytes)
    (hstate : read raw stateKey = some (Borsh.encodeSet header))
    (hindex : header.indexPrefix.length < 256 ^ 4)
    (hlen : header.elements.length < 256 ^ 8)
    (hprefix : header.elements.keyPrefix.length < 256 ^ 4)
    (howner : (getOwner env.current).run raw = .ok (env.predecessor, raw))
    (hinput : env.input = some bytes)
    (hmissing : read raw (cfg.sha256 bytes).val = none)
    (hcost : storeCost cfg raw (write raw (cfg.sha256 bytes).val bytes) ≤ env.deposit) :
    step cfg raw env .store =
      .ok ⟨write (write raw (cfg.sha256 bytes).val bytes)
          stateKey (Borsh.encodeSet header),
        [⟨env.current, [.deployGlobal bytes], none⟩],
        .hash (cfg.sha256 bytes)⟩ := by
  have hbody := store_body_success cfg header raw env bytes hinput hmissing hcost
  have hdecode := exact_set_encode header hindex hlen hprefix
  simp [step, entry, loadFactory, assertOwner, hstate, hdecode, howner,
    Call.private, Call.rejectDeposit, Call.isNew, Call.ownerOnly,
    Call.saveHeader, require, expect, load, save,
    Bind.bind, Pure.pure, Tx.run_bind, hbody,
    Tx.bind, Tx.run, Except.bind]

end SputnikFactory
