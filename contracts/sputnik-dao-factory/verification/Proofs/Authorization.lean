import Proofs.Borsh
import Proofs.Transactions

namespace SputnikFactory

theorem getOwner_depends_only_on_owner_key (raw updated : Raw) (current owner : Account)
    (hread : read updated ownerKey = read raw ownerKey)
    (howner : (getOwner current).run raw = .ok (owner, raw)) :
    (getOwner current).run updated = .ok (owner, updated) := by
  simp only [getOwner, load, expect, require, Bind.bind, Pure.pure,
    Tx.run_bind, Tx.bind, Tx.run] at howner ⊢
  rw [hread]
  simp only [String.toUTF8_eq_toByteArray] at *
  cases hparse : String.fromUTF8?
      ⟨(((read raw ownerKey).getD current.toByteArray.data.toList).toArray)⟩ with
  | none => simp [hparse, Tx.run, Except.bind] at howner
  | some decoded =>
    by_cases hvalid : validAccount decoded = true
    · simp [hparse, hvalid, Tx.run, Except.bind] at howner ⊢
      exact howner
    · simp [hparse, hvalid, Tx.run, Except.bind] at howner

/-- If the stored effective owner decodes successfully, every owner-only entry
point rejects a different predecessor before its method body can run. -/
theorem owner_only_rejects_other (cfg : Config) (raw : Raw) (env : Env)
    (call : Call) (header : SetHeader) (owner : Account)
    (hownerOnly : call.ownerOnly = true)
    (hstate : read raw stateKey = some (Borsh.encodeSet header))
    (hindex : header.indexPrefix.length < 256 ^ 4)
    (hlen : header.elements.length < 256 ^ 8)
    (hprefix : header.elements.keyPrefix.length < 256 ^ 4)
    (howner : (getOwner env.current).run raw = .ok (owner, raw))
    (hcaller : env.predecessor ≠ owner) :
    step cfg raw env call = .error .owner := by
  have hprivate : call.private = false := by
    cases call <;> simp_all [Call.ownerOnly, Call.private]
  have hdeposit : call.rejectDeposit = false := by
    cases call <;> simp_all [Call.ownerOnly, Call.rejectDeposit]
  have hnew : call.isNew = false := by
    cases call <;> simp_all [Call.ownerOnly, Call.isNew]
  have hdecode := exact_set_encode header hindex hlen hprefix
  have hother : owner ≠ env.predecessor := Ne.symm hcaller
  simp [step, entry, loadFactory, assertOwner, hstate, hdecode,
    hprivate, hdeposit, hnew, hownerOnly, howner, hother,
    require, expect, load, Bind.bind, Pure.pure, Tx.run_bind,
    Tx.bind, Tx.run, Except.bind]

end SputnikFactory
