import Model.Methods
import Proofs.Trie

namespace SputnikFactory

theorem Tx.run_bind (program : Tx α) (next : α → Tx β) (raw : Raw) :
    (program.bind next).run raw = (do
      let (value, updated) ← program.run raw
      (next value).run updated) := by
  induction program generalizing raw with
  | ret value => rfl
  | fail panic => rfl
  | inspect cont ih => simpa [Tx.bind, Tx.run] using ih raw raw
  | write key value cont ih =>
    simpa [Tx.bind, Tx.run] using ih (SputnikFactory.write raw key value)
  | erase key cont ih =>
    simpa [Tx.bind, Tx.run] using ih (remove raw key)

/-- Every primitive preserves uniqueness of raw trie keys. This holds even if a
decoded collection header points into an unexpected storage namespace. -/
theorem Tx.run_preserves_wf (program : Tx α) :
    ∀ raw value updated, raw.WF → program.run raw = .ok (value, updated) → updated.WF := by
  induction program with
  | ret value =>
    intro raw result updated hraw hrun
    simp [Tx.run] at hrun
    rcases hrun with ⟨rfl, rfl⟩
    exact hraw
  | fail panic =>
    intro raw result updated hraw hrun
    simp [Tx.run] at hrun
  | inspect next ih =>
    intro raw result updated hraw hrun
    exact ih raw raw result updated hraw (by simpa [Tx.run] using hrun)
  | write key value next ih =>
    intro raw result updated hraw hrun
    exact ih (SputnikFactory.write raw key value) result updated (write_wf raw key value hraw)
      (by simpa [Tx.run] using hrun)
  | erase key next ih =>
    intro raw result updated hraw hrun
    exact ih (remove raw key) result updated (remove_wf raw key hraw)
      (by simpa [Tx.run] using hrun)

theorem step_preserves_wf (cfg : Config) (raw : Raw) (env : Env) (call : Call)
    (hraw : raw.WF) (out : Outcome) (hstep : step cfg raw env call = .ok out) :
    out.raw.WF := by
  unfold step at hstep
  cases hrun : (entry cfg env call).run raw with
  | error panic => simp [hrun] at hstep
  | ok pair =>
    rcases pair with ⟨effects, updated⟩
    simp only [hrun, Except.ok.injEq] at hstep
    subst out
    exact Tx.run_preserves_wf (entry cfg env call) raw effects updated hraw hrun

/-- SDK privacy check executes before state loading or method code. -/
theorem private_callback_rejected (cfg : Config) (raw : Raw) (env : Env)
    (account predecessor : Account) (amount : Nat)
    (h : env.predecessor ≠ env.current) :
    step cfg raw env (.onCreate account amount predecessor) = .error .privateCall := by
  simp [step, entry, require, Call.private, h, Bind.bind, Pure.pure, Tx.run, Tx.bind]

/-- The generated nonpayable check executes even against uninitialized state. -/
theorem funded_init_rejected (cfg : Config) (raw : Raw) (env : Env)
    (h : env.deposit ≠ 0) :
    step cfg raw env .new = .error .deposit := by
  simp [step, entry, require, Call.private, Call.rejectDeposit, h,
    Bind.bind, Pure.pure, Tx.run, Tx.bind]

theorem funded_callback_rejected (cfg : Config) (raw : Raw) (env : Env)
    (account predecessor : Account) (amount : Nat)
    (hauth : env.predecessor = env.current) (hdeposit : env.deposit ≠ 0) :
    step cfg raw env (.onCreate account amount predecessor) = .error .deposit := by
  simp [step, entry, require, Call.private, Call.rejectDeposit, hauth, hdeposit,
    Bind.bind, Pure.pure, Tx.run, Tx.bind]

/-- Initialization is single-use, checked against the actual STATE key. -/
theorem initialized_factory_rejects_new (cfg : Config) (raw : Raw) (env : Env)
    (hdeposit : env.deposit = 0) (hstate : (read raw stateKey).isSome = true) :
    step cfg raw env .new = .error .initialized := by
  have hne : read raw stateKey ≠ none := by
    cases hread : read raw stateKey <;> simp_all
  simp [step, entry, require, Call.private, Call.rejectDeposit, Call.isNew,
    hdeposit, hne, load, Bind.bind, Pure.pure, Tx.run, Tx.bind]

/-- An empty trie initializes only STATE; the OWNER default remains implicit. -/
theorem init_empty (cfg : Config) (env : Env) (hdeposit : env.deposit = 0) :
    step cfg [] env .new =
      .ok ⟨write [] stateKey (Borsh.encodeSet initialSet), [], .unit⟩ := by
  simp [step, entry, require, Call.private, Call.rejectDeposit, Call.isNew,
    hdeposit, load, save, done, read, Bind.bind, Pure.pure, Tx.run, Tx.bind]

end SputnikFactory
