import Model.Methods
import Proofs.Borsh
import Proofs.Transactions

namespace SputnikFactory

/-- A failed base creation callback never inserts a DAO in the modeled body.
It schedules a detached transfer of the entire original deposit instead. -/
theorem failed_creation_refunds (cfg : Config) (header : SetHeader) (raw : Raw)
    (env : Env) (account predecessor : Account) (amount : Nat)
    (hresults : env.results = [.failed]) :
    (body cfg header env (.onCreate account amount predecessor)).run raw =
      .ok (⟨header, [⟨predecessor, [.transfer amount], none⟩], .boolean false⟩, raw) := by
  simp [body, callbackSuccess, hresults, done, Bind.bind, Pure.pure, Tx.bind, Tx.run]

/-- Callback result bytes carry no semantic payload for the registration
decision. Successful means the set insertion path is selected. -/
theorem successful_creation_selects_insert (cfg : Config) (header : SetHeader)
    (env : Env) (account predecessor : Account) (amount : Nat) (bytes : Bytes)
    (hresults : env.results = [.successful bytes]) :
    body cfg header env (.onCreate account amount predecessor) =
      (do
        let updated ← setInsert header account
        done updated (.boolean true)) := by
  simp [body, callbackSuccess, hresults, Bind.bind, Pure.pure, Tx.bind]

theorem unready_creation_aborts (cfg : Config) (header : SetHeader) (raw : Raw)
    (env : Env) (account predecessor : Account) (amount : Nat)
    (hresults : env.results = [.notReady]) :
    (body cfg header env (.onCreate account amount predecessor)).run raw =
      .error .notReady := by
  simp [body, callbackSuccess, hresults, Bind.bind, Tx.bind, Tx.run]

theorem missing_callback_result_aborts (cfg : Config) (header : SetHeader) (raw : Raw)
    (env : Env) (account predecessor : Account) (amount : Nat)
    (hresults : env.results = []) :
    (body cfg header env (.onCreate account amount predecessor)).run raw =
      .error .callbackArity := by
  simp [body, callbackSuccess, hresults, Bind.bind, Tx.bind, Tx.run]

/-- Full exported callback branch, including the SDK wrapper and STATE commit. -/
theorem failed_creation_entry_refunds (cfg : Config) (header : SetHeader) (raw : Raw)
    (env : Env) (account predecessor : Account) (amount : Nat)
    (hread : read raw stateKey = some (Borsh.encodeSet header))
    (hindex : header.indexPrefix.length < 256 ^ 4)
    (hlen : header.elements.length < 256 ^ 8)
    (hprefix : header.elements.keyPrefix.length < 256 ^ 4)
    (hauth : env.predecessor = env.current)
    (hdeposit : env.deposit = 0)
    (hresults : env.results = [.failed]) :
    step cfg raw env (.onCreate account amount predecessor) =
      .ok ⟨write raw stateKey (Borsh.encodeSet header),
        [⟨predecessor, [.transfer amount], none⟩], .boolean false⟩ := by
  simp [step, entry, loadFactory, hread, exact_set_encode header hindex hlen hprefix,
    body, callbackSuccess, hresults, hauth, hdeposit, Call.private,
    Call.rejectDeposit, Call.isNew, Call.ownerOnly, Call.saveHeader,
    require, expect, done, load, save, Bind.bind, Pure.pure, Tx.bind, Tx.run]

/-- A successful callback commits the updated set header and creates no refund. -/
theorem successful_creation_entry_registers (cfg : Config) (header updated : SetHeader)
    (raw afterInsert : Raw) (env : Env) (account predecessor : Account)
    (amount : Nat) (bytes : Bytes)
    (hread : read raw stateKey = some (Borsh.encodeSet header))
    (hindex : header.indexPrefix.length < 256 ^ 4)
    (hlen : header.elements.length < 256 ^ 8)
    (hprefix : header.elements.keyPrefix.length < 256 ^ 4)
    (hauth : env.predecessor = env.current)
    (hdeposit : env.deposit = 0)
    (hresults : env.results = [.successful bytes])
    (hinsert : (setInsert header account).run raw = .ok (updated, afterInsert)) :
    step cfg raw env (.onCreate account amount predecessor) =
      .ok ⟨write afterInsert stateKey (Borsh.encodeSet updated), [], .boolean true⟩ := by
  simp [step, entry, loadFactory, hread, exact_set_encode header hindex hlen hprefix,
    body, callbackSuccess, hresults, hauth, hdeposit, Call.private,
    Call.rejectDeposit, Call.isNew, Call.ownerOnly, Call.saveHeader,
    require, expect, done, load, save, Bind.bind, Pure.pure,
    Tx.run_bind, hinsert, Tx.bind, Tx.run, Except.bind]

end SputnikFactory
