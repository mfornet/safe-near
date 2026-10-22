import Model.Methods
import Proofs.Borsh
import Proofs.Transactions

namespace SputnikFactory

/-- Create selects its base receipt for promise_return. The callback receipt is
dependent on receipt 0 and does not change that return selection. -/
theorem create_returns_base_receipt (cfg : Config) (header : SetHeader)
    (raw : Raw) (env : Env) (name : Account) (args : Bytes)
    (hash : Hash) (code : Bytes)
    (haccount : validAccount (name ++ "." ++ env.current) = true)
    (hdefault : read raw defaultKey = some hash.val)
    (hcode : read raw hash.val = some code)
    (hdeposit : env.deposit ≥ 10 ^ 22) :
    (body cfg header env (.create name args)).run raw =
      .ok (⟨header,
        [⟨name ++ "." ++ env.current,
          [.createAccount, .transfer env.deposit, .useGlobal hash,
           .functionCall "new" args 0 (40 * 10 ^ 12) 0], none⟩,
         ⟨env.current,
          [.onCreate (name ++ "." ++ env.current) env.deposit env.predecessor
            (10 * 10 ^ 12)], some 0⟩],
        .promise 0⟩, raw) := by
  have hhash : Borsh.hash hash.val = some hash := by
    simp [Borsh.hash, hash.property]
  simp [body, loadDefault, haccount, hdefault, hhash, hcode, hdeposit,
    require, expect, done, load, Bind.bind, Pure.pure, Tx.bind, Tx.run]

theorem create_entry_returns_base_receipt (cfg : Config) (header : SetHeader)
    (raw : Raw) (env : Env) (name : Account) (args : Bytes)
    (hash : Hash) (code : Bytes)
    (hstate : read raw stateKey = some (Borsh.encodeSet header))
    (hindex : header.indexPrefix.length < 256 ^ 4)
    (hlen : header.elements.length < 256 ^ 8)
    (hprefix : header.elements.keyPrefix.length < 256 ^ 4)
    (haccount : validAccount (name ++ "." ++ env.current) = true)
    (hdefault : read raw defaultKey = some hash.val)
    (hcode : read raw hash.val = some code)
    (hdeposit : env.deposit ≥ 10 ^ 22) :
    step cfg raw env (.create name args) =
      .ok ⟨write raw stateKey (Borsh.encodeSet header),
        [⟨name ++ "." ++ env.current,
          [.createAccount, .transfer env.deposit, .useGlobal hash,
           .functionCall "new" args 0 (40 * 10 ^ 12) 0], none⟩,
         ⟨env.current,
          [.onCreate (name ++ "." ++ env.current) env.deposit env.predecessor
            (10 * 10 ^ 12)], some 0⟩],
        .promise 0⟩ := by
  have hbody := create_returns_base_receipt cfg header raw env name args hash code
    haccount hdefault hcode hdeposit
  simp [step, entry, loadFactory, hstate, exact_set_encode header hindex hlen hprefix,
    Call.private, Call.rejectDeposit, Call.isNew, Call.ownerOnly, Call.saveHeader,
    require, expect, load, save, Bind.bind, Pure.pure, Tx.run_bind, hbody,
    Tx.bind, Tx.run, Except.bind]

end SputnikFactory
