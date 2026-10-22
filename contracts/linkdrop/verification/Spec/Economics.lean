import Spec.Safety

namespace Linkdrop.Spec

/-- Exact credit, including saturation, and the access-key permission request.
No assertion is made that the separate key-add receipt will succeed. -/
def SendAvailable : Prop :=
  ∀ s e k, s.initialized = true → e.deposit ≠ 0 →
    step s e (.send k) = .ok ⟨s.set k (some (min ((s.accounts k).getD 0 + e.deposit) maxAmount)),
      [⟨e.current, [.limitedKey k (some keyAllowance) e.current
        "claim,create_account_and_claim"], none⟩], .promise 0⟩

/-- Each deposit increases this key's liability by at most the deposited amount.
Equality needs an explicit no-saturation assumption. -/
def SendCreditBound : Prop :=
  ∀ s e k out, step s e (.send k) = .ok out →
    (out.state.accounts k).getD 0 ≤ (s.accounts k).getD 0 + e.deposit

/-- Claim consumes the signer key once, schedules deletion separately, and returns
only the payout receipt. Completion of either action is a runtime obligation. -/
def ClaimAvailable : Prop :=
  ∀ s e account amount, s.initialized = true → e.deposit = 0 →
    e.predecessor = e.current → s.accounts e.signerKey = some amount →
    step s e (.claim account) = .ok ⟨s.set e.signerKey none,
      [⟨e.current, [.deleteKey e.signerKey], none⟩,
       ⟨account, [.transfer amount], none⟩], .promise 1⟩

/-- A failed creation callback restores exactly its argument. It does not add to
an intervening deposit. Provenance of the argument needs receipt-level reasoning. -/
def FailedClaimRestore : Prop :=
  ∀ s e amount, s.initialized = true → e.deposit = 0 → e.predecessor = e.current →
    e.results = [.failed] →
    step s e (.onClaimed amount) =
      .ok ⟨s.set e.signerKey (some amount), [], .boolean false⟩

/-- A failed direct creation schedules exactly the original deposit to the
predecessor captured in its callback arguments; it does not wait for the refund. -/
def FailedCreationRefund : Prop :=
  ∀ s e predecessor amount, s.initialized = true → e.deposit = 0 →
    e.predecessor = e.current → e.results = [.failed] →
    step s e (.onCreated predecessor amount) =
      .ok ⟨s, [⟨predecessor, [.transfer amount], none⟩], .boolean false⟩

/-- Some [] satisfies the option presence check. Only the four deployment fields
are mutually exclusive; key vectors can accompany a deployment. -/
def AdvancedValidation : Prop :=
  ∀ s e account options, s.initialized = true →
    (options.present = false →
      step s e (.createAdvanced account options) = .error .noOptions) ∧
    (options.present = true → options.deployments > 1 →
      step s e (.createAdvanced account options) = .error .conflictingOptions)

end Linkdrop.Spec
