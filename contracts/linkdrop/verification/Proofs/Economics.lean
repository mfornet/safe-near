import Spec.Economics
import Proofs.Safety

namespace Linkdrop

theorem sendAvailable : Spec.SendAvailable := by
  intro s e k hi hd
  simp [step, body, hi, hd, Call.payable, Call.view, Call.private]

theorem sendCreditBound : Spec.SendCreditBound := by
  intro s e k out h
  have hb := step_ok_body h
  simp only [body] at hb
  split at hb <;> simp_all
  subst out
  simp only [State.set, ↓reduceIte, Option.getD_some]
  exact Nat.min_le_left _ _

theorem send_exact_without_saturation (s : State) (e : Env) (k : Key)
    (hfit : (s.accounts k).getD 0 + e.deposit ≤ maxAmount) :
    min ((s.accounts k).getD 0 + e.deposit) maxAmount =
      (s.accounts k).getD 0 + e.deposit := Nat.min_eq_left hfit

theorem claimAvailable : Spec.ClaimAvailable := by
  intro s e account amount hi hd hp hk
  simp [step, body, hi, hd, hp, hk, Call.payable, Call.view, Call.private]

theorem claim_consumes (s : State) (e : Env) (account : Account) (out : Outcome)
    (h : step s e (.claim account) = .ok out) :
    out.state.accounts e.signerKey = none := by
  have hb := step_ok_body h
  simp only [body] at hb
  split at hb <;> simp_all
  subst out
  exact set_same ..

theorem claim_cannot_repeat (s : State) (e : Env) (account : Account) (out : Outcome)
    (h : step s e (.claim account) = .ok out) :
    body out.state e (.claim account) = .error .missingKey := by
  simp [body, claim_consumes s e account out h]

theorem failedClaimRestore : Spec.FailedClaimRestore := by
  intro s e amount hi hd hp hr
  simp [step, body, hi, hd, hp, hr, callbackSuccess, Call.payable, Call.view, Call.private]

theorem failedCreationRefund : Spec.FailedCreationRefund := by
  intro s e predecessor amount hi hd hp hr
  simp [step, body, hi, hd, hp, hr, callbackSuccess, Call.payable, Call.view, Call.private]

theorem successful_claim_callback (s : State) (e : Env) (amount : Nat)
    (hi : s.initialized = true) (hd : e.deposit = 0) (hp : e.predecessor = e.current)
    (hr : e.results = [.successful []]) :
    step s e (.onClaimed amount) =
      .ok ⟨s, [⟨e.current, [.deleteKey e.signerKey], none⟩], .boolean true⟩ := by
  simp [step, body, hi, hd, hp, hr, callbackSuccess, Call.payable, Call.view, Call.private]

theorem advancedValidation : Spec.AdvancedValidation := by
  intro s e account options hi
  constructor
  · intro ho
    simp [step, body, hi, ho, Call.payable, Call.private]
  · intro ho hn
    simp [step, body, hi, ho, hn, Call.payable, Call.private]

theorem zero_allowance_is_unlimited (key : Key) (receiver : Account) (methods : String) :
    limitedAction ⟨key, 0, receiver, methods⟩ =
      .limitedKey key none receiver methods := by rfl

theorem empty_vector_is_present : ({ fullKeys := some [] } : Options).present = true := by decide

theorem view_balance_correct (s : State) (e : Env) (k : Key) (n : Nat)
    (hi : s.initialized = true) (hk : s.accounts k = some n) :
    step s e (.getBalance k) = .ok ⟨s, [], .balance n⟩ := by
  simp [step, body, hi, hk, Call.private, Call.payable, Call.view]

theorem view_information_correct (s : State) (e : Env) (k : Key) (n : Nat)
    (hi : s.initialized = true) (hk : s.accounts k = some n) :
    step s e (.getInformation k) = .ok ⟨s, [], .information n⟩ := by
  simp [step, body, hi, hk, Call.private, Call.payable, Call.view]

theorem missing_views_fail (s : State) (e : Env) (k : Key)
    (hi : s.initialized = true) (hk : s.accounts k = none) :
    step s e (.getBalance k) = .error .missingKey ∧
      step s e (.getInformation k) = .error .missingKey := by
  simp [step, body, hi, hk, Call.private, Call.payable, Call.view]

theorem simple_creation_available (s : State) (e : Env) (account : Account) (key : Key)
    (hi : s.initialized = true) :
    step s e (.createAccount account key) = .ok
      (creation s e account [.create, .fullKey key, .transfer e.deposit]
        (.onCreated e.predecessor e.deposit callbackGas callbackWeight)) := by
  simp [step, body, hi, Call.private, Call.payable]

theorem advanced_creation_available (s : State) (e : Env) (account : Account) (o : Options)
    (hi : s.initialized = true) (hp : o.present = true) (hn : o.deployments ≤ 1) :
    step s e (.createAdvanced account o) = .ok
      (creation s e account ([.create, .transfer e.deposit] ++ optionActions o)
        (.onCreated e.predecessor e.deposit callbackGas callbackWeight)) := by
  simp [step, body, hi, hp, Nat.not_lt.mpr hn, Call.private, Call.payable]

theorem claim_creation_available (s : State) (e : Env) (account : Account) (key : Key)
    (amount : Nat) (hi : s.initialized = true) (hd : e.deposit = 0)
    (hp : e.predecessor = e.current) (hk : s.accounts e.signerKey = some amount) :
    step s e (.createAndClaim account key) = .ok
      (creation (s.set e.signerKey none) e account [.create, .fullKey key, .transfer amount]
        (.onClaimed amount callbackGas callbackWeight)) := by
  simp [step, body, hi, hd, hp, hk, Call.private, Call.payable, Call.view]

theorem callback_success_ignores_bytes (e : Env) (bytes : List UInt8) :
    callbackSuccess { e with results := [.successful bytes] } = .ok true := rfl

theorem callback_not_ready_aborts (e : Env) :
    callbackSuccess { e with results := [.notReady] } = .error .resultNotReady := rfl

end Linkdrop
