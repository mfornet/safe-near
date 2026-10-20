import Mathlib.Tactic.SplitIfs
import NearRuntime.Nonce

namespace Near

open Wasm.Near

/-- Supported ordinary-key envelopes preserve the native version/feature split. -/
theorem transactionVersionSupported_iff (tx : Transaction) (cfg : RuntimeConfig) :
    tx.versionSupported cfg = true ↔
      (tx.version = 0 ∧ tx.nonceMode = .monotonic) ∨
      (tx.version = 1 ∧ cfg.v1TransactionsEnabled = true) := by
  cases hm : tx.nonceMode <;> simp [Transaction.versionSupported, hm]

attribute [local simp] bind pure throw Except.bind Except.pure Except.map

def NonceOrdered (mode : NonceMode) (nonce current : Nat) : Prop :=
  match mode with
  | .monotonic => current < nonce
  | .strict => current < 2 ^ 64 - 1 ∧ nonce = current + 1

/-- Exact executable success condition, including optional height and checked
strict increment. The lower ordering check takes precedence over the ceiling. -/
theorem verifyNonce_success_iff (nonce current : Nat) (height : Option Nat) (mode : NonceMode) :
    verifyNonce nonce current height mode = .ok () ↔
      NonceOrdered mode nonce current ∧ ∀ h, height = some h → nonce < nonceUpperBound h := by
  cases mode <;> cases height <;> simp [verifyNonce, NonceOrdered]
  all_goals split_ifs <;> simp_all
  all_goals omega

theorem verifyNonce_increases (nonce current : Nat) (height : Option Nat) (mode : NonceMode)
    (h : verifyNonce nonce current height mode = .ok ()) : current < nonce := by
  have hp := (verifyNonce_success_iff nonce current height mode).mp h
  cases mode <;> simp_all [NonceOrdered]

theorem verifyNonce_below_ceiling (nonce current height : Nat) (mode : NonceMode)
    (h : verifyNonce nonce current (some height) mode = .ok ()) : nonce < nonceUpperBound height :=
  ((verifyNonce_success_iff nonce current (some height) mode).mp h).2 height rfl

theorem verifyNonce_u64 (nonce current height : Nat) (mode : NonceMode)
    (h : verifyNonce nonce current (some height) mode = .ok ()) : nonce < 2 ^ 64 - 1 := by
  have hb := verifyNonce_below_ceiling nonce current height mode h
  have hm := Nat.min_le_right (height * 1_000_000) (2 ^ 64 - 1)
  exact Nat.lt_of_lt_of_le hb hm

end Near
