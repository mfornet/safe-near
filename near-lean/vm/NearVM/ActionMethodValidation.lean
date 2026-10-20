import NearVM.Metered

namespace Wasm.Near

/-- The VM mock's opaque-byte external policy is an explicit context choice. -/
theorem actionMethodEncodingError_opaque (name : String) (before : Store NearState) (args : List Value)
    (hpolicy : before.host.config.validateActionMethodUtf8 = false) :
    actionMethodEncodingError name before args = none := by
  simp [actionMethodEncodingError, hpolicy]

/-- Runtime external rejection retains the native structured error. -/
theorem actionMethodEncodingError_invalid (name : String) (before : Store NearState) (args : List Value)
    (bytes : List UInt8) (hpolicy : before.host.config.validateActionMethodUtf8 = true)
    (hinput : actionMethodBytes? name before args = some bytes)
    (hutf8 : String.fromUTF8? ⟨bytes.toArray⟩ = none) :
    actionMethodEncodingError name before args = some .invalidMethodName := by
  simp [actionMethodEncodingError, hpolicy, hinput, hutf8]

/-- Successful external validation supplies an actual decoded string; lossy
fallback decoding is not an assumption of this theorem. -/
theorem actionMethodEncodingError_none_utf8 (name : String) (before : Store NearState) (args : List Value)
    (bytes : List UInt8) (hpolicy : before.host.config.validateActionMethodUtf8 = true)
    (hinput : actionMethodBytes? name before args = some bytes)
    (h : actionMethodEncodingError name before args = none) :
    ∃ decoded, String.fromUTF8? ⟨bytes.toArray⟩ = some decoded := by
  cases he : String.fromUTF8? ⟨bytes.toArray⟩ with
  | none => simp [actionMethodEncodingError, hpolicy, hinput, he] at h
  | some decoded => exact ⟨decoded, rfl⟩

/-- Fees and prepaid gas are checked before runtime external decoding. -/
theorem finishMeteredCall_charge_error (extra : Nat) (name : String) (before after : Store NearState)
    (args values : List Value) (paid : NearState) (error : HostError)
    (hcharge : applyCharges after.host (chargesAfter name before after args) = (paid, some error)) :
    finishMeteredCall extra name before args (.Return values after) = trapWith { after with host := paid } error := by
  simp only [finishMeteredCall, hcharge]

/-- A balance failure wins over an invalid method encoding, for every policy
and byte sequence. This follows from the executable post-call order. -/
theorem finishMeteredCall_deposit_error (extra : Nat) (name : String) (before after : Store NearState)
    (args values : List Value) (paid : NearState) (final : Store NearState) (error : HostError)
    (hcharge : applyCharges after.host (chargesAfter name before after args) = (paid, none))
    (hdeposit : deductDeposit name before { after with host := paid } args = (final, some error)) :
    finishMeteredCall extra name before args (.Return values after) = trapWith final error := by
  simp only [finishMeteredCall, hcharge, hdeposit]

/-- A successful actual post-call return has passed external validation. -/
theorem finishMeteredCall_success_encoding (extra : Nat) (name : String) (before : Store NearState)
    (args : List Value) (result : HostResult NearState) (values : List Value) (after : Store NearState)
    (hreturn : finishMeteredCall extra name before args result = .Return values after) :
    actionMethodEncodingError name before args = none := by
  cases result with
  | Trap st message => simp [finishMeteredCall] at hreturn
  | Throw st tag vals => simp [finishMeteredCall] at hreturn
  | Return vals st =>
    unfold finishMeteredCall at hreturn
    repeat' (first | assumption | contradiction | (split at hreturn) | (dsimp only at hreturn; split at hreturn))

/-- A concrete successful return under the runtime policy has UTF-8 method
bytes. The earlier charging/deposit checks need no additional assumptions. -/
theorem finishMeteredCall_success_method_utf8 (extra : Nat) (name : String) (before : Store NearState)
    (args : List Value) (result : HostResult NearState) (values : List Value) (after : Store NearState)
    (bytes : List UInt8) (hpolicy : before.host.config.validateActionMethodUtf8 = true)
    (hinput : actionMethodBytes? name before args = some bytes)
    (hreturn : finishMeteredCall extra name before args result = .Return values after) :
    ∃ decoded, String.fromUTF8? ⟨bytes.toArray⟩ = some decoded :=
  actionMethodEncodingError_none_utf8 name before args bytes hpolicy hinput
    (finishMeteredCall_success_encoding extra name before args result values after hreturn)

end Wasm.Near
