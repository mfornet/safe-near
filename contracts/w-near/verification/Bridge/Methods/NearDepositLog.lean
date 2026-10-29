import Bridge.Functions.DepositTail
import Bridge.Functions.ToVec
import Model

/-!
# `near_deposit`'s log is the model's (M8)

The bytes `DepositTail.tail232_spec` logs are `logW (decDigits amount) ab 4`, `"Deposit "`, the
amount's decimal digits, `" NEAR to "` and the account's bytes. For the predecessor `a`'s bytes,
they are the UTF-8 of the model's `s!"Deposit {amount} NEAR to {a}"` (`logW_model`), and the host's
`logsOf` reads the model's string back (`log_utf8String`).
-/

namespace WNear.Binary.NearDepositLog

open WNear.Binary WNear.Binary.DepositLog WNear.Binary.FmtDigits

/-- **The log's bytes are the model's text.** -/
theorem logW_model (amount : Nat) (a : WNear.AccountId) :
    logW (decDigits amount) a.val.toUTF8.toList 4 = (s!"Deposit {amount} NEAR to {a}").toUTF8.toList := by
  obtain ⟨h1, h2⟩ := ToVec.toDigits_dec amount
  have e : toString amount = String.ofList (Nat.toDigits 10 amount) := rfl
  have ea : toString a = a.val := rfl
  have q1 : ("Deposit " : String) = String.ofList "Deposit ".toList := rfl
  have q2 : (" NEAR to " : String) = String.ofList " NEAR to ".toList := rfl
  simp only [e, ea]
  show _ = ("Deposit " ++ String.ofList (Nat.toDigits 10 amount) ++ " NEAR to " ++ a.val).toUTF8.toList
  rw [q1, q2]
  simp only [String.toUTF8_eq_toByteArray, String.toByteArray_append, String.toByteArray_ofList, List.utf8Encode,
    ToVec.flat_ascii _ h2, ToVec.toList_eq, ByteArray.data_append, Array.toList_append]
  rw [ToVec.flat_ascii _ (by decide), ToVec.flat_ascii " NEAR to ".toList (by decide)]
  simp [h1, logW]
  rfl

/-- **The host reads the model's log back**: `logsOf`'s decoding of the logged bytes. -/
theorem log_utf8String (amount : Nat) (a : WNear.AccountId) :
    (String.fromUTF8? ⟨(logW (decDigits amount) a.val.toUTF8.toList 4).toArray⟩).getD "" =
      s!"Deposit {amount} NEAR to {a}" := by
  rw [logW_model, Wasm.ByteEncoding.byteArray_of_toList, Wasm.ByteEncoding.string_fromUTF8_toUTF8]
  rfl

end WNear.Binary.NearDepositLog
