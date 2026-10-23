import Model.Methods
import NearInterface.Json
import Wasm.Bytes

/-!
# The model's view of the function-call boundary

`NearInterface.Context` is what one real call receives; the model reads it
as an `Env`. Two facts make the reading exact:

* nearcore's account-id rules (`validAccountIdBytes`, on bytes) and
  near-sdk 3.1.0's (`isValidAccountId`, on characters) accept the same
  strings, so the context's account ids are model account ids;
* the callback result is parsed as near-sdk does,
  `serde_json::from_slice::<U128>`, on the raw promise result.
-/

namespace WNear

open Wasm.Near

/-! ## Account ids -/

theorem toUTF8_toList_eq_flatMap (s : String) :
    s.toUTF8.toList = s.toList.flatMap String.utf8EncodeChar := by
  rw [← String.ofList_toList (s := s)]
  simp only [String.toUTF8_eq_toByteArray, String.toByteArray_ofList, String.toList_ofList]
  induction s.toList with
  | nil => simp [List.utf8Encode_nil, Wasm.ByteEncoding.byteArray_toList_eq]
  | cons c l ih =>
    rw [List.utf8Encode_cons, List.utf8Encode_singleton]
    simp only [Wasm.ByteEncoding.byteArray_toList_eq] at ih ⊢
    simp [ih]

/-- One character of the byte-level scan: an ASCII character is its own byte;
any other character starts with a byte at or above `0x80`, which the scan rejects. -/
theorem accountIdFormat_utf8EncodeChar (p : Bool) (c : Char) (rest : List UInt8) :
    accountIdFormat p (String.utf8EncodeChar c ++ rest) =
      if isAccountIdChar c then accountIdFormat false rest
      else if isAccountIdSeparator c then (!p && accountIdFormat true rest) else false := by
  have hle : ∀ d : Char, (c ≤ d ↔ c.toNat ≤ d.toNat) := fun d => by
    rw [Char.le_def]; simp [UInt32.le_iff_toNat_le]
  have hge : ∀ d : Char, (d ≤ c ↔ d.toNat ≤ c.toNat) := fun d => by
    rw [Char.le_def]; simp [UInt32.le_iff_toNat_le]
  have heq : ∀ d : Char, (c == d) = decide (c.toNat = d.toNat) := fun d => by
    rw [beq_eq_decide]; congr 1; exact propext Char.toNat_inj.symm
  simp only [isAccountIdChar, isAccountIdSeparator, heq, hle, hge]
  by_cases h : c.toNat ≤ 0x7f
  · have hb : (UInt8.ofNat c.toNat).toNat = c.toNat := by
      simp only [UInt8.toNat_ofNat']; omega
    simp only [String.utf8EncodeChar, show c.val.toNat = c.toNat from rfl, h, ite_true,
      List.cons_append, List.nil_append, accountIdFormat, hb]
    simp only [show 'a'.toNat = 97 from rfl, show 'z'.toNat = 122 from rfl,
      show '0'.toNat = 48 from rfl, show '9'.toNat = 57 from rfl, show '-'.toNat = 45 from rfl,
      show '_'.toNat = 95 from rfl, show '.'.toNat = 46 from rfl]
    generalize c.toNat = n at *
    split_ifs <;> simp_all
  · obtain ⟨b, bs, hcode, hb⟩ : ∃ b bs, String.utf8EncodeChar c = b :: bs ∧ 128 ≤ b.toNat := by
      unfold String.utf8EncodeChar
      simp only [show c.val.toNat = c.toNat from rfl]
      split_ifs <;> refine ⟨_, _, rfl, ?_⟩ <;> simp only [UInt8.toNat_ofNat'] <;> omega
    rw [hcode, List.cons_append, accountIdFormat]
    simp only [show 'a'.toNat = 97 from rfl, show 'z'.toNat = 122 from rfl,
      show '0'.toNat = 48 from rfl, show '9'.toNat = 57 from rfl, show '-'.toNat = 45 from rfl,
      show '_'.toNat = 95 from rfl, show '.'.toNat = 46 from rfl]
    have : ¬ b.toNat ≤ 122 := by omega
    split_ifs <;> simp_all <;> omega

theorem accountIdFormat_flatMap (l : List Char) (p : Bool) :
    accountIdFormat p (l.flatMap String.utf8EncodeChar) = accountIdScan l p := by
  induction l generalizing p with
  | nil => simp [accountIdFormat, accountIdScan]
  | cons c l ih => rw [List.flatMap_cons, accountIdFormat_utf8EncodeChar, accountIdScan, ih, ih]

/-- nearcore's and near-sdk 3.1.0's account-id rules agree on every string. -/
theorem validAccountIdBytes_toUTF8 (s : String) :
    validAccountIdBytes s.toUTF8.toList = isValidAccountId s := by
  have hlen : s.toUTF8.toList.length = s.utf8ByteSize := by
    rw [Wasm.ByteEncoding.byteArray_toList_length]; simp [String.toUTF8_eq_toByteArray]
  unfold validAccountIdBytes isValidAccountId
  rw [hlen, toUTF8_toList_eq_flatMap, accountIdFormat_flatMap]

/-- A protocol account id as a model account id. -/
def AccountId.ofNear (a : NearInterface.AccountId) : AccountId :=
  ⟨a.val, by rw [← validAccountIdBytes_toUTF8]; exact a.property⟩

/-- A model account id as a protocol account id. -/
def AccountId.toNear (a : AccountId) : NearInterface.AccountId :=
  ⟨a.val, by rw [validAccountIdBytes_toUTF8]; exact a.property⟩

@[simp] theorem AccountId.toNear_ofNear (a : NearInterface.AccountId) :
    (AccountId.ofNear a).toNear = a := rfl

@[simp] theorem AccountId.ofNear_toNear (a : AccountId) : AccountId.ofNear a.toNear = a := rfl

/-! ## The environment of one call -/

/-- `serde_json::from_slice::<U128>` on a successful callback's return value. -/
def parseU128Result (bytes : List UInt8) : Option Nat :=
  (NearInterface.Json.parse bytes).bind NearInterface.Json.u128

/-- `env::promise_result(0)` as `ft_resolve_transfer` reads it; `none` when
the call has no promise results. Results past the first are not read. -/
def callbackResultOf (results : List Wasm.PromiseResult) : Option PromiseResult :=
  match results.head? with
  | none => none
  | some .notReady => some .notReady
  | some .failed => some .failed
  | some (.successful bytes) => some (.successful (parseU128Result bytes))

/-- The model's reading of a context. -/
def Env.ofContext (ctx : NearInterface.Context) : Env where
  currentAccount := .ofNear ctx.current
  predecessor := .ofNear ctx.predecessor
  attachedDeposit := ctx.attached
  prepaidGas := ctx.prepaidGas
  promiseResult := callbackResultOf ctx.promiseResults

/-- The model's parameters under a protocol configuration. -/
def Config.ofRuntime (cfg : RuntimeConfig) : Config :=
  { extraBytesPerRecord := cfg.fees.numExtraBytesRecord }

end WNear
