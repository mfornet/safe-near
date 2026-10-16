import Mathlib.Data.Finset.Basic
import Architect

/-!
# Basic types of the wNEAR model

Amounts are plain `Nat`; the `u128`/`u64` ranges of the on-chain
representation are tracked by well-formedness predicates on the state rather
than by wrapping arithmetic, so every overflow check in the contract becomes
an explicit branch of the model.
-/

namespace WNear

/-! yoctoNEAR amounts, wNEAR balances (`u128` on chain) and gas (`u64`) are
plain `Nat`. No type alias: `omega` does not see through `abbrev`s, and the
proofs lean on it heavily. -/

def u128Bound : Nat := 2 ^ 128
def u64Bound : Nat := 2 ^ 64

/-- `a`–`z` or `0`–`9`. -/
def isAccountIdChar (c : Char) : Bool :=
  ('a' ≤ c && c ≤ 'z') || ('0' ≤ c && c ≤ '9')

/-- `-`, `_` or `.`. -/
def isAccountIdSeparator (c : Char) : Bool :=
  c == '-' || c == '_' || c == '.'

/-- Character scan of `near_sdk::env::is_valid_account_id` (near-sdk 3.1.0):
separators may not be adjacent, lead, or trail. `lastSep` is "the previous
character was a separator" and starts `true`. -/
def accountIdScan : List Char → Bool → Bool
  | [], lastSep => !lastSep
  | c :: cs, lastSep =>
    if isAccountIdChar c then accountIdScan cs false
    else if isAccountIdSeparator c then !lastSep && accountIdScan cs true
    else false

/-- Validity of a NEAR account id as checked by near-sdk 3.1.0
(`/^(([a-z\d]+[-_])*[a-z\d]+\.)*([a-z\d]+[-_])*[a-z\d]+$/`, 2 to 64 bytes). -/
@[blueprint "def:valid-account-id"
  (statement := /-- A string is a \emph{valid account id} when it has 2 to 64 bytes and consists of lowercase letters, digits and the separators \texttt{-}, \texttt{\_}, \texttt{.}, with no separator first, last or next to another (near-sdk 3.1.0 \texttt{is\_valid\_account\_id}). -/)]
def isValidAccountId (s : String) : Bool :=
  2 ≤ s.utf8ByteSize && s.utf8ByteSize ≤ 64 && accountIdScan s.toList true

/-- A valid NEAR account id. Every account id the model manipulates is valid:
the SDK rejects invalid ids in arguments (`ValidAccountId`) and the runtime only
ever supplies valid predecessor / current account ids. -/
@[blueprint "def:account-id"
  (statement := /-- An \emph{account id} is a string satisfying \cref{def:valid-account-id}. -/)]
abbrev AccountId := { s : String // isValidAccountId s = true }

instance : ToString AccountId := ⟨fun a => a.val⟩
instance : Repr AccountId := ⟨fun a _ => repr a.val⟩

/-- Longest possible account id, in bytes. -/
def maxAccountIdBytes : Nat := 64

theorem AccountId.utf8ByteSize_le (a : AccountId) : a.val.utf8ByteSize ≤ maxAccountIdBytes := by
  have h := a.property
  simp only [isValidAccountId, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.2

end WNear
