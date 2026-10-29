import Bridge.Methods.NearDepositWords
import Bridge.Methods.NearDepositLog

/-!
# The successful deposit's amount and log

The binary's two-word subtraction is the model's subtraction after the registration
check. Consequently its minted amount, account record and log encode the model values.
-/

namespace WNear.Binary.NearDepositMethod

open Wasm Wasm.Near WasmLogic NearLogic NearInterface
open WNear.Binary.DepositBody

/-- A successful new-account branch has already checked that registration is affordable. -/
theorem dcase_ok_min (dep min supply : Nat) (hc : dcase dep none min supply = .ok) : min ≤ dep := by
  by_cases hd : dep = 0
  · simp only [dcase, hd, ite_true] at hc
    cases hc
  · by_contra hm
    have hsmall : dep < min := Nat.lt_of_not_ge hm
    rw [dcase, if_neg hd, if_pos ⟨rfl, hsmall⟩] at hc
    cases hc

/-- The two subtracted words denote the mathematical difference, without wraparound. -/
theorem amount232_eq (h : NearState) (reg : Option (UInt64 × UInt64)) (xb : List UInt8)
    (hm : reg = none → minOf xb ≤ depOf h) :
    amount232 h reg xb = amountOf (depOf h) (regB reg) (minOf xb) := by
  cases reg with
  | some p => rfl
  | none =>
    have hmin := minOf_words xb
    have hle : (mloOf xb).toNat + 2 ^ 64 * (mhiOf xb).toNat ≤
        (EnvGetters.depLo h).toNat + 2 ^ 64 * (EnvGetters.depHi h).toNat := by
      rw [hmin]
      exact hm rfl
    have hsub := Cmp128.sub128_words (EnvGetters.depLo h) (EnvGetters.depHi h) (mloOf xb) (mhiOf xb) hle
    change (aloOf h xb).toNat + 2 ^ 64 * (ahiOf h xb).toNat = depOf h - minOf xb
    rw [hsub, hmin]

/-- The amount recorded in the initialized method's postcondition is the model's mint. -/
theorem amount232_model (ctx : Context) (raw : RawStorage) (s : WNear.State)
    (hwf : ctx.WF raw) (hs : s.WF) (h : NearState)
    (he : eraseP h = eraseP (hostOf ctx raw))
    (hok : caseDep h s (regOf s (.ofNear ctx.predecessor)) = .ok) :
    amount232 h (regOf s (.ofNear ctx.predecessor)) (WNear.Borsh.u64 s.accountStorageUsage) =
      amountOf ctx.attached (modelReg s (.ofNear ctx.predecessor)) s.storageMin := by
  have hmin : regOf s (.ofNear ctx.predecessor) = none →
      minOf (WNear.Borsh.u64 s.accountStorageUsage) ≤ depOf h := by
    intro hr
    rw [caseDep, case232, hr, regB, Option.map_none] at hok
    exact dcase_ok_min _ _ _ hok
  rw [amount232_eq h _ _ hmin, depOf_of_eraseP ctx raw hwf h he, regB_regOf s _ hs, minOf_model s hs]

/-- The words sent to the formatter are precisely `amount232`. -/
theorem text232_amount (h : NearState) (reg : Option (UInt64 × UInt64)) (xb : List UInt8) :
    text232 h reg xb = DepositLog.logW (FmtDigits.decDigits (amount232 h reg xb))
      h.context.predecessorAccountId 4 := by
  cases reg with
  | none =>
    unfold text232 amount232
    unfold DepositTail.logText FmtU128.val
    rfl
  | some p =>
    unfold text232 amount232
    unfold DepositTail.logText FmtU128.val depOf
    rfl

/-- On success, the logged bytes are exactly the model's message, including the fee deduction. -/
theorem text232_model (ctx : Context) (raw : RawStorage) (s : WNear.State)
    (hwf : ctx.WF raw) (hs : s.WF) (h : NearState)
    (he : eraseP h = eraseP (hostOf ctx raw))
    (hok : caseDep h s (regOf s (.ofNear ctx.predecessor)) = .ok) :
    text232 h (regOf s (.ofNear ctx.predecessor)) (WNear.Borsh.u64 s.accountStorageUsage) =
      (s!"Deposit {amountOf ctx.attached (modelReg s (.ofNear ctx.predecessor)) s.storageMin} NEAR to {WNear.AccountId.ofNear ctx.predecessor}").toUTF8.toList := by
  have hp : h.context.predecessorAccountId = ctx.predecessor.bytes :=
    eraseP_field he (fun x => x.context.predecessorAccountId) fun _ => rfl
  rw [text232_amount, amount232_model ctx raw s hwf hs h he hok, hp]
  exact NearDepositLog.logW_model _ (.ofNear ctx.predecessor)

/-- Both checked additions fit on the successful branch. -/
theorem dcase_ok_bounds (dep : Nat) (reg : Option Nat) (min supply : Nat)
    (hc : dcase dep reg min supply = .ok) :
    reg.getD 0 + amountOf dep reg min < 2 ^ 128 ∧ supply + amountOf dep reg min < 2 ^ 128 := by
  unfold dcase at hc
  split at hc
  · cases hc
  · split at hc
    · cases hc
    · split at hc
      · cases hc
      · split at hc
        · cases hc
        · constructor <;> omega

/-- Serializing the two words of a bounded value gives its model Borsh encoding. -/
theorem u128Of_borsh (n : Nat) (hn : n < 2 ^ 128) :
    StorageBalanceBounds.u128Of n = WNear.Borsh.u128 n := by
  have hw := StorageBalanceBounds.u128Bytes_eq_u128Of (balanceWords n).1 (balanceWords n).2 n
    (balanceWords_val n hn)
  exact hw.symm.trans (DepositBody234.sb_u128 n).symm

/-- The account record is the previous balance plus the minted amount. -/
theorem nv232_amount (h : NearState) (reg : Option (UInt64 × UInt64)) (xb : List UInt8) :
    nv232 h reg xb = StorageBalanceBounds.u128Of ((regB reg).getD 0 + amount232 h reg xb) := by
  cases reg with
  | none =>
    simp only [nv232, regB, Option.map_none, Option.getD_none, amount232, Nat.mul_zero, Nat.zero_add]
  | some p =>
    rcases p with ⟨lo, hi⟩
    simp only [nv232, regB, Option.map_some, Option.getD_some, amount232]

/-- On success, the balance bytes written by the binary encode the model's new balance. -/
theorem nv232_model (ctx : Context) (raw : RawStorage) (s : WNear.State)
    (hwf : ctx.WF raw) (hs : s.WF) (h : NearState)
    (he : eraseP h = eraseP (hostOf ctx raw))
    (hok : caseDep h s (regOf s (.ofNear ctx.predecessor)) = .ok) :
    nv232 h (regOf s (.ofNear ctx.predecessor)) (WNear.Borsh.u64 s.accountStorageUsage) =
      WNear.Borsh.u128 ((modelReg s (.ofNear ctx.predecessor)).getD 0 +
        amountOf ctx.attached (modelReg s (.ofNear ctx.predecessor)) s.storageMin) := by
  have hc := (caseDep_eq_model ctx raw s hwf hs h he).symm.trans hok
  have hb := (dcase_ok_bounds _ _ _ _ hc).1
  rw [nv232_amount, amount232_model ctx raw s hwf hs h he hok, regB_regOf s _ hs]
  exact u128Of_borsh _ hb

end WNear.Binary.NearDepositMethod
