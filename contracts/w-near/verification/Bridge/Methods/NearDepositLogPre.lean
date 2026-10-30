import Bridge.Methods.NearDepositContext
import Bridge.Functions.DepositTail

/-!
# The initialized deposit's log is valid and fits

Discharge `DepOk.log`: every `u128` amount and typed predecessor give an ASCII message of
at most 120 bytes. Protocol 86's existing bounds cover it once the log count permits one entry.
-/

namespace WNear.Binary.NearDepositMethod

open Wasm Wasm.Near NearLogic NearInterface

private theorem digit_ascii (n : Nat) (hn : n < 10) : (FmtDigits.digit n).toNat < 128 := by
  simp only [FmtDigits.digit, UInt8.toNat_ofNat']
  rw [Nat.mod_eq_of_lt (show 48 + n < 256 by omega)]
  omega

/-- Every byte emitted by the amount formatter is an ASCII digit. -/
theorem decDigits_ascii (n : Nat) : ∀ b ∈ FmtDigits.decDigits n, b.toNat < 128 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [FmtDigits.decDigits]
    split
    · rename_i hn
      intro b hb
      simp only [List.mem_singleton] at hb
      subst b
      exact digit_ascii _ hn
    · rename_i hn
      intro b hb
      rcases List.mem_append.mp hb with hb | hb
      · exact ih (n / 10) (by omega) b hb
      · simp only [List.mem_singleton] at hb
        subst b
        exact digit_ascii _ (Nat.mod_lt _ (by decide))

private theorem pDeposit_ascii : ∀ b ∈ DepositLog.pDeposit, b.toNat < 128 := by decide
private theorem pNear_ascii : ∀ b ∈ DepositLog.pNear, b.toNat < 128 := by decide

/-- Both fixed pieces, the digits, and the account bytes are ASCII. -/
theorem deposit_log_ascii (lo hi : UInt64) (ab : List UInt8)
    (ha : ∀ b ∈ ab, b.toNat < 128) : ∀ b ∈ DepositTail.logText lo hi ab, b.toNat < 128 := by
  intro b hb
  simp only [DepositTail.logText, DepositLog.logW, List.mem_append] at hb
  rcases hb with ((hb | hb) | hb) | hb
  · exact pDeposit_ascii b hb
  · exact decDigits_ascii _ b hb
  · exact pNear_ascii b hb
  · exact ha b hb

private theorem validUtf8_of_ascii (bs : List UInt8) (ha : ∀ b ∈ bs, b.toNat < 128) :
    validUtf8 bs = true := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    rw [validUtf8.eq_def]
    dsimp only
    rw [if_pos (ha b (by simp))]
    exact ih (fun x hx => ha x (List.mem_cons_of_mem b hx))

/-- An amount takes at most 39 digits; the account ID at most 64 bytes. -/
theorem deposit_log_length (lo hi : UInt64) (ab : List UInt8) (ha : ab.length ≤ 64) :
    0 < (DepositTail.logText lo hi ab).length ∧ (DepositTail.logText lo hi ab).length ≤ 120 := by
  have hl : lo.toNat < 2 ^ 64 := lo.toNat_lt
  have hh : hi.toNat < 2 ^ 64 := hi.toNat_lt
  have hv : FmtU128.val lo hi < 2 ^ 128 := by unfold FmtU128.val; omega
  have h39 : 2 ^ 128 ≤ 10 ^ 39 := by decide
  have hd := FmtDigits.decDigits_length_le 39 (FmtU128.val lo hi) (by decide) (by omega)
  have hw := DepositLog.logW_length (FmtDigits.decDigits (FmtU128.val lo hi)) ab 4
  constructor
  · simp [DepositTail.logText, DepositLog.logW, DepositLog.pDeposit, DepositLog.pNear]
  · change (DepositLog.logW _ ab 4).length ≤ 120
    omega

/-- The deposit log's full host-call precondition, for every amount. -/
theorem deposit_log_ok (ctx : Context) (raw : RawStorage) (h : NearState)
    (he : eraseP h = eraseP (hostOf ctx raw)) (hl : FtTotalSupplyMethod.LimitsV86 ctx.protocol)
    (hc : FtTotalSupplyMethod.CostsV86 ctx.protocol) (hn : 1 ≤ ctx.protocol.wasm.limits.maxNumberLogs)
    (lo hi : UInt64) :
    LogStr.LogOk h (DepositTail.logText lo hi h.context.predecessorAccountId)
      (DepositTail.logText lo hi h.context.predecessorAccountId).length := by
  have hp := predecessor_properties_of_eraseP ctx raw h he
  have ha := predecessor_ascii_of_eraseP ctx raw h he
  obtain ⟨hpos, hlen⟩ := deposit_log_length lo hi _ hp.2.1
  have hbound : (DepositTail.logText lo hi h.context.predecessorAccountId).length ≤ 16384 := by omega
  refine ⟨rfl, hpos, ?_, initial_log_room ctx raw h he hn,
    initial_log_fits ctx raw h he hl _ hbound, log_read_cost_fits ctx raw h he hc _ hbound⟩
  exact validUtf8_of_ascii _ (deposit_log_ascii lo hi _ ha)

end WNear.Binary.NearDepositMethod
