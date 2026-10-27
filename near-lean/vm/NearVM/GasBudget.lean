import NearVM.GasCredits

/-!
# Comparing metering budgets

The first component of the low-budget simulation: every successful charge
under smaller metering limits succeeds with the same accounting under larger
limits. Guest-visible `prepaid_gas` lives separately in `NearContext`; a
machine simulation must keep that context fixed even when relaxing these
internal counter limits. This file does not assert that arbitrary host
functions are insensitive to either limit.
-/
namespace Wasm.Near.GasCounter

/-- Equal accounting with possibly smaller prepaid and burn limits. -/
structure Below (small large : GasCounter) : Prop where
  burnt : small.burnt = large.burnt
  promises : small.promises = large.promises
  prepaid : small.prepaid ≤ large.prepaid
  limit : small.maxBurnt ≤ large.maxBurnt

/-- A successful charge can be replayed at larger metering limits. Promise
reservations are included; no ordering assumption on `burn` and `use` is needed. -/
theorem Below.deduct {small large : GasCounter} (h : Below small large)
    (burn use : Nat) (hok : (small.deduct burn use).2 = none) :
    (large.deduct burn use).2 = none ∧
      Below (small.deduct burn use).1 (large.deduct burn use).1 := by
  have hs : small.burnt + burn ≤ small.maxBurnt ∧
      small.burnt + burn + (small.promises + (use - burn)) ≤ small.prepaid := by
    unfold GasCounter.deduct at hok
    dsimp only at hok
    split at hok
    · assumption
    · contradiction
  have hl : large.burnt + burn ≤ large.maxBurnt ∧
      large.burnt + burn + (large.promises + (use - burn)) ≤ large.prepaid := by
    obtain ⟨hb, hp, hpre, hlim⟩ := h
    constructor <;> omega
  simp only [GasCounter.deduct, ite_eq_left hs, ite_eq_left hl]
  exact ⟨True.intro, ⟨by simpa using congrArg (· + burn) h.burnt,
    by simpa using congrArg (· + (use - burn)) h.promises, h.prepaid, h.limit⟩⟩

theorem Below.burn {small large : GasCounter} (h : Below small large)
    (cost : Nat) (hok : (small.burn cost).2 = none) :
    (large.burn cost).2 = none ∧ Below (small.burn cost).1 (large.burn cost).1 :=
  h.deduct cost cost hok

theorem Below.prepay {small large : GasCounter} (h : Below small large)
    (cost : Nat) (hok : (small.prepay cost).2 = none) :
    (large.prepay cost).2 = none ∧ Below (small.prepay cost).1 (large.prepay cost).1 :=
  h.deduct 0 cost hok

/-- Relaxing the metering limits leaves the accounting untouched. This
constructor deliberately says nothing about guest-visible call context. -/
theorem below_withLimits (g : GasCounter) (prepaid burnLimit : Nat)
    (hp : g.prepaid ≤ prepaid) (hb : g.maxBurnt ≤ burnLimit) :
    Below g { g with prepaid := prepaid, maxBurnt := burnLimit } :=
  ⟨rfl, rfl, hp, hb⟩

/-- The charge where replay stops is a protocol gas failure, never an
interpreter error or some other host error. -/
theorem deduct_error_is_gas (g : GasCounter) (burn use : Nat) {error : HostError}
    (h : (g.deduct burn use).2 = some error) :
    error = .gasLimitExceeded ∨ error = .gasExceeded := by
  unfold GasCounter.deduct at h
  dsimp only at h
  split at h
  · contradiction
  · split at h <;> simp_all

end Wasm.Near.GasCounter
