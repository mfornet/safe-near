import NearLogic.Hosts.HostFnsRelax

/-!
# Functional storage host functions under raised gas limits

`storage_read`, `storage_write`, `storage_remove` and `storage_has_key` commute
with raising the gas limits and keep them.
-/

namespace NearLogic

open Wasm Wasm.Near

@[simp] theorem relaxSt_storage (st : HostStore NearState) (p m : Nat) :
    (relaxSt st p m).host.storage = st.host.storage := rfl

theorem checkDataLimit_relax (name label : String) (limit : Option Nat) (n : Nat)
    (st : HostStore NearState) (next next' : Unit → HostResult NearState)
    (error : Option (Nat → Nat → HostError)) (p m : Nat)
    (hn : next' () = (next ()).relax p m) :
    checkDataLimit name label limit n (relaxSt st p m) next' error =
      (checkDataLimit name label limit n st next error).relax p m := by
  unfold checkDataLimit
  by_cases h : withinLimit limit n = true
  · simp only [h, ↓reduceIte]; exact hn
  · simp only [h, ↓reduceIte]
    cases error <;> rfl

theorem checkDataLimit_keep (name label : String) (limit : Option Nat) (n : Nat)
    (st : HostStore NearState) (next : Unit → HostResult NearState)
    (error : Option (Nat → Nat → HostError)) (h : KeepsLimits st (next ())) :
    KeepsLimits st (checkDataLimit name label limit n st next error) := by
  unfold checkDataLimit
  split
  · exact h
  · split <;> exact KeepsLimits.trap _ _ _

theorem checkedSetRegister?_gas (st st' : HostStore NearState) (r : UInt64) (d : List UInt8)
    (h : checkedSetRegister? st r d = some st') :
    st'.host.gas.prepaid = st.host.gas.prepaid ∧ st'.host.gas.maxBurnt = st.host.gas.maxBurnt := by
  unfold checkedSetRegister? at h
  split at h
  · cases h; exact ⟨rfl, rfl⟩
  · split at h
    · cases h; exact ⟨rfl, rfl⟩
    · cases h

theorem checkedSetRegister?_some_relax (st st' : HostStore NearState) (r : UInt64) (d : List UInt8) (p m : Nat)
    (h : checkedSetRegister? st r d = some st') :
    checkedSetRegister? (relaxSt st p m) r d = some (relaxSt st' p m) := by
  rw [checkedSetRegister?_relax, h]; rfl

theorem checkedSetRegister?_none_relax (st : HostStore NearState) (r : UInt64) (d : List UInt8) (p m : Nat)
    (h : checkedSetRegister? st r d = none) :
    checkedSetRegister? (relaxSt st p m) r d = none := by
  rw [checkedSetRegister?_relax, h]; rfl

macro "srsplit" : tactic =>
  `(tactic| (repeat' (first
      | (simp only [getMemOrReg_relaxSt, config_relaxSt, relaxSt_storage, checkedSetRegister?_relax])
      | (have h2 := ‹checkedSetRegister? _ _ _ = some _›
         simp only [h2, Option.map_some, Option.some.injEq] at *
         subst_vars)
      | (have h2 := ‹checkedSetRegister? _ _ _ = none›
         simp only [h2, Option.map_none] at *)
      | rfl
      | contradiction
      | (exact writeRegisterResult_relax ..)
      | (refine checkDataLimit_relax _ _ _ _ _ _ _ _ _ _ ?_)
      | split
      | (simp only [*, ↓reduceIte, if_true, if_false]))))

macro "sksplit" : tactic =>
  `(tactic| (repeat' (first
      | (exact KeepsLimits.trap _ _ _)
      | (exact KeepsLimits.ret _ _ _ rfl rfl)
      | (obtain ⟨h1, h2⟩ := checkedSetRegister?_gas _ _ _ _ ‹checkedSetRegister? _ _ _ = some _›
         exact KeepsLimits.ret _ _ _ h1 h2)
      | (exact writeRegisterResult_keep _ _ _ _ _)
      | (refine checkDataLimit_keep _ _ _ _ _ _ _ ?_)
      | split)))

theorem storageReadFn_relax : RelaxComm storageReadFn := by
  intro st args p m
  unfold storageReadFn
  dsimp only
  srsplit

theorem storageReadFn_keep : KeepGas storageReadFn := by
  refine KeepGas.of_keepsLimits ?_
  intro st args
  unfold storageReadFn
  dsimp only
  sksplit

theorem storageHasKeyFn_relax : RelaxComm storageHasKeyFn := by
  intro st args p m
  unfold storageHasKeyFn
  dsimp only
  srsplit

theorem storageHasKeyFn_keep : KeepGas storageHasKeyFn := by
  refine KeepGas.of_keepsLimits ?_
  intro st args
  unfold storageHasKeyFn
  dsimp only
  sksplit

theorem storageRemoveFn_relax : RelaxComm storageRemoveFn := by
  unfold storageRemoveFn
  refine disallowInView_relax _ _ ?_
  intro st args p m
  dsimp only
  srsplit

theorem storageRemoveFn_keep : KeepGas storageRemoveFn := by
  unfold storageRemoveFn
  refine disallowInView_keep _ _ (KeepGas.of_keepsLimits ?_)
  intro st args
  dsimp only
  sksplit

theorem storageWriteFn_relax : RelaxComm storageWriteFn := by
  unfold storageWriteFn
  refine disallowInView_relax _ _ ?_
  intro st args p m
  dsimp only
  srsplit

theorem storageWriteFn_keep : KeepGas storageWriteFn := by
  unfold storageWriteFn
  refine disallowInView_keep _ _ (KeepGas.of_keepsLimits ?_)
  intro st args
  dsimp only
  sksplit

end NearLogic
