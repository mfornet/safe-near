import NearLogic.Hosts.RelaxFns

/-!
# The panics under raised gas limits

`panic` and `panic_utf8` always trap, with a message read from memory that
does not depend on the gas limits.
-/

namespace NearLogic

open Wasm Wasm.Near

theorem panicUtf8Read_relax (st : HostStore NearState) (len ptr : UInt64) (p m : Nat) :
    panicUtf8Read (relaxSt st p m) len ptr = panicUtf8Read st len ptr := by
  simp only [panicUtf8Read, readUtf8String, scanNulBytes_relax]
  rfl

theorem panicMetered_relax (st : HostStore NearState) (args : List Value) (p m : Nat) :
    panicMetered.invoke (relaxSt st p m) args = (panicMetered.invoke st args).relax p m := rfl

theorem panicUtf8Metered_relax (st : HostStore NearState) (args : List Value) (p m : Nat) :
    panicUtf8Metered.invoke (relaxSt st p m) args = (panicUtf8Metered.invoke st args).relax p m := by
  simp only [panicUtf8Metered]
  split
  · rw [panicUtf8Read_relax]
    split <;> rfl
  · rfl

theorem relaxFn_panic (extra : Nat) : RelaxFn (metered extra "panic" panicMetered).toHostFn :=
  relaxFn_plain extra (by simp [gasNames]) panicMetered (by decide) panicMetered_relax
    (fun st args vals st2 h => by simp [panicMetered, trapWith] at h)

theorem relaxFn_panicUtf8 (extra : Nat) : RelaxFn (metered extra "panic_utf8" panicUtf8Metered).toHostFn :=
  relaxFn_plain extra (by simp [gasNames]) panicUtf8Metered (by decide) panicUtf8Metered_relax
    (fun st args vals st2 h => by
      simp only [panicUtf8Metered] at h
      split at h
      · split at h <;> simp [trapWith] at h
      · simp [trapWith] at h)

end NearLogic
