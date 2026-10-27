import Proofs.InterfaceSetCore

/-! The actual post-lookup setter core restores the outer shadow-stack global. -/
namespace WNear.Proofs.InterfaceSetCoreFinalState
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.StorePairCaller (paid)
open InterfaceSetState
set_option maxRecDepth 16384

private theorem paid_globals (s : Store NearState) (op n : Nat) : (paid s op n).globals = s.globals := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih
private theorem charge_globals (s : Store NearState) (cost : Nat) : (chargedStore s cost).globals = s.globals := rfl

private theorem acquired_globals (s : Store NearState) (op : Nat) (p : Layout) (memory : Memory)
    (hg : s.globals[p.globalIndex]? = some {p.global with value := .i32 (scratch p)}) :
    (InterfaceSetCore.acquired s op p memory).globals = s.globals := by
  have ha : (InterfaceSetCore.arguments s op).globals[p.globalIndex]? = some {p.global with value := .i32 (scratch p)} := by
    rw [InterfaceSetCore.arguments, paid_globals, paid_globals]; exact hg
  have he := InterfaceSetPhases.calledAcquireStore_globals (InterfaceSetCore.arguments s op) op p.globalIndex p.memoryIndex
    (scratch p) (scratch p + 8) 1074904 memory {p.global with value := .i32 (scratch p)} ha rfl
  rw [InterfaceSetCore.acquired, he, InterfaceSetCore.arguments, paid_globals, paid_globals]

private theorem installed_globals (s : Store NearState) (op : Nat) (p : Layout) (memory : Memory)
    (hg : s.globals[p.globalIndex]? = some {p.global with value := .i32 (scratch p)}) :
    (InterfaceSetCore.installed s op p memory).globals = s.globals := by
  rw [InterfaceSetCore.installed, InterfaceSetTail.installed, InterfaceSetPhases.installTail_globals]
  exact acquired_globals s op p memory hg

private theorem release_globals (s : Store NearState) (op index : Nat) (counter : UInt32) (memory : Memory) :
    (InterfaceBorrow.calledReleaseStore s op index counter memory).globals = s.globals := by
  have hr := InterfaceBorrow.releasedStore_resources (InterfaceBorrow.releaseEntryStore s op) op index counter memory
  have hg := congrArg (fun t : Store NearState => t.globals) hr
  simpa only [InterfaceBorrow.calledReleaseStore, InterfaceBorrow.releaseEntryStore, chargedStore] using hg

private theorem check_globals (s : Store NearState) (op index : Nat) (sp : UInt32) (global : GlobalInst)
    (hg : s.globals[index]? = some global) (hv : global.value = .i32 sp) :
    (ValueReturnOuter.checkAfter s op index sp).globals = s.globals := by
  have he : (ValueReturnOuter.nonnullEntry s op).globals = s.globals := by
    rw [ValueReturnOuter.nonnullEntry, charge_globals, charge_globals]
  have hg' : (ValueReturnOuter.nonnullEntry s op).globals[index]? = some global := by rw [he]; exact hg
  have hc := ValueReturnBorrow.checkedStore_globals (ValueReturnOuter.nonnullEntry s op) op index sp global hg' hv
  rw [ValueReturnOuter.checkAfter, hc, he]

/-- All internal stack reservations are restored; only the final outer restore
changes the incoming global array, to the exact wrapping scratch+32 value. -/
theorem after_globals (s : Store NearState) (op : Nat) (p : Layout) (memory : Memory)
    (hg : s.globals[p.globalIndex]? = some {p.global with value := .i32 (scratch p)}) :
    (InterfaceSetCore.after s op p memory).globals =
      (setGlobal s p.globalIndex (.i32 (scratch p + 32))).globals := by
  let i := InterfaceSetCore.installed s op p memory
  let r := InterfaceBorrow.calledReleaseStore (paid i op 5) op p.memoryIndex
    (InterfaceSetCore.counter p memory) (InterfaceSetCore.installedMemory p memory)
  let b := chargedStore (paid r op 2) op
  let a := paid b op 1
  have hi : i.globals = s.globals := installed_globals s op p memory hg
  have hr : r.globals = i.globals := by
    dsimp only [r]
    rw [release_globals, paid_globals]
  have hb : b.globals = s.globals := by
    dsimp only [b]
    rw [charge_globals, paid_globals, hr, hi]
  have ha : a.globals = s.globals := by
    dsimp only [a]
    rw [paid_globals, hb]
  have hga : a.globals[p.globalIndex]? = some {p.global with value := .i32 (scratch p)} := by rw [ha]; exact hg
  have hc := (check_globals a op p.globalIndex (scratch p) {p.global with value := .i32 (scratch p)} hga rfl).trans ha
  have hm := congrArg (fun arr => arr.modify p.globalIndex (fun g => {g with value := .i32 (scratch p + 32)})) hc
  simpa only [InterfaceSetCore.after, InterfaceSetTail.after, InterfaceSetReleaseTail.after,
    InterfaceSetReleaseTail.epilogueAfter, InterfaceSetReleaseTail.released, InterfaceSetCore.installed,
    a, b, r, i, setGlobal, paid_globals] using hm

/-- The actual original global instance is recovered, including type and mutability. -/
theorem after_global (s : Store NearState) (op : Nat) (p : Layout) (memory : Memory)
    (hg : s.globals[p.globalIndex]? = some {p.global with value := .i32 (scratch p)})
    (hv : p.global.value = .i32 p.sp) :
    (InterfaceSetCore.after s op p memory).globals[p.globalIndex]? = some p.global := by
  rw [after_globals s op p memory hg]
  have hc : scratch p + 32 = p.sp := UInt32.sub_add_cancel p.sp 32
  have he : ({p.global with value := .i32 (scratch p + 32)} : GlobalInst) = p.global := by
    rw [hc, ← hv]
  simp [setGlobal, Array.getElem?_modify, hg, he]

end WNear.Proofs.InterfaceSetCoreFinalState
