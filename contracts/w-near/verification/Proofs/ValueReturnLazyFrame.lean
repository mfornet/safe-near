import Proofs.ValueReturnLazyLookup
import Proofs.InterfaceLazyLayout

/-! Concrete post-memory and restored state fields for the real lazy lookup. -/
namespace WNear.Proofs.ValueReturnLazyLookup
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.StorePairCaller (paid)
open InterfaceLazyComplete (Layout)
set_option maxRecDepth 16384
set_option maxHeartbeats 300000

private theorem paid_globals (s : Store NearState) (op n : Nat) : (paid s op n).globals = s.globals := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

private theorem tail_globals (s : Store NearState) (op : Nat) (p : InterfaceLazyState.Layout) :
    (InterfaceLazyTail.after s op p).globals = (setGlobal s p.globalIndex (.i32 (p.scratch + 48))).globals := by
  simp only [InterfaceLazyTail.after, InterfaceLazyTail.wordAfter, InterfaceLazyTail.statusAfter,
    InterfaceLazySavedTail.after, InterfaceLazyState.finalStore, InterfaceLazyFinish.finalStore,
    InterfaceLazyState.saved, InterfaceLazySaved.savedStore, InterfaceLazySaved.savedHigh,
    InterfaceLazySaved.savedLow, InterfaceLazyState.status, InterfaceLazyState.word, InterfaceLazyState.high,
    InterfaceLazyBody.exchanged64, InterfaceLazyBody.exchanged32, InterfaceLazyBody.replacedStatus,
    InterfaceSetBody.storeWord, paid_globals, storeI32_globals, storeI64_globals, setGlobal]

/-- The lazy body restores every global after using its wrapping reserve48. -/
theorem complete_globals (s : Store NearState) (op : Nat) (p : Layout)
    (hg : s.globals[p.globalIndex]? = some p.global) (hsp : p.global.value = .i32 p.sp) :
    (InterfaceLazyComplete.after s op p).globals = s.globals := by
  have initFields := InterfaceLazyPrefix.after_resources (InterfaceLazyComplete.reserved s op p) op p.memoryIndex
    (InterfaceLazyComplete.scratch p) p.memory
  have initGlobals := congrArg (fun t => t.globals) initFields
  simp only at initGlobals
  have result := tail_globals (InterfaceLazyComplete.initialized s op p) op (InterfaceLazyComplete.tailLayout p)
  have restore := StorePairCaller.setGlobal_restore s p.globalIndex (.i32 (InterfaceLazyComplete.scratch p)) p.global hg
  simp only [InterfaceLazyComplete.after]
  rw [result]
  simp only [InterfaceLazyComplete.tailLayout, InterfaceLazyComplete.scratch, UInt32.sub_add_cancel, setGlobal]
  have initializedGlobals : (InterfaceLazyComplete.initialized s op p).globals = (InterfaceLazyComplete.reserved s op p).globals := by
    simpa only [InterfaceLazyComplete.initialized] using initGlobals
  rw [initializedGlobals]
  simpa only [InterfaceLazyComplete.reserved, paid_globals, setGlobal, hsp] using restore

/-- Functions, tables and module instances are untouched by initialization. -/
theorem complete_fields (s : Store NearState) (op : Nat) (p : Layout) :
    (InterfaceLazyComplete.after s op p).funcs = s.funcs ∧
    (InterfaceLazyComplete.after s op p).tables = s.tables ∧
    (InterfaceLazyComplete.after s op p).modules = s.modules := by
  simp only [InterfaceLazyComplete.after, InterfaceLazyComplete.initialized, InterfaceLazyComplete.reserved,
    InterfaceLazyPrefix.after, InterfaceInitialize.after, InterfaceInitialize.bodyAfter, InterfaceInitialize.entry,
    InterfaceLazyTail.after, InterfaceLazyTail.wordAfter, InterfaceLazyTail.statusAfter,
    InterfaceLazySavedTail.after, InterfaceLazyState.finalStore, InterfaceLazyFinish.finalStore,
    InterfaceLazyState.saved, InterfaceLazySaved.savedStore, InterfaceLazySaved.savedHigh,
    InterfaceLazySaved.savedLow, InterfaceLazyState.status, InterfaceLazyState.word, InterfaceLazyState.high,
    InterfaceLazyBody.exchanged64, InterfaceLazyBody.exchanged32, InterfaceLazyBody.replacedStatus,
    InterfaceSetBody.storeWord, paid, chargedStore, storeI32, storeI64, setGlobal, and_self]

/-- Exact alias-aware sequential memory produced by the actual indirect chain. -/
theorem indirectAfter_memory (s : Store NearState) (op : Nat) (p : Layout)
    (hm : s.mems[p.memoryIndex]? = some p.memory) :
    (indirectAfter s op p).mems[p.memoryIndex]? = some (InterfaceLazyLayout.finalMemory p) := by
  let active := InterfaceLazyCall.entered (paid (entered (paid (indirectEntered s op) op 2) op) op 7) op
  have hmem : active.mems[p.memoryIndex]? = some p.memory := by
    simpa only [active, InterfaceLazyCall.entered, entered, indirectEntered, paid, chargedStore] using hm
  have result := InterfaceLazyLayout.after_memory active op p hmem
  simpa only [indirectAfter, lookupAfter, callAfter, bodyAfter, InterfaceLazyCall.after, active, chargedStore] using result

theorem indirectAfter_globals (s : Store NearState) (op : Nat) (p : Layout)
    (hg : s.globals[p.globalIndex]? = some p.global) (hsp : p.global.value = .i32 p.sp) :
    (indirectAfter s op p).globals = s.globals := by
  let active := InterfaceLazyCall.entered (paid (entered (paid (indirectEntered s op) op 2) op) op 7) op
  have global : active.globals[p.globalIndex]? = some p.global := by
    simpa only [active, InterfaceLazyCall.entered, entered, indirectEntered, paid, chargedStore] using hg
  have result := complete_globals active op p global hsp
  simpa only [indirectAfter, lookupAfter, callAfter, bodyAfter, InterfaceLazyCall.after, active,
    InterfaceLazyCall.entered, entered, indirectEntered, paid_globals, chargedStore] using result

theorem indirectAfter_fields (s : Store NearState) (op : Nat) (p : Layout) :
    (indirectAfter s op p).funcs = s.funcs ∧ (indirectAfter s op p).tables = s.tables ∧ (indirectAfter s op p).modules = s.modules := by
  let active := InterfaceLazyCall.entered (paid (entered (paid (indirectEntered s op) op 2) op) op 7) op
  have result := complete_fields active op p
  simpa only [indirectAfter, lookupAfter, callAfter, bodyAfter, InterfaceLazyCall.after, active,
    InterfaceLazyCall.entered, entered, indirectEntered, paid, chargedStore] using result

end WNear.Proofs.ValueReturnLazyLookup
