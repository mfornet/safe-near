import Proofs.AllocateFlaggedControl

/-! Complete actual heap-write, branch and commit suffix of the direct split. -/
namespace WNear.Proofs.AllocateFlagged
open Wasm Wasm.Near MeteredLogic
open AllocateSearch (Layout)
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16784
set_option maxHeartbeats 900000
attribute [local irreducible] WP atCode readI32 writeI32

def mutateInitialized (s : Store NearState) (op : Nat) (p : Layout) :=
  Allocate.initializedStore s op p.memoryIndex p.memory (head p) (header p)
def mutateAfter (s : Store NearState) (op : Nat) (p : Layout) :=
  Allocate.committed (controlAfter (mutateInitialized s op p) op p) op p.memoryIndex (flaggedMemory p) (header p)
def mutateFrame (frame : CallFrame) (p : Layout) := Allocate.resultFrame (controlFrame frame p) (header p)

/-- All actual79 heap-write/commit opcodes and the thirteen-label exit. The
original heap Native predicate supplies every computed memory/read condition. -/
theorem wp_mutate (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (skipped : List Label) (code discarded : Expr) (p : Layout) (post : Post)
    (hskip : skipped.length = 12) (hn : Native p)
    (hh : frame.locals[1]? = some (.i32 (head p))) (ha : frame.locals[9]? = some (.i32 (header p)))
    (hs : 11 ≤ frame.locals.size) (hm : s.modules[frame.inst]? = some p.mi)
    (hi : p.mi.memAddrs[0]? = some p.memoryIndex) (hmem : s.mems[p.memoryIndex]? = some p.memory)
    (hc : s.host.gas.Credits (79*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (mutateAfter s cfg.regularOpCost p) limits stack (mutateFrame frame p) callers code)) rest post) :
    WP cfg (fuel+80) (.next (atCode s limits stack
      (labelPrefixFrame frame stack.size skipped (WNear.Binary.Allocate.commit++code)) callers
      (WNear.Binary.Allocate.initializeSplit++WNear.Binary.AllocateSearch.linkCode++WNear.Binary.AllocateFlagged.transfer++discarded)))
      (79*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  let initialized := mutateInitialized s op p
  let controlled := controlAfter initialized op p
  let committedFrame := controlFrame frame p
  have intervals := intervals p hn
  have ms := flagged_shape p hn
  have cclear : (Allocate.clearedStore s op p.memoryIndex p.memory (header p)).host.gas.Credits (6*op+(67*op+rest)) :=
    Allocate.clearedStore_credits s op p.memoryIndex _ p.memory (header p) (hc.mono (by dsimp [op]; omega))
  have ci : initialized.host.gas.Credits (67*op+rest) := by
    dsimp only [initialized,mutateInitialized,Allocate.initializedStore,Allocate.copiedEndStore]
    rw [storeI32_host]
    exact paid_credits (Allocate.clearedStore s op p.memoryIndex p.memory (header p)) op 6 _ cclear
  have cc : controlled.host.gas.Credits (10*op+rest) :=
    controlAfter_credits initialized op (10*op+rest) p (ci.mono (by omega))
  have mclear := Allocate.clearedStore_memory s op p.memoryIndex p.memory (header p) hmem
  have mclear6 : (paid (Allocate.clearedStore s op p.memoryIndex p.memory (header p)) op 6).mems[p.memoryIndex]? =
      some (Allocate.clearedMemory p.memory (header p)) := by simpa only [paid,chargedStore] using mclear
  have mi : initialized.mems[p.memoryIndex]? = some (initializedMemory p) := by
    exact storeI32_memory _ p.memoryIndex (header p).toNat (Allocate.clearedMemory p.memory (header p))
      (readI32 (Allocate.clearedMemory p.memory (header p)) (head p).toNat &&& 4294967292) mclear6
  have mc : controlled.mems[p.memoryIndex]? = some (flaggedMemory p) := controlAfter_memory initialized op p mi
  have hmI : initialized.modules[frame.inst]? = some p.mi := by
    simpa only [initialized,mutateInitialized,Allocate.initializedStore,Allocate.copiedEndStore,Allocate.clearedStore,
      paid,chargedStore,storeI32_modules,storeI64_modules] using hm
  have fields := controlAfter_fields initialized op p
  have hmC : controlled.modules[committedFrame.inst]? = some p.mi := by rw [fields.2.1]; exact hmI
  have h9 : committedFrame.locals[9]? = some (.i32 (header p)) := by
    simp [committedFrame,controlFrame,backlinkFrame,endReadFrame,AllocateSearch.endSelectedFrame,ha]
  have commitNext : WP cfg fuel (.next (atCode (Allocate.committed controlled op p.memoryIndex (flaggedMemory p) (header p))
      limits stack (Allocate.resultFrame committedFrame (header p)) callers code)) rest post := by
    simpa only [controlled,initialized,mutateAfter,mutateFrame,committedFrame,op] using hnext
  have commit := Allocate.wp_commit cfg fuel rest controlled limits stack committedFrame callers code (header p) p.mi
    p.memoryIndex (flaggedMemory p) post h9 hmC hi mc (by rw [ms.size]; omega) cc commitNext
  have controlledNext : WP cfg (fuel+10) (.next (atCode controlled limits stack (controlFrame frame p) callers
      (WNear.Binary.Allocate.commit++code))) (10*op+rest) post := commit
  have control := wp_link_control cfg (fuel+10) (10*op+rest) initialized limits stack frame callers skipped
    (WNear.Binary.Allocate.commit++code) discarded p post hskip hn hh ha hs hmI hi mi
    (ci.mono (by dsimp [op]; omega)) controlledNext
  have initNext : WP cfg (fuel+68) (.next (atCode initialized limits stack
      (labelPrefixFrame frame stack.size skipped (WNear.Binary.Allocate.commit++code)) callers
      (WNear.Binary.AllocateSearch.linkCode++WNear.Binary.AllocateFlagged.transfer++discarded))) (67*op+rest) post := by
    have cost : 57*cfg.regularOpCost+(10*op+rest)=67*op+rest := by dsimp [op]; omega
    rw [cost] at control
    simpa only [Nat.add_assoc,Nat.reduceAdd] using control
  have init := Allocate.wp_initialize_split cfg (fuel+68) (67*op+rest) s limits stack
    (labelPrefixFrame frame stack.size skipped (WNear.Binary.Allocate.commit++code)) callers
    (WNear.Binary.AllocateSearch.linkCode++WNear.Binary.AllocateFlagged.transfer++discarded) (head p) (header p) p.mi p.memoryIndex p.memory post
    ha hh hm hi hmem hn.memoryWf (by omega) (by omega) (hc.mono (by dsimp [op]; omega)) initNext
  have cost : 12*cfg.regularOpCost+(67*op+rest)=79*cfg.regularOpCost+rest := by dsimp [op]; omega
  rw [cost] at init
  simpa only [Nat.add_assoc,Nat.reduceAdd,List.append_assoc] using init
end WNear.Proofs.AllocateFlagged
