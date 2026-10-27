import Proofs.AllocateControlBacklink
import Proofs.AllocateControlLinks
import Proofs.AllocateControlExit

/-! Actual full link mutation/control phase of the direct end-split branch. -/
namespace WNear.Proofs.AllocateSearch
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
set_option maxHeartbeats 900000
attribute [local irreducible] WP atCode readI32 writeI32

def afterBacklink (s : Store NearState) (op : Nat) (p : Layout) :=
  backlinkStore s op p.memoryIndex (initializedMemory p) (finish p) (header p)
def controlAfter (s : Store NearState) (op : Nat) (p : Layout) := paid (linkedStore (afterBacklink s op p) op p) op 5
def controlFrame (frame : CallFrame) (p : Layout) :=
  {backlinkFrame frame (finish p) with locals:=(backlinkFrame frame (finish p)).locals.set! 2 (.i32 (header p))}

/-- All actual backlink tests and pointer writes, followed by the true branch12
through the real label stack. Every heap condition follows from original Native. -/
theorem wp_link_control (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (skipped : List Label) (code discarded : Expr) (p : Layout) (post : Post)
    (hskip : skipped.length = 12) (hn : Native p)
    (hhead : frame.locals[1]? = some (.i32 (head p))) (hheader : frame.locals[9]? = some (.i32 (header p)))
    (hs : 11 ≤ frame.locals.size) (hm : s.modules[frame.inst]? = some p.mi)
    (hi : p.mi.memAddrs[0]? = some p.memoryIndex) (hmem : s.mems[p.memoryIndex]? = some (initializedMemory p))
    (hc : s.host.gas.Credits (53*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (controlAfter s cfg.regularOpCost p) limits stack (controlFrame frame p) callers code)) rest post) :
    WP cfg (fuel+55) (.next (atCode s limits stack (labelPrefixFrame frame stack.size skipped code) callers
      (WNear.Binary.AllocateSearch.linkCode++discarded))) (53*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  let nested := labelPrefixFrame frame stack.size skipped code
  let back := afterBacklink s op p
  let linked := linkedStore back op p
  let updated := controlFrame frame p
  let intermediate := backlinkFrame nested (finish p)
  have intervals := intervals p hn
  have shape := initialized_shape p hn
  have hm25 : (paid (paid s op 17) op 8).mems[p.memoryIndex]? = some (initializedMemory p) := by
    simpa only [paid,chargedStore] using hmem
  have mb : back.mems[p.memoryIndex]? = some (backlinkedMemory p) := by
    exact storeI32_memory (paid (paid s op 17) op 8) p.memoryIndex ((finish p).toNat+4) (initializedMemory p)
      (Allocate.taggedValue (initializedMemory p) (finish p) 4 (header p)) hm25
  have moduleBack : back.modules[intermediate.inst]? = some p.mi := by
    simpa only [back,afterBacklink,backlinkStore,Allocate.taggedStore,paid,chargedStore,storeI32_modules,
      intermediate,backlinkFrame,endReadFrame,endSelectedFrame,nested,labelPrefixFrame] using hm
  have cb : back.host.gas.Credits (28*op+rest) := by
    dsimp only [back,afterBacklink,backlinkStore,Allocate.taggedStore]
    rw [storeI32_host]
    exact paid_credits (paid s op 17) op 8 _ (paid_credits s op 17 _ (hc.mono (by dsimp [op]; omega)))
  have cp : (previousStore back op p).host.gas.Credits (20*op+rest) := by
    unfold previousStore Allocate.taggedStore
    rw [storeI32_host]
    exact paid_credits back op 8 _ (cb.mono (by omega))
  have cu : (unflaggedStore back op p).host.gas.Credits (14*op+rest) := by
    unfold unflaggedStore maskStore
    rw [storeI32_host]
    exact paid_credits (previousStore back op p) op 6 _ (cp.mono (by omega))
  have cl : linked.host.gas.Credits (5*op+rest) := by
    unfold linked linkedStore taggedTeeStore
    rw [storeI32_host]
    exact paid_credits (unflaggedStore back op p) op 9 _ (cu.mono (by omega))
  have h2valid : 2 < frame.locals.size := by omega
  have h2 : updated.locals[2]? = some (.i32 (header p)) := by
    simp [updated,controlFrame,backlinkFrame,endReadFrame,endSelectedFrame,h2valid]
  have exit := wp_flag_exit cfg fuel rest linked limits stack updated callers skipped code discarded p post hskip h2 hn cl hnext
  have exitNext : WP cfg (fuel+5) (.next (atCode linked limits stack
      {intermediate with locals:=intermediate.locals.set! 2 (.i32 (header p))} callers
      (WNear.Binary.AllocateSearch.flagExit++discarded))) (5*op+rest) post := by
    simpa only [updated,controlFrame,intermediate,backlinkFrame,endReadFrame,endSelectedFrame,nested,labelPrefixFrame,atCode] using exit
  have ih : intermediate.locals[1]? = some (.i32 (head p)) := by
    simp [intermediate,backlinkFrame,endReadFrame,endSelectedFrame,nested,labelPrefixFrame,hhead]
  have ia : intermediate.locals[9]? = some (.i32 (header p)) := by
    simp [intermediate,backlinkFrame,endReadFrame,endSelectedFrame,nested,labelPrefixFrame,hheader]
  have writes := wp_link_writes cfg (fuel+5) (5*op+rest) back limits stack intermediate callers
    (WNear.Binary.AllocateSearch.flagExit++discarded) p post hn ih ia moduleBack hi mb (cb.mono (by dsimp [op]; omega)) exitNext
  have backNext : WP cfg (fuel+28) (.next (atCode back limits stack intermediate callers
      (WNear.Binary.AllocateSearch.previousWrite++WNear.Binary.AllocateSearch.unflagWrite++WNear.Binary.AllocateSearch.headWrite++WNear.Binary.AllocateSearch.flagExit++discarded)))
      (28*op+rest) post := by
    have cost : 23*cfg.regularOpCost+(5*op+rest)=28*op+rest := by dsimp [op]; omega
    rw [cost] at writes
    simpa only [Nat.add_assoc,Nat.reduceAdd,List.append_assoc] using writes
  have fm : finish p &&& 4294967292 = finish p := by
    unfold finish Allocate.endWord
    rw [UInt32.and_assoc,UInt32.and_self]
  have ff : finish p &&& 2 = 0 := by
    unfold finish Allocate.endWord
    rw [UInt32.and_assoc]
    change readI32 p.memory (head p).toNat &&& 0 = 0
    exact UInt32.and_zero
  have fn : finish p ≠ 0 := by
    intro hz
    have bound := hn.split.room
    have zero := congrArg UInt32.toNat hz
    change (Allocate.endWord p.memory (head p)).toNat = 0 at zero
    omega
  have backlink := wp_backlink_block cfg (fuel+28) (28*op+rest) s limits stack nested callers
    (WNear.Binary.AllocateSearch.previousWrite++WNear.Binary.AllocateSearch.unflagWrite++WNear.Binary.AllocateSearch.headWrite++WNear.Binary.AllocateSearch.flagExit++discarded)
    (head p) (finish p) (header p) p.mi p.memoryIndex (initializedMemory p) post hhead hheader hs hm hi hmem
    (by rw [shape.size]; omega) (by rw [shape.size]; exact hn.endBound) (initialized_head_finish p hn) fm ff fn
    (hc.mono (by dsimp [op]; omega)) backNext
  have cost : 25*cfg.regularOpCost+(28*op+rest)=53*cfg.regularOpCost+rest := by dsimp [op]; omega
  rw [cost] at backlink
  simpa only [WNear.Binary.AllocateSearch.linkCode,Nat.add_assoc,Nat.reduceAdd,List.cons_append,List.nil_append,List.append_assoc] using backlink
end WNear.Proofs.AllocateSearch
