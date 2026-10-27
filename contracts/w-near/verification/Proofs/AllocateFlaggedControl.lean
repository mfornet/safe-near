import Proofs.AllocateFlaggedControlState

/-! Complete actual flags-two control: skipped backlink, links, flag transfer,
and unconditional branch through thirteen labels. -/
namespace WNear.Proofs.AllocateFlagged
open Wasm Wasm.Near MeteredLogic
open AllocateSearch (Layout taggedTeeStore maskStore)
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
set_option maxHeartbeats 900000
attribute [local irreducible] WP atCode readI32 writeI32

theorem wp_link_control (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (skipped : List Label) (code discarded : Expr) (p : Layout) (post : Post)
    (hskip : skipped.length=12) (hn : Native p)
    (hh : frame.locals[1]?=some (.i32 (head p))) (ha : frame.locals[9]?=some (.i32 (header p)))
    (hs : 11≤frame.locals.size) (hm : s.modules[frame.inst]?=some p.mi)
    (hi : p.mi.memAddrs[0]?=some p.memoryIndex) (hmem : s.mems[p.memoryIndex]?=some (initializedMemory p))
    (hc : s.host.gas.Credits (57*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (controlAfter s cfg.regularOpCost p) limits stack (controlFrame frame p) callers code)) rest post) :
    WP cfg (fuel+58) (.next (atCode s limits stack (labelPrefixFrame frame stack.size skipped code) callers
      (WNear.Binary.AllocateSearch.linkCode++WNear.Binary.AllocateFlagged.transfer++discarded))) (57*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  let nested := labelPrefixFrame frame stack.size skipped code
  let raw := readI32 p.memory (head p).toNat
  let back := afterBacklink s op
  let linked := linkedStore back op p
  let updated := controlFrame frame p
  let intermediate := backlinkFrame nested raw (finish p)
  have bounds := intervals p hn
  have shape := initialized_shape p hn
  have cb : back.host.gas.Credits (40*op+rest) := paid_credits s op 17 _ (hc.mono (by dsimp [op]; omega))
  have cl : linked.host.gas.Credits (17*op+rest) := linkedStore_credits back op _ p (cb.mono (by omega))
  have ct := paid_credits linked op 5 (12*op+rest) (cl.mono (by omega))
  have mb : back.mems[p.memoryIndex]?=some (initializedMemory p) := by simpa only [back,afterBacklink,paid,chargedStore] using hmem
  have ml : (paid linked op 5).mems[p.memoryIndex]?=some (linkedMemory p) := by
    simpa only [paid,chargedStore,linked] using linkedStore_memory back op p mb
  have moduleBack : back.modules[intermediate.inst]?=some p.mi := by
    simpa only [back,afterBacklink,paid,chargedStore,intermediate,backlinkFrame,endReadFrame,AllocateSearch.endSelectedFrame,nested,labelPrefixFrame] using hm
  have moduleLinked : (paid linked op 5).modules[updated.inst]?=some p.mi := by
    simpa only [linked,linkedStore,taggedTeeStore,unflaggedStore,maskStore,previousStore,Allocate.taggedStore,back,afterBacklink,
      paid,chargedStore,storeI32_modules,updated,controlFrame,backlinkFrame,endReadFrame,AllocateSearch.endSelectedFrame] using hm
  have h1 : updated.locals[1]?=some (.i32 (head p)) := by
    simp [updated,controlFrame,backlinkFrame,endReadFrame,AllocateSearch.endSelectedFrame,hh]
  have h9 : updated.locals[9]?=some (.i32 (header p)) := by
    simp [updated,controlFrame,backlinkFrame,endReadFrame,AllocateSearch.endSelectedFrame,ha]
  have h2 : updated.locals[2]?=some (.i32 (linkedWord p)) := by
    simp [updated,controlFrame,backlinkFrame,endReadFrame,AllocateSearch.endSelectedFrame,show 2<frame.locals.size by omega]
  have tn : WP cfg fuel (.next (atCode (transferred (paid linked op 5) cfg.regularOpCost p) limits stack updated callers code)) rest post := by
    simpa only [controlAfter,linked,back,updated,op] using hnext
  have transfer := wp_transfer cfg fuel rest (paid linked op 5) limits stack updated callers skipped code discarded p post
    hskip hn h1 h2 h9 moduleLinked hi ml ct tn
  have flagNext : WP cfg (fuel+12) (.next (atCode (paid linked cfg.regularOpCost 5) limits stack
      (labelPrefixFrame updated stack.size skipped code) callers (WNear.Binary.AllocateFlagged.transfer++discarded))) (12*op+rest) post := transfer
  have flag := wp_flag_fallthrough cfg (fuel+12) (12*op+rest) linked limits stack (labelPrefixFrame updated stack.size skipped code) callers
    (WNear.Binary.AllocateFlagged.transfer++discarded) (linkedWord p) post h2 (linked_word_flag p hn)
    (cl.mono (by dsimp [op]; omega)) flagNext
  have wn : WP cfg (fuel+17) (.next (atCode linked limits stack
      {intermediate with locals:=intermediate.locals.set! 2 (.i32 (linkedWord p))} callers
      (WNear.Binary.AllocateSearch.flagExit++WNear.Binary.AllocateFlagged.transfer++discarded))) (17*op+rest) post := by
    have cost : 5*cfg.regularOpCost+(12*op+rest)=17*op+rest := by dsimp [op]; omega
    rw [cost] at flag
    simpa only [updated,controlFrame,intermediate,backlinkFrame,endReadFrame,AllocateSearch.endSelectedFrame,nested,labelPrefixFrame,
      raw,Nat.add_assoc,Nat.reduceAdd,List.append_assoc] using flag
  have ih : intermediate.locals[1]?=some (.i32 (head p)) := by
    simp [intermediate,backlinkFrame,endReadFrame,AllocateSearch.endSelectedFrame,nested,labelPrefixFrame,hh]
  have ia : intermediate.locals[9]?=some (.i32 (header p)) := by
    simp [intermediate,backlinkFrame,endReadFrame,AllocateSearch.endSelectedFrame,nested,labelPrefixFrame,ha]
  have writes := wp_link_writes cfg (fuel+17) (17*op+rest) back limits stack intermediate callers
    (WNear.Binary.AllocateSearch.flagExit++WNear.Binary.AllocateFlagged.transfer++discarded) p post hn ih ia moduleBack hi mb
    (cb.mono (by dsimp [op]; omega)) wn
  have bn : WP cfg (fuel+40) (.next (atCode back limits stack intermediate callers
      (WNear.Binary.AllocateSearch.previousWrite++WNear.Binary.AllocateSearch.unflagWrite++WNear.Binary.AllocateSearch.headWrite++
        WNear.Binary.AllocateSearch.flagExit++WNear.Binary.AllocateFlagged.transfer++discarded))) (40*op+rest) post := by
    have cost : 23*cfg.regularOpCost+(17*op+rest)=40*op+rest := by dsimp [op]; omega
    rw [cost] at writes
    simpa only [Nat.add_assoc,Nat.reduceAdd,List.append_assoc] using writes
  have mask : raw &&& 4294967292=finish p := rfl
  have skip := wp_backlink_skip cfg (fuel+40) (40*op+rest) s limits stack nested callers
    (WNear.Binary.AllocateSearch.previousWrite++WNear.Binary.AllocateSearch.unflagWrite++WNear.Binary.AllocateSearch.headWrite++
      WNear.Binary.AllocateSearch.flagExit++WNear.Binary.AllocateFlagged.transfer++discarded)
    (head p) raw (finish p) p.mi p.memoryIndex (initializedMemory p) post hh hs hm hi hmem
    (by rw [shape.size]; omega) (initialized_reads p hn).1 mask (original_flag p hn) (finish_nonzero p hn)
    (hc.mono (by dsimp [op]; omega)) bn
  have cost : 17*cfg.regularOpCost+(40*op+rest)=57*cfg.regularOpCost+rest := by dsimp [op]; omega
  rw [cost] at skip
  simpa only [WNear.Binary.AllocateSearch.linkCode,Nat.add_assoc,Nat.reduceAdd,List.cons_append,List.nil_append,List.append_assoc] using skip
end WNear.Proofs.AllocateFlagged
