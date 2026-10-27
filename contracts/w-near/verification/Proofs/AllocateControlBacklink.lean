import Proofs.AllocateControlGuard

/-! The actual conditional backlink block in the zero-low-flags split path. -/
namespace WNear.Proofs.AllocateSearch
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
set_option maxHeartbeats 700000
attribute [local irreducible] WP atCode readI32 writeI32

def backlinkStore (s : Store NearState) (op index : Nat) (memory : Memory) (finish header : UInt32) :=
  Allocate.taggedStore (paid s op 17) op index 4 4 memory finish finish header

/-- Both real tests, the tagged backlink write, and both free block transitions.
The end-word hypotheses are primitive current reads derived from original heap facts. -/
theorem wp_backlink_block (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (head finish header : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (hl : frame.locals[1]? = some (.i32 head)) (hh : frame.locals[9]? = some (.i32 header))
    (hs : 11 ≤ frame.locals.size) (hm : s.modules[frame.inst]? = some mi)
    (hi : mi.memAddrs[0]? = some index) (hmem : s.mems[index]? = some memory)
    (hr : head.toNat+4 ≤ memory.byteSize) (hw : finish.toNat+8 ≤ memory.byteSize)
    (hread : readI32 memory head.toNat = finish) (hmask : finish &&& 4294967292 = finish)
    (hf : finish &&& 2 = 0) (hn : finish ≠ 0) (hc : s.host.gas.Credits (25*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (backlinkStore s cfg.regularOpCost index memory finish header)
      limits stack (backlinkFrame frame finish) callers code)) rest post) :
    WP cfg (fuel+27) (.next (atCode s limits stack frame callers
      (.block .empty WNear.Binary.AllocateSearch.backlinkBody::code))) (25*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  let bf := emptyBlockFrame frame stack.size code
  let written := backlinkStore s op index memory finish header
  let updated := backlinkFrame frame finish
  let innerUpdated := backlinkFrame bf finish
  let label : Label := {arity:=0,height:=stack.size,rest:=code,loop:=none}
  have h2 : 2 < frame.locals.size := by omega
  have two : innerUpdated.locals[2]? = some (.i32 finish) := by simp [innerUpdated,backlinkFrame,endReadFrame,endSelectedFrame,bf,emptyBlockFrame,h2]
  have nine : innerUpdated.locals[9]? = some (.i32 header) := by simp [innerUpdated,backlinkFrame,endReadFrame,endSelectedFrame,bf,emptyBlockFrame,hh]
  have hm17 : (paid s op 17).modules[innerUpdated.inst]? = some mi := by
    simpa only [paid,chargedStore,innerUpdated,backlinkFrame,endSelectedFrame,endReadFrame,bf,emptyBlockFrame] using hm
  have hmem17 : (paid s op 17).mems[index]? = some memory := by simpa only [paid,chargedStore] using hmem
  have cp := paid_credits s op 17 (8*op+rest) (hc.mono (by dsimp [op]; omega))
  have cf : written.host.gas.Credits rest := by
    dsimp only [written,backlinkStore,Allocate.taggedStore]
    rw [storeI32_host]
    exact paid_credits (paid s op 17) op 8 rest cp
  have ending := wp_end_label cfg fuel rest written limits stack updated callers label post cf hnext
  have endNext : WP cfg (fuel+1) (.next (atCode written limits stack innerUpdated callers [])) rest post := by
    simpa only [updated,innerUpdated,backlinkFrame,endReadFrame,endSelectedFrame,bf,emptyBlockFrame,label,atCode] using ending
  have write := Allocate.wp_tagged_store cfg (fuel+1) rest (paid s op 17) limits stack innerUpdated callers []
    2 2 9 4 4 finish finish header mi index memory post two two nine hm17 hi hmem17
    (by omega) (by omega) cp endNext
  have guardedNext : WP cfg (fuel+9) (.next (atCode (paid s op 17) limits stack innerUpdated callers
      WNear.Binary.AllocateSearch.backlinkWrite)) (8*op+rest) post := by
    simpa only [Allocate.taggedPrefix,WNear.Binary.AllocateSearch.backlinkWrite,List.append_nil,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd] using write
  have guarded := wp_backlink_guard cfg (fuel+9) (8*op+rest) s limits stack bf callers
    WNear.Binary.AllocateSearch.backlinkWrite head finish mi index memory post hl hs hm hi hmem hr hread hmask hf hn
    (hc.mono (by dsimp [op]; omega)) guardedNext
  have inside : WP cfg (fuel+26) (.next (atCode s limits stack bf callers WNear.Binary.AllocateSearch.backlinkBody))
      (25*op+rest) post := by
    have cost : 17*cfg.regularOpCost+(8*op+rest)=25*op+rest := by dsimp [op]; omega
    rw [cost] at guarded
    simpa only [WNear.Binary.AllocateSearch.backlinkBody,Nat.add_assoc,Nat.reduceAdd] using guarded
  exact wp_block_empty cfg (fuel+26) (25*op+rest) s limits stack frame callers WNear.Binary.AllocateSearch.backlinkBody code post hc inside
end WNear.Proofs.AllocateSearch
