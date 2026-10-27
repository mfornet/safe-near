import Proofs.AllocatePositiveArguments

/-! Complete actual first580 attempt, accepted by its returned nonzero pointer. -/
namespace WNear.Proofs.AllocatePositive
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
attribute [local irreducible] WP atCode AllocateSearch.callAfter WNear.Binary.Allocate.searchFunction

def attemptAfter (s : Store NearState) (op : Nat) (p : Layout) :=
  AllocateSearch.callAfter (paid s op 7) op (searchLayout p)
def foundAfter (s : Store NearState) (op : Nat) (p : Layout) := paid (attemptAfter s op p) op 2
def foundFrame (frame : CallFrame) (p : Layout) := {frame with locals:=frame.locals.set! 1 (.i32 (result p))}

/-- The actual two-opcode successful-search branch, over an arbitrary store. -/
theorem wp_found (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (p : Layout) (post : Post) (hn : result p≠0)
    (hc : s.host.gas.Credits (2*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 2) limits base.toArray (foundFrame frame p) callers code)) rest post) :
    WP cfg (fuel+2) (.next (atCode s limits (base.toArray.push (.i32 (result p)))
      (emptyBlockFrame frame base.toArray.size code) callers (.local_tee 1::.br_if 0::WNear.Binary.Allocate.retry)))
      (2*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  let bf := emptyBlockFrame frame base.toArray.size code
  have bn : WP cfg fuel (.next (atCode (chargedStore (paid s op 1) cfg.regularOpCost) limits base.toArray
      (foundFrame frame p) callers code)) rest post := by simpa only [op,paid] using hnext
  have branch := wp_br_if_block_nonzero cfg fuel rest (paid s op 1) limits base.toArray (foundFrame frame p) callers code
    WNear.Binary.Allocate.retry (result p) post hn (paid_credits s op 1 _ (hc.mono (by dsimp [op]; omega))) bn
  have teeNext : WP cfg (fuel+1) (.next (atCode (chargedStore s cfg.regularOpCost) limits
      (base.toArray.push (.i32 (result p))) {bf with locals:=bf.locals.set! 1 (.i32 (result p))} callers
      (.br_if 0::WNear.Binary.Allocate.retry))) (op+rest) post := by
    simpa only [foundFrame,bf,emptyBlockFrame,paid,op] using branch
  have tee := wp_local_tee cfg (fuel+1) (op+rest) s limits base.toArray bf callers
    (.br_if 0::WNear.Binary.Allocate.retry) 1 (.i32 (result p)) post (hc.mono (by dsimp [op]; omega)) teeNext
  have cost : cfg.regularOpCost+(op+rest)=2*cfg.regularOpCost+rest := by dsimp [op]; omega
  simpa only [cost,Nat.add_assoc,Nat.reduceAdd] using tee

theorem wp_first_search (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (p : Layout) (post : Post) (hn : Native p)
    (h4 : frame.locals[4]?=some (.i32 (words p))) (h2 : frame.locals[2]?=some (.i32 1))
    (h3 : frame.locals[3]?=some (.i32 (scratch p)))
    (hcode : Code s frame.inst p) (hmem : s.mems[p.memoryIndex]?=some (savedMemory p))
    (hd : callers.length+2<limits.maxCallDepth) (hc : s.host.gas.Credits (283*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (foundAfter s cfg.regularOpCost p) limits base.toArray (foundFrame frame p) callers code)) rest post) :
    WP cfg (fuel+247) (.next (atCode s limits base.toArray frame callers
      (WNear.Binary.AllocatePositive.searchBlock++code))) (283*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  let bf := emptyBlockFrame frame base.toArray.size code
  let current := attemptAfter s op p
  have c7 := paid_credits s op 7 (274*op+(2*op+rest)) (hc.mono (by dsimp [op]; omega))
  have c281 : current.host.gas.Credits (2*op+rest) := AllocateSearch.callAfter_credits (paid s op 7) op _ (searchLayout p) c7
  have nonzero : result p≠0 := (Allocate.split_result (savedMemory p) (AllocateSearch.head (searchLayout p)) (words p) hn.search.split).2.1
  have fn : WP cfg fuel (.next (atCode (paid current cfg.regularOpCost 2) limits base.toArray (foundFrame frame p) callers code)) rest post := by
    simpa only [foundAfter,current,op] using hnext
  have tee := wp_found cfg fuel rest current limits base frame callers code p post nonzero c281 fn
  have arr : (base++[Value.i32 (AllocateSearch.pointer (searchLayout p))]).toArray=base.toArray.push (.i32 (AllocateSearch.pointer (searchLayout p))) := by apply Array.toList_inj.mp; simp
  have callNext : WP cfg (fuel+2) (.next (atCode (AllocateSearch.callAfter (paid s op 7) op (searchLayout p)) limits
      (base++[Value.i32 (AllocateSearch.pointer (searchLayout p))]).toArray bf callers (.local_tee 1::.br_if 0::WNear.Binary.Allocate.retry))) (2*op+rest) post := by
    simpa only [result,arr,current,attemptAfter,Nat.add_assoc,Nat.reduceAdd] using tee
  have inst : bf.inst=frame.inst := rfl
  have code7 : AllocateSearch.SearchCode (paid s op 7) (searchLayout p) bf.inst := by
    rw [inst]
    constructor
    · exact hcode.search.toCode.paid s op 7 (searchLayout p) frame.inst
    · exact hcode.search.sizeIndex
    · simpa only [paid,chargedStore] using hcode.search.sizeFunction
  have mem7base : (paid s op 7).mems[p.memoryIndex]?=some (savedMemory p) := by
    simpa only [paid,chargedStore] using hmem
  have mem7 : (paid s op 7).mems[(searchLayout p).memoryIndex]?=some (searchLayout p).memory := by
    simpa only [searchLayout] using mem7base
  have fn7 : (paid s op 7).funcs[p.searchAddress]?=some (.wasm WNear.Binary.AllocateSearch.signature bf.inst WNear.Binary.Allocate.searchFunction) := by
    rw [inst]
    simpa only [paid,chargedStore] using hcode.searchFunction
  have call := AllocateSearch.wp_call cfg (fuel+2) (2*op+rest) (paid s op 7) limits base bf callers
    (.local_tee 1::.br_if 0::WNear.Binary.Allocate.retry) (searchLayout p) p.searchAddress post hn.search code7 mem7
    hcode.searchIndex fn7 hd c7 callNext
  have argsNext : WP cfg (fuel+239) (.next (atCode (paid s op 7) limits
      (base++[Value.i32 (words p),.i32 1,.i32 (scratch p+12),.i32 1057464,.i32 1057464]).toArray bf callers
      (.call 580::.local_tee 1::.br_if 0::WNear.Binary.Allocate.retry))) (276*op+rest) post := by
    have cost : 274*cfg.regularOpCost+(2*op+rest)=276*op+rest := by dsimp [op]; omega
    rw [cost] at call
    simpa only [searchLayout,Nat.add_assoc,Nat.reduceAdd] using call
  have args := wp_arguments cfg (fuel+239) (276*op+rest) s limits base bf callers
    (.local_tee 1::.br_if 0::WNear.Binary.Allocate.retry) p post h4 h2 h3 (hc.mono (by dsimp [op]; omega)) argsNext
  have cost : 7*cfg.regularOpCost+(276*op+rest)=283*cfg.regularOpCost+rest := by dsimp [op]; omega
  rw [cost] at args
  apply wp_block_empty cfg (fuel+246) _ s limits base.toArray frame callers _ code post hc
  simpa only [Nat.add_assoc,Nat.reduceAdd,List.append_assoc,List.append_eq,List.cons_append,List.nil_append] using args
end WNear.Proofs.AllocatePositive
