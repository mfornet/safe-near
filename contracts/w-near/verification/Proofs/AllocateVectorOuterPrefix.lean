import Proofs.AllocateVectorOuterPhases

/-! Actual687 stack reservation, both free block entries, low-byte guard and686 arguments. -/
namespace WNear.Proofs.AllocateVectorOuter
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode reserved guarded arguments

theorem wp_prefix (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (p : Layout) (post : Post) (hn : Native p) (hcode : Code s frame.inst p)
    (h1 : frame.locals[1]?=some (.i32 p.flag)) (h2 : frame.locals[2]?=some (.i32 p.size))
    (hs : 4≤frame.locals.size) (hg : s.globals[p.globalIndex]?=some p.global687)
    (hv : p.global687.value=.i32 p.sp687)
    (hc : s.host.gas.Credits (14*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (arguments s cfg.regularOpCost p) limits
      (((stack.push (.i32 p.out686)).push (.i32 p.size)).push (.i32 1))
      (nestedFrame (reservedFrame frame p) stack.size code) callers (.call 686::tailCode))) rest post) :
    WP cfg (fuel+16) (.next (atCode s limits stack frame callers (WNear.Binary.AllocateVectorOuter.body++code)))
      (14*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  let rf := reservedFrame frame p
  let inner := nestedFrame rf stack.size code
  let outer := outerFrame rf stack.size code
  let continuation := .call 686::tailCode
  have cReserved : (reserved s op p).host.gas.Credits (9*op+rest) := by
    unfold reserved
    exact paid_credits s op 5 (9*op+rest) (hc.mono (by dsimp [op];omega))
  have cGuarded : (guarded s op p).host.gas.Credits (5*op+rest) := by
    unfold guarded
    exact paid_credits (reserved s op p) op 4 _ (cReserved.mono (by omega))
  have f1 : inner.locals[1]?=some (.i32 p.flag) := by simp [inner,nestedFrame,outerFrame,emptyBlockFrame,rf,reservedFrame,h1]
  have f2 : inner.locals[2]?=some (.i32 p.size) := by simp [inner,nestedFrame,outerFrame,emptyBlockFrame,rf,reservedFrame,h2]
  have f3 : inner.locals[3]?=some (.i32 p.outerSP) := by
    simp [inner,nestedFrame,outerFrame,emptyBlockFrame,rf,reservedFrame,show 3<frame.locals.size by omega]
  have argsNext : WP cfg fuel (.next (atCode (paid (guarded s op p) cfg.regularOpCost 5) limits
      (((stack.push (.i32 (p.outerSP+8))).push (.i32 p.size)).push (.i32 1)) inner callers continuation)) rest post := by
    simpa only [arguments,inner,rf,continuation,hn.innerOut,op] using hnext
  have args := wp_arguments cfg fuel rest (guarded s op p) limits stack inner callers continuation p.outerSP p.size post
    f3 f2 cGuarded argsNext
  have guardNext : WP cfg (fuel+5) (.next (atCode (paid (reserved s op p) cfg.regularOpCost 4) limits stack inner callers
      (WNear.Binary.AllocateVectorOuter.arguments++continuation))) (5*op+rest) post := by
    simpa only [guarded,op] using args
  have guard := wp_byte_guard cfg (fuel+5) (5*op+rest) (reserved s op p) limits stack inner callers
    (WNear.Binary.AllocateVectorOuter.arguments++continuation) p.flag post f1 hn.byteFlag
    (cReserved.mono (by omega)) guardNext
  have innerNext : WP cfg (fuel+9) (.next (atCode (reserved s op p) limits stack
      (emptyBlockFrame outer stack.size WNear.Binary.AllocateVectorOuter.alternative) callers WNear.Binary.AllocateVectorOuter.accepted))
      (9*op+rest) post := by
    have ce : 4*cfg.regularOpCost+(5*op+rest)=9*op+rest := by dsimp [op];omega
    rw [ce] at guard
    simpa only [inner,nestedFrame,outer,outerFrame,continuation,tailCode,WNear.Binary.AllocateVectorOuter.accepted,
      List.append_assoc,List.cons_append,List.nil_append,List.singleton_append,Nat.add_assoc,Nat.reduceAdd] using guard
  have enterInner := wp_block_empty cfg (fuel+9) (9*op+rest) (reserved s op p) limits stack outer callers
    WNear.Binary.AllocateVectorOuter.accepted WNear.Binary.AllocateVectorOuter.alternative post cReserved innerNext
  have outerNext : WP cfg (fuel+10) (.next (atCode (reserved s op p) limits stack
      (emptyBlockFrame rf stack.size (WNear.Binary.AllocateVectorOuter.restore++code)) callers
      ([.block .empty WNear.Binary.AllocateVectorOuter.accepted]++WNear.Binary.AllocateVectorOuter.alternative)))
      (9*op+rest) post := by
    simpa only [outer,outerFrame,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd] using enterInner
  have enterOuter := wp_block_empty cfg (fuel+10) (9*op+rest) (reserved s op p) limits stack rf callers
    ([.block .empty WNear.Binary.AllocateVectorOuter.accepted]++WNear.Binary.AllocateVectorOuter.alternative)
    (WNear.Binary.AllocateVectorOuter.restore++code) post cReserved outerNext
  have reserveNext : WP cfg (fuel+11) (.next (atCode
      (setGlobal (paid s cfg.regularOpCost 5) p.globalIndex (.i32 (p.sp687-32))) limits stack
      {frame with locals:=frame.locals.set! 3 (.i32 (p.sp687-32))} callers
      ([.block .empty ([.block .empty WNear.Binary.AllocateVectorOuter.accepted]++WNear.Binary.AllocateVectorOuter.alternative)]++
        WNear.Binary.AllocateVectorOuter.restore++code))) (9*op+rest) post := by
    simpa only [reserved,rf,reservedFrame,hn.innerSP,op,List.cons_append,List.nil_append] using enterOuter
  have reserve := InterfaceStack.wp_reserve cfg (fuel+11) (9*op+rest) s limits stack frame callers
    ([.block .empty ([.block .empty WNear.Binary.AllocateVectorOuter.accepted]++WNear.Binary.AllocateVectorOuter.alternative)]++
        WNear.Binary.AllocateVectorOuter.restore++code)
    p.mi p.globalIndex p.global687 p.sp687 3 32 post
    hcode.vector.allocation.allocation.retry.originalCode.search.module
    hcode.vector.allocation.allocation.retry.originalCode.globalIndex hg hv
    (hc.mono (by dsimp [op];omega)) reserveNext
  have ce : 5*cfg.regularOpCost+(9*op+rest)=14*cfg.regularOpCost+rest := by dsimp [op];omega
  rw [ce] at reserve
  simpa only [WNear.Binary.AllocateVectorOuter.body,WNear.Binary.AllocateVectorOuter.reserve,List.append_assoc,
    List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd] using reserve
end WNear.Proofs.AllocateVectorOuter
