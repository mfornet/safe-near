import Proofs.StateDecodePrefixWrapperTailSteps
import Proofs.InterfaceStack

/-! Actual315 publishes the zero result tag and restores its16-byte stack slot. -/
namespace WNear.Proofs.StateDecodePrefixWrapper.Tail
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
attribute [local irreducible] WP atCode finished tagged
private theorem modules_paid(s:Store NearState)(op n:Nat):(paid s op n).modules=s.modules:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem globals_paid(s:Store NearState)(op n:Nat):(paid s op n).globals=s.globals:=by
  induction n with|zero=>rfl|succ n ih=>exact ih

theorem wp_finish (cfg:WasmConfig)(fuel rest:Nat)(s:Store NearState)(limits:ExecLimits)
    (stack:Array Value)(frame:CallFrame)(callers:List CallFrame)(code:Expr)(p:Layout)(mi:ModuleInst)(global:GlobalInst)(post:Post)
    (hn:Native p)(h0:frame.locals[0]?=some (.i32 p.out))(h1:frame.locals[1]?=some (.i32 0))
    (h2:frame.locals[2]?=some (.i32 p.pointer))(h3:frame.locals[3]?=some (.i64 (lowValue p)))
    (hm:s.modules[frame.inst]?=some mi)(hi:mi.memAddrs[0]?=some p.index)(he:s.mems[p.index]?=some (highMemory p))
    (hg:mi.globalAddrs[0]?=some p.globalIndex)(hglobal:s.globals[p.globalIndex]?=some global)
    (hc:s.host.gas.Credits (7*cfg.regularOpCost+rest))
    (hnext:WP cfg fuel (.next (atCode (finished s cfg.regularOpCost p) limits stack frame callers code)) rest post):
    WP cfg (fuel+7) (.next (atCode s limits stack frame callers (WNear.Binary.StateDecodePrefixWrapper.finish++code))) (7*cfg.regularOpCost+rest) post:=by
  let op:=cfg.regularOpCost
  have ct:(tagged s op p).host.gas.Credits (4*op+rest):=by
    have h:=paid_credits s op 3 (4*op+rest) (hc.mono (by dsimp[op];omega))
    simpa only[tagged,storeI32_host] using h
  have mt:(tagged s op p).modules[frame.inst]?=some mi:=by
    simp only[tagged,storeI32_modules,modules_paid];exact hm
  have gt:(tagged s op p).globals[p.globalIndex]?=some global:=by
    simp only[tagged,storeI32_globals,globals_paid];exact hglobal
  have rn:WP cfg fuel (.next (atCode (setGlobal (paid (tagged s op p) op 4) p.globalIndex (.i32 (p.pointer+16))) limits stack frame callers code)) rest post:=by
    simpa only[finished,op] using hnext
  have restore:=InterfaceStack.wp_restore cfg fuel rest (tagged s op p) limits stack frame callers code mi p.globalIndex global p.pointer 2 16 post h2 mt hg gt ct rn
  have tagNext:WP cfg (fuel+4) (.next (atCode (tagStore s op p.index (highMemory p) p.out 0) limits stack frame callers
      ([.local_get 2,.i32_const 16,.i32_binop .add,.global_set 0]++code))) (4*op+rest) post:=by
    simpa only[tagged,tagStore] using restore
  have b:p.out.toNat+4≤(highMemory p).byteSize:=by rw[(memory_specs p hn).2.2.2];have o:=hn.outputBound;omega
  have tag:=wp_tag cfg (fuel+4) (4*op+rest) s limits stack frame callers ([.local_get 2,.i32_const 16,.i32_binop .add,.global_set 0]++code) p.out p.pointer 0 (lowValue p) mi p.index (highMemory p) post h0 h1 h2 h3 hm hi he b (hc.mono (by dsimp[op];omega)) tagNext
  simpa only[WNear.Binary.StateDecodePrefixWrapper.finish,tagCode,List.cons_append,List.nil_append,show fuel+4+3=fuel+7 by omega,
    show 3*cfg.regularOpCost+(4*op+rest)=7*cfg.regularOpCost+rest by dsimp[op];omega] using tag
end WNear.Proofs.StateDecodePrefixWrapper.Tail
