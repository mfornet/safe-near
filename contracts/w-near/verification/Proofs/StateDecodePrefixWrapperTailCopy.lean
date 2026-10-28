import Proofs.StateDecodePrefixWrapperTailSteps

/-! Actual315 snapshots the high length before its two accepted output writes. -/
namespace WNear.Proofs.StateDecodePrefixWrapper.Tail
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
attribute [local irreducible] WP atCode highRead copiedLow copiedHigh zeroed
private theorem modules_paid(s:Store NearState)(op n:Nat):(paid s op n).modules=s.modules:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem mems_paid(s:Store NearState)(op n:Nat):(paid s op n).mems=s.mems:=by
  induction n with|zero=>rfl|succ n ih=>exact ih

def copyLinearCode:Expr:=readHighCode++writeLowCode++writeHighCode++zeroCode
def copyFinalFrame(frame:CallFrame)(p:Layout):=highFrame (copyFrame frame p) 0

theorem wp_copy_linear (cfg:WasmConfig)(fuel rest:Nat)(s:Store NearState)(limits:ExecLimits)
    (stack:Array Value)(frame:CallFrame)(callers:List CallFrame)(code:Expr)(p:Layout)(mi:ModuleInst)(post:Post)
    (hn:Native p)(h0:frame.locals[0]?=some (.i32 p.out))(h1:frame.locals[1]?=some (.i32 1))
    (h2:frame.locals[2]?=some (.i32 p.pointer))(h3:frame.locals[3]?=some (.i64 (lowValue p)))(hsize:4≤frame.locals.size)
    (hm:s.modules[frame.inst]?=some mi)(hi:mi.memAddrs[0]?=some p.index)(he:s.mems[p.index]?=some p.memory)
    (hc:s.host.gas.Credits (15*cfg.regularOpCost+rest))
    (hnext:WP cfg fuel (.next (atCode (zeroed s cfg.regularOpCost p) limits stack (copyFinalFrame frame p) callers code)) rest post):
    WP cfg (fuel+15) (.next (atCode s limits stack frame callers (copyLinearCode++code))) (15*cfg.regularOpCost+rest) post:=by
  let op:=cfg.regularOpCost
  let f:=copyFrame frame p
  have f0:f.locals[0]?=some (.i32 p.out):=by simp[f,copyFrame,Array.set!,h0]
  have f1:f.locals[1]?=some (.i32 (highValue p)):=by simp[f,copyFrame,Array.set!,show 1<frame.locals.size by omega]
  have f2:f.locals[2]?=some (.i32 p.pointer):=by simp[f,copyFrame,Array.set!,h2]
  have f3:f.locals[3]?=some (.i64 (lowValue p)):=by simp[f,copyFrame,Array.set!,h3]
  have c5:(highRead s op).host.gas.Credits (10*op+rest):=by
    unfold highRead
    exact paid_credits s op 5 _ (hc.mono (by dsimp[op];omega))
  have c8:(copiedLow s op p).host.gas.Credits (7*op+rest):=by
    have h:=paid_credits (highRead s op) op 3 (7*op+rest) (c5.mono (by omega))
    simpa only[copiedLow,storeI64_host] using h
  have c13:(copiedHigh s op p).host.gas.Credits (2*op+rest):=by
    have h:=paid_credits (copiedLow s op p) op 5 (2*op+rest) (c8.mono (by omega))
    simpa only[copiedHigh,storeI32_host] using h
  have hm5:(highRead s op).modules[f.inst]?=some mi:=by rw[highRead,modules_paid];exact hm
  have me5:(highRead s op).mems[p.index]?=some p.memory:=by rw[highRead,mems_paid];exact he
  have hm8:(copiedLow s op p).modules[f.inst]?=some mi:=by simp only[copiedLow,storeI64_modules,modules_paid];exact hm5
  have me8:(copiedLow s op p).mems[p.index]?=some (lowMemory p):=by
    unfold copiedLow lowMemory
    apply storeI64_memory
    rw[mems_paid];exact me5
  have shape:=memory_specs p hn
  have highBound:(p.out+12).toNat+4≤(lowMemory p).byteSize:=by rw[shape.2.1,add_output p hn];exact hn.outputBound
  have lowBound:p.out.toNat+12≤p.memory.byteSize:=by have b:=hn.outputBound;omega
  have readBound:(p.pointer+12).toNat+4≤p.memory.byteSize:=by rw[add_pointer p hn];exact hn.pointerBound
  have zn:WP cfg fuel (.next (atCode (paid (copiedHigh s op p) op 2) limits stack (highFrame f 0) callers code)) rest post:=by
    simpa only[zeroed,copyFinalFrame,f,op] using hnext
  have zero:=wp_zero cfg fuel rest (copiedHigh s op p) limits stack f callers code post c13 zn
  have highNext:WP cfg (fuel+2) (.next (atCode (highStore (copiedLow s op p) op p.index (lowMemory p) p.out (highValue p)) limits stack f callers (zeroCode++code))) (2*op+rest) post:=by
    simpa only[copiedHigh,highStore] using zero
  have wh:=wp_writeHigh cfg (fuel+2) (2*op+rest) (copiedLow s op p) limits stack f callers (zeroCode++code) p.out p.pointer (highValue p) (lowValue p) mi p.index (lowMemory p) post f0 f1 f2 f3 hm8 hi me8 highBound (c8.mono (by dsimp[op];omega)) highNext
  have lowNext:WP cfg (fuel+7) (.next (atCode (lowStore (highRead s op) op p.index p.memory p.out (lowValue p)) limits stack f callers (writeHighCode++zeroCode++code))) (7*op+rest) post:=by
    simpa only[copiedLow,lowStore,List.append_assoc,show fuel+2+5=fuel+7 by omega,show 5*cfg.regularOpCost+(2*op+rest)=7*op+rest by dsimp[op];omega] using wh
  have wl:=wp_writeLow cfg (fuel+7) (7*op+rest) (highRead s op) limits stack f callers (writeHighCode++zeroCode++code) p.out p.pointer (highValue p) (lowValue p) mi p.index p.memory post f0 f1 f2 f3 hm5 hi me5 lowBound (c5.mono (by dsimp[op];omega)) lowNext
  have readNext:WP cfg (fuel+10) (.next (atCode (paid s op 5) limits stack (highFrame frame (readI32 p.memory (p.pointer+12).toNat)) callers (writeLowCode++writeHighCode++zeroCode++code))) (10*op+rest) post:=by
    simpa only[highRead,f,copyFrame,highFrame,highValue,List.append_assoc,show fuel+7+3=fuel+10 by omega,show 3*cfg.regularOpCost+(7*op+rest)=10*op+rest by dsimp[op];omega] using wl
  have read:=wp_readHigh cfg (fuel+10) (10*op+rest) s limits stack frame callers (writeLowCode++writeHighCode++zeroCode++code) p.out p.pointer 1 (lowValue p) mi p.index p.memory post h0 h1 h2 h3 hm hi he readBound (hc.mono (by dsimp[op];omega)) readNext
  simpa only[copyLinearCode,List.append_assoc,show fuel+10+5=fuel+15 by omega,show 5*cfg.regularOpCost+(10*op+rest)=15*cfg.regularOpCost+rest by dsimp[op];omega] using read
end WNear.Proofs.StateDecodePrefixWrapper.Tail
