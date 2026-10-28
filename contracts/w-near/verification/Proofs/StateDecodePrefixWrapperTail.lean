import Proofs.StateDecodePrefixWrapperTailCopy
import Proofs.StateDecodePrefixWrapperTailFinish
import Proofs.StateDecodePrefixWrapperTailFrame
import NearVM.MeteredSelectionRules

/-! Complete315 accepted tail: both cached result reads, two real block entries,
accepted guard/copy/branch, zero tag, and16-byte stack restoration. -/
namespace WNear.Proofs.StateDecodePrefixWrapper.Tail
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
attribute [local irreducible] WP atCode cached guarded zeroed copied finished after
private theorem modules_paid(s:Store NearState)(op n:Nat):(paid s op n).modules=s.modules:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem mems_paid(s:Store NearState)(op n:Nat):(paid s op n).mems=s.mems:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem globals_paid(s:Store NearState)(op n:Nat):(paid s op n).globals=s.globals:=by
  induction n with|zero=>rfl|succ n ih=>exact ih

def codeTail:Expr:=WNear.Binary.StateDecodePrefixWrapper.cache++
  [.block .empty ([.block .empty (WNear.Binary.StateDecodePrefixWrapper.guard++WNear.Binary.StateDecodePrefixWrapper.copy)]++WNear.Binary.StateDecodePrefixWrapper.rejected)]++WNear.Binary.StateDecodePrefixWrapper.finish
private theorem finalFrame_eq(frame:CallFrame)(p:Layout):
    copyFinalFrame (cacheFrame frame p.memory p.pointer) p=finalFrame frame p:=by
  simp[copyFinalFrame,highFrame,copyFrame,finalFrame,cacheFrame,Array.set!]

theorem wp_tail (cfg:WasmConfig)(fuel rest:Nat)(s:Store NearState)(limits:ExecLimits)
    (stack:Array Value)(frame:CallFrame)(callers:List CallFrame)(code:Expr)(p:Layout)(mi:ModuleInst)(global:GlobalInst)(post:Post)
    (hn:Native p)(h0:frame.locals[0]?=some (.i32 p.out))(h2:frame.locals[2]?=some (.i32 p.pointer))(hsize:4≤frame.locals.size)
    (hm:s.modules[frame.inst]?=some mi)(hi:mi.memAddrs[0]?=some p.index)(he:s.mems[p.index]?=some p.memory)
    (hg:mi.globalAddrs[0]?=some p.globalIndex)(hglobal:s.globals[p.globalIndex]?=some global)
    (htag:readI32 p.memory p.pointer.toNat≠1)(hc:s.host.gas.Credits (33*cfg.regularOpCost+rest))
    (hnext:WP cfg fuel (.next (atCode (after s cfg.regularOpCost p) limits stack (finalFrame frame p) callers code)) rest post):
    WP cfg (fuel+35) (.next (atCode s limits stack frame callers (codeTail++code))) (33*cfg.regularOpCost+rest) post:=by
  let op:=cfg.regularOpCost
  let c:=cacheFrame frame p.memory p.pointer
  let finishCode:=WNear.Binary.StateDecodePrefixWrapper.finish++code
  let n:=emptyBlockFrame (emptyBlockFrame c stack.size finishCode) stack.size WNear.Binary.StateDecodePrefixWrapper.rejected
  let f:=copyFinalFrame c p
  have c0:c.locals[0]?=some (.i32 p.out):=by simp[c,cacheFrame,Array.set!,h0]
  have c1:c.locals[1]?=some (.i32 1):=by simp[c,cacheFrame,Array.set!,show 1<frame.locals.size by omega]
  have c2:c.locals[2]?=some (.i32 p.pointer):=by simp[c,cacheFrame,Array.set!,h2]
  have c3:c.locals[3]?=some (.i64 (lowValue p)):=by simp[c,cacheFrame,lowValue,Array.set!,show 3<frame.locals.size by omega]
  have cs:4≤c.locals.size:=by simpa only[c,cacheFrame,Array.size_set!] using hsize
  have f0:f.locals[0]?=some (.i32 p.out):=by simp[f,copyFinalFrame,highFrame,copyFrame,Array.set!,c0]
  have f1:f.locals[1]?=some (.i32 0):=by simp[f,copyFinalFrame,highFrame,copyFrame,Array.set!,show 1<c.locals.size by omega]
  have f2:f.locals[2]?=some (.i32 p.pointer):=by simp[f,copyFinalFrame,highFrame,copyFrame,Array.set!,c2]
  have f3:f.locals[3]?=some (.i64 (lowValue p)):=by simp[f,copyFinalFrame,highFrame,copyFrame,Array.set!,c3]
  have fEq:f=finalFrame frame p:=finalFrame_eq frame p
  have gc:(guarded s op).host.gas.Credits (23*op+rest):=guarded_credits s op rest hc
  have cc:(copied (guarded s op) op p).host.gas.Credits (7*op+rest):=
    copied_credits (guarded s op) op (7*op+rest) p (gc.mono (by omega))
  have zc:(zeroed (guarded s op) op p).host.gas.Credits (8*op+rest):=
    zeroed_credits (guarded s op) op (8*op+rest) p (gc.mono (by omega))
  have gm:(guarded s op).modules[c.inst]?=some mi:=by rw[guarded,modules_paid,cached,modules_paid];exact hm
  have ge:(guarded s op).mems[p.index]?=some p.memory:=by rw[guarded,mems_paid,cached,mems_paid];exact he
  have gg:(guarded s op).globals[p.globalIndex]?=some global:=by rw[guarded,globals_paid,cached,globals_paid];exact hglobal
  have cf:=copied_fields (guarded s op) op p
  have cm:(copied (guarded s op) op p).modules[f.inst]?=some mi:=by rw[cf.2.1];exact gm
  have cg:(copied (guarded s op) op p).globals[p.globalIndex]?=some global:=by rw[cf.2.2.2];exact gg
  have fn:WP cfg fuel (.next (atCode (finished (copied (guarded s op) op p) op p) limits stack f callers code)) rest post:=by
    simpa only[after,op,fEq] using hnext
  have finish:=wp_finish cfg fuel rest (copied (guarded s op) op p) limits stack f callers code p mi global post hn f0 f1 f2 f3 cm hi (copied_memory (guarded s op) op p ge) hg cg cc fn
  simp only[copied,op] at finish
  have branch:=wp_br_two_blocks cfg (fuel+7) (7*op+rest) (zeroed (guarded s op) op p) limits stack f callers finishCode WNear.Binary.StateDecodePrefixWrapper.rejected [] post (zc.mono (by dsimp[op];omega)) finish
  have copyNext:WP cfg (fuel+8) (.next (atCode (zeroed (guarded s op) op p) limits stack (copyFinalFrame n p) callers [.br 1])) (8*op+rest) post:=by
    simpa only[n,f,copyFinalFrame,highFrame,copyFrame,emptyBlockFrame,finishCode,show fuel+7+1=fuel+8 by omega,
      show cfg.regularOpCost+(7*op+rest)=8*op+rest by dsimp[op];omega] using branch
  have copy:=wp_copy_linear cfg (fuel+8) (8*op+rest) (guarded s op) limits stack n callers [.br 1] p mi post hn c0 c1 c2 c3 cs gm hi ge
    (gc.mono (by dsimp[op];omega)) copyNext
  have guardNext:WP cfg (fuel+23) (.next (atCode (paid (cached s op) op 5) limits stack n callers WNear.Binary.StateDecodePrefixWrapper.copy)) (23*op+rest) post:=by
    simpa only[guarded,WNear.Binary.StateDecodePrefixWrapper.copy,copyLinearCode,readHighCode,writeLowCode,writeHighCode,zeroCode,List.cons_append,List.nil_append,List.append_assoc,
      show fuel+8+15=fuel+23 by omega,show 15*cfg.regularOpCost+(8*op+rest)=23*op+rest by dsimp[op];omega] using copy
  have cb:p.pointer.toNat+4≤p.memory.byteSize:=by have b:=hn.pointerBound;omega
  have cacheCredits:(cached s op).host.gas.Credits (28*op+rest):=by unfold cached;exact StorePairCaller.paid_credits s op 5 _ (hc.mono (by dsimp[op];omega))
  have cacheModule:(cached s op).modules[n.inst]?=some mi:=by rw[cached,modules_paid];exact hm
  have cacheMemory:(cached s op).mems[p.index]?=some p.memory:=by rw[cached,mems_paid];exact he
  have guard:=StateDecodePrefixWrapper.wp_guard cfg (fuel+23) (23*op+rest) (cached s op) limits stack n callers WNear.Binary.StateDecodePrefixWrapper.copy p.pointer mi p.index p.memory post c2 cacheModule hi cacheMemory cb htag (cacheCredits.mono (by dsimp[op];omega)) guardNext
  have guardWP:WP cfg (fuel+28) (.next (atCode (cached s op) limits stack n callers (WNear.Binary.StateDecodePrefixWrapper.guard++WNear.Binary.StateDecodePrefixWrapper.copy))) (28*op+rest) post:=by
    simpa only[show fuel+23+5=fuel+28 by omega,show 5*cfg.regularOpCost+(23*op+rest)=28*op+rest by dsimp[op];omega] using guard
  have inner:=wp_block_empty cfg (fuel+28) (28*op+rest) (cached s op) limits stack (emptyBlockFrame c stack.size finishCode) callers
    (WNear.Binary.StateDecodePrefixWrapper.guard++WNear.Binary.StateDecodePrefixWrapper.copy) WNear.Binary.StateDecodePrefixWrapper.rejected post cacheCredits guardWP
  have outer:=wp_block_empty cfg (fuel+29) (28*op+rest) (cached s op) limits stack c callers
    ([.block .empty (WNear.Binary.StateDecodePrefixWrapper.guard++WNear.Binary.StateDecodePrefixWrapper.copy)]++WNear.Binary.StateDecodePrefixWrapper.rejected) finishCode post cacheCredits inner
  have cachedNext:WP cfg (fuel+30) (.next (atCode (paid s op 5) limits stack c callers
      (.block .empty ([.block .empty (WNear.Binary.StateDecodePrefixWrapper.guard++WNear.Binary.StateDecodePrefixWrapper.copy)]++WNear.Binary.StateDecodePrefixWrapper.rejected)::finishCode))) (28*op+rest) post:=by
    simpa only[cached,show fuel+29+1=fuel+30 by omega,show fuel+28+1=fuel+29 by omega] using outer
  have b12:p.pointer.toNat+12≤p.memory.byteSize:=by have b:=hn.pointerBound;omega
  have cache:=StateDecodePrefixWrapper.wp_cache cfg (fuel+30) (28*op+rest) s limits stack frame callers
    (.block .empty ([.block .empty (WNear.Binary.StateDecodePrefixWrapper.guard++WNear.Binary.StateDecodePrefixWrapper.copy)]++WNear.Binary.StateDecodePrefixWrapper.rejected)::finishCode) p.pointer mi p.index p.memory post h2 hm hi he b12 (hc.mono (by dsimp[op];omega)) cachedNext
  simpa only[codeTail,finishCode,List.append_assoc,List.singleton_append,List.cons_append,List.nil_append,show fuel+30+5=fuel+35 by omega,
    show 5*cfg.regularOpCost+(28*op+rest)=33*cfg.regularOpCost+rest by dsimp[op];omega] using cache
end WNear.Proofs.StateDecodePrefixWrapper.Tail
