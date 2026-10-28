import Proofs.AllocateVectorCacheBranch
import Proofs.AllocateVectorFinish
import Proofs.AllocateVectorFrame
import Proofs.AllocateVectorResources
import Proofs.AllocateVectorCode

/-! Concrete686 suffix after690, deriving every memory/global resource from original data. -/
namespace WNear.Proofs.AllocateVector
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
set_option maxRecDepth 16384
set_option maxHeartbeats 600000
attribute [local irreducible] WP atCode allocated joined after finished resultMemory

def exitCode : Expr := WNear.Binary.AllocateVector.nonzero++WNear.Binary.AllocateVector.record++
  WNear.Binary.AllocateVector.restore++[.return]
def alternateCode : Expr := WNear.Binary.AllocateVector.alternateArguments++[.call 688]++WNear.Binary.AllocateVector.alternateCache

private theorem mems_paid (s : Store NearState) (op n : Nat) : (paid s op n).mems=s.mems := by
  induction n with | zero=>rfl | succ n ih=>exact ih
private theorem modules_paid (s : Store NearState) (op n : Nat) : (paid s op n).modules=s.modules := by
  induction n with | zero=>rfl | succ n ih=>exact ih
private theorem globals_paid (s : Store NearState) (op n : Nat) : (paid s op n).globals=s.globals := by
  induction n with | zero=>rfl | succ n ih=>exact ih

theorem wp_suffix (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame caller : CallFrame) (callers : List CallFrame)
    (p : Layout) (post : Post) (hn : Native p) (hcode : Code s frame.inst p)
    (h0 : frame.locals[0]?=some (.i32 p.out686)) (h3 : frame.locals[3]?=some (.i32 (reservedSP p)))
    (hs : 6≤frame.locals.size) (ha : frame.arity=0) (hh : frame.height=base.length)
    (hm : s.mems[p.memoryIndex]?=some p.memory) (hg : s.globals[p.globalIndex]?=some p.outerGlobal)
    (hc : s.host.gas.Credits (bodyCost p*cfg.regularOpCost+fee cfg p+rest))
    (hnext : WP cfg fuel (.next (atCode (after cfg s p) limits base.toArray caller callers caller.code)) rest post) :
    WP cfg (fuel+21) (.next (atCode (allocated cfg s p) limits base.toArray
      (emptyBlockFrame (emptyBlockFrame frame base.toArray.size exitCode) base.toArray.size alternateCode)
      (caller::callers) (WNear.Binary.AllocateVector.cache++[.br 1]))) (21*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  let ff := cachedFrame frame p
  have h0f : ff.locals[0]?=some (.i32 p.out686) := by simp [ff,cachedFrame,h0]
  have h3f : ff.locals[3]?=some (.i32 (reservedSP p)) := by simp [ff,cachedFrame,h3]
  have h2f : ff.locals[2]?=some (.i32 (result p)) := by simp [ff,cachedFrame,show 2<frame.locals.size by omega]
  have h5f : ff.locals[5]?=some (.i32 p.size) := by simp [ff,cachedFrame,show 5<frame.locals.size by omega]
  have fields := allocated_fields cfg s p
  have orig := hcode.allocation.allocation.retry.originalCode
  have jm : (joined cfg s p).modules[ff.inst]?=some p.mi := by
    rw [joined,modules_paid,cached,modules_paid,fields.2.1]
    simpa only [ff,cachedFrame,AllocatePositive.searchLayout] using orig.search.module
  have je : (joined cfg s p).mems[p.memoryIndex]?=some (resultMemory p) := by
    rw [joined,mems_paid,cached,mems_paid];exact allocated_memory cfg s p hm
  have jg : (joined cfg s p).globals[p.globalIndex]?=some {p.outerGlobal with value:=.i32 (reservedSP p)} := by
    rw [joined,globals_paid,cached,globals_paid,allocated_globals cfg s p hn hg]
    exact arguments_global s op p hg
  have shape := resultMemory_spec p hn
  have cn := (joined_gas cfg s p).credits (rest:=14*op+rest) (hc.mono (by simp only [bodyCost,Nat.add_mul,op];omega))
  have nxt : WP cfg fuel (.next (atCode
      (finished (paid (joined cfg s p) op 3) op p.memoryIndex p.globalIndex (resultMemory p)
        p.out686 (result p) p.size (reservedSP p)) limits base.toArray caller callers caller.code)) rest post := by
    simpa only [finished,nonzero,recorded,restored,after,reservedSP,UInt32.sub_add_cancel,op] using hnext
  have fin := wp_finish cfg fuel rest (joined cfg s p) limits base ff caller callers [] p.mi p.memoryIndex p.globalIndex
    {p.outerGlobal with value:=.i32 (reservedSP p)} (resultMemory p) p.out686 (result p) p.size (reservedSP p) post
    h0f h2f h5f h3f jm orig.search.memoryIndex je orig.globalIndex jg shape.1
    (hn.outputBound.trans shape.2.1) (result_nonzero p hn) ha hh cn nxt
  have bn : WP cfg (fuel+14) (.next (atCode (paid (allocated cfg s p) op 7) limits base.toArray
      {frame with locals:=(frame.locals.set! 5 (.i32 p.size)).set! 2 (.i32 (result p))} (caller::callers) exitCode)) (14*op+rest) post := by
    simpa only [joined,cached,paid,ff,cachedFrame,exitCode,List.append_assoc,op] using fin
  have nums := stack_numbers p hn
  have lower := hn.spLower
  have bound := hn.spBound
  have span : (reservedSP p).toNat+16≤(resultMemory p).byteSize := by rw [nums.1];omega
  have am : (allocated cfg s p).modules[frame.inst]?=some p.mi := by
    rw [fields.2.1];simpa only [AllocatePositive.searchLayout] using orig.search.module
  have ca := wp_cache_branch cfg (fuel+14) (14*op+rest) (allocated cfg s p) limits base.toArray frame (caller::callers)
    exitCode alternateCode (reservedSP p) (result p) p.size p.mi p.memoryIndex (resultMemory p) post h3 am orig.search.memoryIndex
    (allocated_memory cfg s p hm) span (result_low p hn) (result_high p hn)
    ((allocated_gas cfg s p).credits (hc.mono (by simp only [bodyCost,Nat.add_mul,op];omega))) bn
  have ce : 7*cfg.regularOpCost+(14*op+rest)=21*cfg.regularOpCost+rest := by dsimp [op];omega
  rw [ce] at ca
  simpa only [Nat.add_assoc,Nat.reduceAdd] using ca
end WNear.Proofs.AllocateVector
