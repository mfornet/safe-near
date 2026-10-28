import Proofs.StateDecodeRawAllocateCall
import Proofs.StateDecodeRawRecordSteps
import Proofs.AllocatePositivePayload

/-! Complete selected f770 body, including both real block entries, actual310
allocation, the normal outer-block end, and ordered record writes. -/
namespace WNear.Proofs.StateDecodeRaw
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
open AllocateSearch (GasUnits gasUnits_paid)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode recordInput allocatedRecord AllocateRawForwardDirect.callAfter310 AllocatePositive.finalMemory

def recordAfter (cfg : WasmConfig) (s : Store NearState) (q : AllocatePositive.Layout) (out : UInt32) :=
  recordStore (recordInput cfg (paid s cfg.regularOpCost 6) q) cfg.regularOpCost q.memoryIndex
    (AllocatePositive.finalMemory q) out q.size (AllocatePositive.result q)

private theorem mems_paid (s : Store NearState) (op n : Nat) : (paid s op n).mems=s.mems := by
  induction n with |zero=>rfl|succ n ih=>exact ih
private theorem modules_paid (s : Store NearState) (op n : Nat) : (paid s op n).modules=s.modules := by
  induction n with |zero=>rfl|succ n ih=>exact ih
private theorem globals_paid (s : Store NearState) (op n : Nat) : (paid s op n).globals=s.globals := by
  induction n with |zero=>rfl|succ n ih=>exact ih
private theorem paid_add (s : Store NearState) (op a b : Nat) : paid (paid s op a) op b=paid s op (a+b) := by
  induction b with |zero=>rfl|succ b ih=>exact congrArg (fun t=>chargedStore t op) ih

theorem recordInput_gas (cfg : WasmConfig) (s : Store NearState) (q : AllocatePositive.Layout) :
    GasUnits s (recordInput cfg s q) cfg.regularOpCost 390 := by
  have h:=(gasUnits_paid s cfg.regularOpCost 2).trans (AllocateRawForwardDirect.callAfter310_gas cfg (paid s cfg.regularOpCost 2) q)
  have h':GasUnits s (allocatedRecord cfg s q) cfg.regularOpCost 389 := by
    simpa only[allocatedRecord,AllocateRawForwardDirect.cost310,AllocateRawForwardDirect.cost236,Nat.reduceAdd] using h
  simpa only[recordInput,Nat.reduceAdd] using h'.trans (gasUnits_paid (allocatedRecord cfg s q) cfg.regularOpCost 1)

theorem recordAfter_gas (cfg : WasmConfig) (s : Store NearState) (q : AllocatePositive.Layout) (out : UInt32) :
    GasUnits s (recordAfter cfg s q out) cfg.regularOpCost 402 := by
  have a:=(gasUnits_paid s cfg.regularOpCost 6).trans (recordInput_gas cfg (paid s cfg.regularOpCost 6) q)
  have b:=a.trans (recordStore_gas (recordInput cfg (paid s cfg.regularOpCost 6) q) cfg.regularOpCost q.memoryIndex
    (AllocatePositive.finalMemory q) out q.size (AllocatePositive.result q))
  simpa only[recordAfter,Nat.reduceAdd] using b

theorem wp_record_body (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (q : AllocatePositive.Layout) (out : UInt32) (a581 a236 a310 : Nat) (post : Post)
    (hn : AllocatePositive.Native q) (hcode : RecordCode s frame.inst q a581 a236 a310)
    (ha : q.allocator=1074896)
    (h0 : frame.locals[0]?=some (.i32 out)) (h1 : frame.locals[1]?=some (.i32 q.size))
    (h2 : frame.locals[2]?=some (.i32 1)) (h3 : frame.locals[3]?=some (.i32 0)) (hs : 4≤frame.locals.size)
    (hm : s.mems[q.memoryIndex]?=some q.memory) (hg : s.globals[q.globalIndex]?=some q.global)
    (hv : q.global.value=.i32 q.sp) (hb : out.toNat+8≤q.memory.byteSize)
    (hd : callers.length+5<limits.maxCallDepth) (hc : s.host.gas.Credits (402*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (recordAfter cfg s q out) limits base.toArray (allocationFrame frame q) callers code)) rest post) :
    WP cfg (fuel+328) (.next (atCode s limits base.toArray frame callers (WNear.Binary.StateDecodeRaw.body770++code)))
      (402*cfg.regularOpCost+rest) post := by
  let op:=cfg.regularOpCost
  let g:=paid s op 6
  let r:=recordInput cfg g q
  let af:=allocationFrame frame q
  let outer:=emptyBlockFrame frame base.toArray.size (WNear.Binary.StateDecodeRaw.recordWrites++code)
  have c6:r.host.gas.Credits (6*op+rest):=(recordInput_gas cfg g q _ (paid_credits s op 6 _ (hc.mono (by dsimp[op];omega)))).2.2
  have rm:r.mems[q.memoryIndex]?=some (AllocatePositive.finalMemory q) := by
    unfold r
    rw[recordInput,mems_paid,allocatedRecord]
    apply AllocateRawForwardDirect.callAfter310_memory
    rw[mems_paid,mems_paid];exact hm
  have rmodule:r.modules[af.inst]?=some q.mi := by
    unfold r
    rw[recordInput,modules_paid,allocatedRecord,(AllocateRawForwardDirect.callAfter310_fields cfg (paid g op 2) q).2.1,modules_paid,modules_paid]
    exact hcode.allocation.search.module
  have a0:af.locals[0]?=some (.i32 out):=by simp[af,allocationFrame,h0]
  have a1:af.locals[1]?=some (.i32 q.size):=by simp[af,allocationFrame,h1]
  have a2:af.locals[2]?=some (.i32 (AllocatePositive.result q)):=by simp[af,allocationFrame,show 2<frame.locals.size by omega]
  have shape:=AllocatePositive.finalMemory_spec q hn
  have writes:=wp_record cfg fuel rest r limits base.toArray af callers code q.mi q.memoryIndex (AllocatePositive.finalMemory q) out q.size (AllocatePositive.result q) post
    a0 a1 a2 rmodule hcode.allocation.search.memoryIndex rm shape.1 (by rw[shape.2.1];exact hb) c6
    (by simpa only[recordAfter,r,g,op] using hnext)
  have endBlock:=wp_end_label cfg (fuel+6) (6*op+rest) r limits base.toArray af callers
    {arity:=0,height:=base.toArray.size,rest:=WNear.Binary.StateDecodeRaw.recordWrites++code,loop:=none} post c6 writes
  have raw:=wp_raw_allocate cfg (fuel+7) (6*op+rest) g limits base outer callers [] q a581 a236 a310 post hn
    (hcode.paid s op 6 frame.inst q a581 a236 a310) ha h1 h2
    (by rw[mems_paid];exact hm) (by rw[globals_paid];exact hg) hv hd
    (paid_credits s op 6 _ (hc.mono (by dsimp[op];omega)))
    (by simpa only[r,af,outer,allocationFrame,emptyBlockFrame] using endBlock)
  have flag:=wp_record_flag_zero cfg (fuel+320) (396*op+rest) (paid s op 3) limits base.toArray outer callers
    WNear.Binary.StateDecodeRaw.rawCall WNear.Binary.StateDecodeRaw.zeroedCall post h3
    (paid_credits s op 3 _ (hc.mono (by dsimp[op];omega)))
    (by simpa only[g,op,paid_add,Nat.reduceAdd,List.append_nil,Nat.add_assoc,Nat.reduceAdd,
      show 390*cfg.regularOpCost+(6*op+rest)=396*op+rest by dsimp[op];omega] using raw)
  have block:=wp_block_empty cfg (fuel+323) (399*op+rest) (paid s op 3) limits base.toArray outer callers
    (WNear.Binary.StateDecodeRaw.recordFlagGuard++WNear.Binary.StateDecodeRaw.zeroedCall) WNear.Binary.StateDecodeRaw.rawCall post
    (paid_credits s op 3 _ (hc.mono (by dsimp[op];omega)))
    (by simpa only[show 3*cfg.regularOpCost+(396*op+rest)=399*op+rest by dsimp[op];omega] using flag)
  have guard:=wp_nonzero_guard cfg (fuel+324) (399*op+rest) s limits base.toArray outer callers
    (.block .empty (WNear.Binary.StateDecodeRaw.recordFlagGuard++WNear.Binary.StateDecodeRaw.zeroedCall)::WNear.Binary.StateDecodeRaw.rawCall)
    q.size post h1 hn.positive (hc.mono (by dsimp[op];omega)) block
  have entry:=wp_block_empty cfg (fuel+327) (402*op+rest) s limits base.toArray frame callers
    (WNear.Binary.StateDecodeRaw.nonzeroGuard++[.block .empty (WNear.Binary.StateDecodeRaw.recordFlagGuard++WNear.Binary.StateDecodeRaw.zeroedCall)]++WNear.Binary.StateDecodeRaw.rawCall)
    (WNear.Binary.StateDecodeRaw.recordWrites++code) post hc
    (by simpa only[outer,List.append_assoc,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd,show 3*cfg.regularOpCost+(399*op+rest)=402*op+rest by dsimp[op];omega] using guard)
  simpa only[WNear.Binary.StateDecodeRaw.body770,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd] using entry
end WNear.Proofs.StateDecodeRaw
