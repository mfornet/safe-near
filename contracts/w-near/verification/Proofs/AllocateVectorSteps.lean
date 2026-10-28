import Binary.AllocateVector
import Proofs.AllocateRecordCopySteps

/-! Small pure instruction groups of686, before allocator state is instantiated. -/
namespace WNear.Proofs.AllocateVector
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode readI32 writeI32
private theorem modules_paid (s : Store NearState) (op n : Nat) : (paid s op n).modules=s.modules := by
  induction n with | zero=>rfl | succ n ih=>exact ih
private theorem mems_paid (s : Store NearState) (op n : Nat) : (paid s op n).mems=s.mems := by
  induction n with | zero=>rfl | succ n ih=>exact ih

def loadedFrame (frame : CallFrame) (target : Nat) (value : UInt32) :=
  {frame with locals:=frame.locals.set! target (.i32 value)}

theorem wp_load_local (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (sourceSlot target offset : Nat) (source : UInt32)
    (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (hl : frame.locals[sourceSlot]?=some (.i32 source))
    (hm : s.modules[frame.inst]?=some mi) (hi : mi.memAddrs[0]?=some index)
    (hmem : s.mems[index]?=some memory) (hb : source.toNat+offset+4≤memory.byteSize)
    (hc : s.host.gas.Credits (3*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 3) limits stack
      (loadedFrame frame target (readI32 memory (source.toNat+offset))) callers code)) rest post) :
    WP cfg (fuel+3) (.next (atCode s limits stack frame callers
      ([.local_get sourceSlot,.load .i32 none {align:=2,offset},.local_set target]++code)))
      (3*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  have sm : WP cfg fuel (.next (atCode (paid s op 3) limits stack
      {frame with locals:=frame.locals.set! target (.i32 (readI32 memory (source.toNat+offset)))} callers code)) rest post := hnext
  have ls := wp_local_set cfg fuel rest (paid s op 2) limits stack frame callers code target
    (.i32 (readI32 memory (source.toNat+offset))) post
    (paid_credits s op 2 _ (hc.mono (by dsimp [op];omega))) sm
  have mm : (paid s op 1).modules[frame.inst]?=some mi := by rw [modules_paid];exact hm
  have me : (paid s op 1).mems[index]?=some memory := by rw [mems_paid];exact hmem
  have ld := wp_i32_load cfg (fuel+1) (op+rest) (paid s op 1) limits stack frame callers
    (.local_set target::code) {align:=2,offset} source mi index memory post mm hi me hb
    (paid_credits s op 1 _ (hc.mono (by dsimp [op];omega))) ls
  have g := wp_local_get cfg (fuel+2) (op+(op+rest)) s limits stack frame callers
    (.load .i32 none {align:=2,offset}::.local_set target::code) sourceSlot (.i32 source) post hl
    (hc.mono (by dsimp [op];omega)) ld
  simpa only [List.cons_append,List.nil_append,
    show cfg.regularOpCost+(op+(op+rest))=3*cfg.regularOpCost+rest by dsimp [op];omega] using g

def recordMemory (memory : Memory) (out pointer size : UInt32) :=
  writeI32 (writeI32 memory out.toNat pointer) (out.toNat+4) size

def recordStore (s : Store NearState) (op index : Nat) (memory : Memory) (out pointer size : UInt32) :=
  storeI32 (paid (storeI32 (paid s op 3) index out.toNat memory pointer) op 3)
    index (out.toNat+4) (writeI32 memory out.toNat pointer) size

theorem wp_record (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (mi : ModuleInst) (index : Nat) (memory : Memory) (out pointer size : UInt32) (post : Post)
    (h0 : frame.locals[0]?=some (.i32 out)) (h2 : frame.locals[2]?=some (.i32 pointer))
    (h5 : frame.locals[5]?=some (.i32 size)) (hm : s.modules[frame.inst]?=some mi)
    (hi : mi.memAddrs[0]?=some index) (hmem : s.mems[index]?=some memory)
    (hw : memory.wf) (hb : out.toNat+8≤memory.byteSize)
    (hc : s.host.gas.Credits (6*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (recordStore s cfg.regularOpCost index memory out pointer size)
      limits stack frame callers code)) rest post) :
    WP cfg (fuel+6) (.next (atCode s limits stack frame callers
      (WNear.Binary.AllocateVector.record++code))) (6*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  let low := storeI32 (paid s op 3) index out.toNat memory pointer
  let written := writeI32 memory out.toNat pointer
  have spec := writeI32_spec memory out.toNat pointer hw (by omega)
  have m3 : (paid s op 3).mems[index]?=some memory := by rw [mems_paid];exact hmem
  have mm : low.mems[index]?=some written := storeI32_memory _ _ _ _ _ m3
  have hm2 : (paid s op 2).modules[frame.inst]?=some mi := by rw [modules_paid];exact hm
  have hm5 : (paid low op 2).modules[frame.inst]?=some mi := by rw [modules_paid,show low.modules=s.modules by simp only [low,storeI32_modules,modules_paid]];exact hm
  have mm2 : (paid s op 2).mems[index]?=some memory := by rw [mems_paid];exact hmem
  have mm5 : (paid low op 2).mems[index]?=some written := by rw [mems_paid];exact mm
  have c3 : low.host.gas.Credits (3*op+rest) := paid_credits s op 3 _ (hc.mono (by dsimp [op];omega))
  have sn : WP cfg fuel (.next (atCode (storeI32 (paid low op 3) index (out.toNat+4) written size)
      limits stack frame callers code)) rest post := by simpa only [recordStore,low,written,op] using hnext
  have store := wp_i32_store cfg fuel rest (paid low op 2) limits stack frame callers code {align:=2,offset:=4}
    out size mi index written post hm5 hi mm5 (by change out.toNat+4+4≤written.byteSize;rw [spec.2.1];omega)
    (paid_credits low op 2 _ (c3.mono (by omega))) sn
  have g5 := wp_local_get cfg (fuel+1) (op+rest) (paid low op 1) limits (stack.push (.i32 out)) frame callers
    (.store .i32 none {align:=2,offset:=4}::code) 5 (.i32 size) post h5
    (paid_credits low op 1 _ (c3.mono (by omega))) store
  have g0 := wp_local_get cfg (fuel+2) (op+(op+rest)) low limits stack frame callers
    (.local_get 5::.store .i32 none {align:=2,offset:=4}::code) 0 (.i32 out) post h0 (c3.mono (by omega)) g5
  have hn : WP cfg (fuel+3) (.next (atCode low limits stack frame callers
      (.local_get 0::.local_get 5::.store .i32 none {align:=2,offset:=4}::code))) (3*op+rest) post := by
    simpa only [show cfg.regularOpCost+(op+(op+rest))=3*op+rest by dsimp [op];omega] using g0
  have lowStore := wp_i32_store cfg (fuel+3) (3*op+rest) (paid s op 2) limits stack frame callers
    (.local_get 0::.local_get 5::.store .i32 none {align:=2,offset:=4}::code) {align:=2,offset:=0}
    out pointer mi index memory post hm2 hi mm2 (by change out.toNat+0+4≤memory.byteSize;omega) (paid_credits s op 2 _ (hc.mono (by dsimp [op];omega))) hn
  have low1 := wp_local_get cfg (fuel+4) (op+(3*op+rest)) (paid s op 1) limits (stack.push (.i32 out)) frame callers
    (.store .i32 none {align:=2,offset:=0}::.local_get 0::.local_get 5::.store .i32 none {align:=2,offset:=4}::code)
    2 (.i32 pointer) post h2 (paid_credits s op 1 _ (hc.mono (by dsimp [op];omega))) lowStore
  have low0 := wp_local_get cfg (fuel+5) (op+(op+(3*op+rest))) s limits stack frame callers
    (.local_get 2::.store .i32 none {align:=2,offset:=0}::.local_get 0::.local_get 5::.store .i32 none {align:=2,offset:=4}::code)
    0 (.i32 out) post h0 (hc.mono (by dsimp [op];omega)) low1
  have ce : cfg.regularOpCost+(op+(op+(3*op+rest)))=6*cfg.regularOpCost+rest := by dsimp [op];omega
  simpa only [ce,WNear.Binary.AllocateVector.record,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd] using low0
end WNear.Proofs.AllocateVector
