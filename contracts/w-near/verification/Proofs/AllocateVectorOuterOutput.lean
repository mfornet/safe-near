import Binary.AllocateVectorOuter
import NearVM.MeteredI32MemoryRules
import NearVM.MeteredMemoryRules
import Proofs.StorePairCaller

/-! The two actual f687 output stores use an already cached eight-byte record. -/
namespace WNear.Proofs.AllocateVectorOuter
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384

def highStore (s : Store NearState) (op index : Nat) (memory : Memory) (out count : UInt32) :=
  storeI32 (paid s op 3) index (out.toNat+8) memory count
def outputMemory (memory : Memory) (out count : UInt32) (cached : UInt64) :=
  writeI64 (writeI32 memory (out.toNat+8) count) out.toNat cached
def outputAfter (s : Store NearState) (op index : Nat) (memory : Memory) (out count : UInt32) (cached : UInt64) :=
  storeI64 (paid (highStore s op index memory out count) op 3) index out.toNat
    (writeI32 memory (out.toNat+8) count) cached

private theorem mems_paid (s : Store NearState) (op n : Nat) : (paid s op n).mems=s.mems := by
  induction n with | zero=>rfl | succ n ih=>exact ih
private theorem modules_paid (s : Store NearState) (op n : Nat) : (paid s op n).modules=s.modules := by
  induction n with | zero=>rfl | succ n ih=>exact ih

theorem wp_output (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (mi : ModuleInst) (index : Nat) (memory : Memory)
    (out count : UInt32) (cached : UInt64) (post : Post)
    (h0 : frame.locals[0]?=some (.i32 out)) (h2 : frame.locals[2]?=some (.i32 count))
    (h4 : frame.locals[4]?=some (.i64 cached))
    (hm : s.modules[frame.inst]?=some mi) (hi : mi.memAddrs[0]?=some index)
    (hmem : s.mems[index]?=some memory) (hw : memory.wf) (hb : out.toNat+12≤memory.byteSize)
    (hc : s.host.gas.Credits (6*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (outputAfter s cfg.regularOpCost index memory out count cached)
      limits stack frame callers code)) rest post) :
    WP cfg (fuel+6) (.next (atCode s limits stack frame callers (WNear.Binary.AllocateVectorOuter.output++code)))
      (6*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  let high := highStore s op index memory out count
  let memory1 := writeI32 memory (out.toNat+8) count
  have spec := writeI32_spec memory (out.toNat+8) count hw (by omega)
  have lowBound : out.toNat+0+8≤memory1.byteSize := by dsimp [memory1];rw [spec.2.1];omega
  have highMemory : high.mems[index]?=some memory1 := by
    unfold high highStore memory1
    apply storeI32_memory
    rw [mems_paid];exact hmem
  have highModule : high.modules[frame.inst]?=some mi := by
    simpa only [high,highStore,storeI32_modules,modules_paid] using hm
  have highCredit : high.host.gas.Credits (3*op+rest) := paid_credits s op 3 _ (hc.mono (by dsimp [op];omega))
  have nextLow : WP cfg fuel (.next (atCode (storeI64 (chargedStore (paid high op 2) cfg.regularOpCost)
      index (out.toNat+0) memory1 cached) limits stack frame callers code)) rest post := by
    simpa only [outputAfter,high,memory1,paid,op,Nat.add_zero] using hnext
  have low := wp_i64_store cfg fuel rest (paid high op 2) limits stack frame callers code {align:=2,offset:=0}
    out cached mi index memory1 post (by rw [modules_paid];exact highModule) hi
    (by rw [mems_paid];exact highMemory) lowBound
    (paid_credits high op 2 _ (highCredit.mono (by dsimp [op];omega))) nextLow
  have get4 := wp_local_get cfg (fuel+1) (op+rest) (paid high op 1) limits (stack.push (.i32 out)) frame callers
    (.store .i64 none {align:=2,offset:=0}::code) 4 (.i64 cached) post h4
    (paid_credits high op 1 _ (highCredit.mono (by dsimp [op];omega))) low
  have get0 := wp_local_get cfg (fuel+2) (op+(op+rest)) high limits stack frame callers
    (.local_get 4::.store .i64 none {align:=2,offset:=0}::code) 0 (.i32 out) post h0
    (highCredit.mono (by dsimp [op];omega)) get4
  have nextHigh : WP cfg (fuel+3) (.next (atCode (storeI32 (chargedStore (paid s op 2) cfg.regularOpCost)
      index (out.toNat+8) memory count) limits stack frame callers
      (.local_get 0::.local_get 4::.store .i64 none {align:=2,offset:=0}::code))) (3*op+rest) post := by
    have ce : cfg.regularOpCost+(op+(op+rest))=3*op+rest := by dsimp [op];omega
    simpa only [high,highStore,paid,op,ce,Nat.add_assoc,Nat.reduceAdd] using get0
  have highWrite := wp_i32_store cfg (fuel+3) (3*op+rest) (paid s op 2) limits stack frame callers
    (.local_get 0::.local_get 4::.store .i64 none {align:=2,offset:=0}::code) {align:=2,offset:=8}
    out count mi index memory post (by rw [modules_paid];exact hm) hi (by rw [mems_paid];exact hmem) (by omega)
    (paid_credits s op 2 _ (hc.mono (by dsimp [op];omega))) nextHigh
  have g2 := wp_local_get cfg (fuel+4) (op+(3*op+rest)) (paid s op 1) limits (stack.push (.i32 out)) frame callers
    (.store .i32 none {align:=2,offset:=8}::.local_get 0::.local_get 4::.store .i64 none {align:=2,offset:=0}::code)
    2 (.i32 count) post h2 (paid_credits s op 1 _ (hc.mono (by dsimp [op];omega))) highWrite
  have g0 := wp_local_get cfg (fuel+5) (op+(op+(3*op+rest))) s limits stack frame callers
    (.local_get 2::.store .i32 none {align:=2,offset:=8}::.local_get 0::.local_get 4::.store .i64 none {align:=2,offset:=0}::code)
    0 (.i32 out) post h0 (hc.mono (by dsimp [op];omega)) g2
  have ce : cfg.regularOpCost+(op+(op+(3*op+rest)))=6*cfg.regularOpCost+rest := by dsimp [op];omega
  rw [ce] at g0
  simpa only [WNear.Binary.AllocateVectorOuter.output,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd] using g0
end WNear.Proofs.AllocateVectorOuter
