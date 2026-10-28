import Proofs.AllocateRecordState
import NearVM.MeteredSelectionRules

/-! Actual pure689 guard and two sequential result-word stores. -/
namespace WNear.Proofs.AllocateRecord
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode writeI32
private theorem modules_paid (s : Store NearState) (op n : Nat) : (paid s op n).modules=s.modules := by
  induction n with | zero=>rfl | succ n ih=>exact ih
private theorem mems_paid (s : Store NearState) (op n : Nat) : (paid s op n).mems=s.mems := by
  induction n with | zero=>rfl | succ n ih=>exact ih

theorem wp_nonzero_guard (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (index : Nat) (value : UInt32) (post : Post)
    (hl : frame.locals[index]?=some (.i32 value)) (hn : value≠0)
    (hc : s.host.gas.Credits (3*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 3) limits stack frame callers code)) rest post) :
    WP cfg (fuel+3) (.next (atCode s limits stack frame callers
      (.local_get index::.i32_eqz::.br_if 0::code))) (3*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  have branch := wp_br_if_zero cfg fuel rest (paid s op 2) limits stack frame callers code 0 post
    (paid_credits s op 2 _ (hc.mono (by dsimp [op];omega))) hnext
  have eqz := wp_i32_eqz cfg (fuel+1) (op+rest) (paid s op 1) limits stack frame callers (.br_if 0::code) value post
    (paid_credits s op 1 _ (hc.mono (by dsimp [op];omega)))
    (by simpa only [Numeric.bool,show (value==0)=false from beq_eq_false_iff_ne.mpr hn,Bool.false_eq_true,ite_false,paid,op] using branch)
  have get := wp_local_get cfg (fuel+2) (op+(op+rest)) s limits stack frame callers (.i32_eqz::.br_if 0::code)
    index (.i32 value) post hl (hc.mono (by dsimp [op];omega)) eqz
  have ce : cfg.regularOpCost+(op+(op+rest))=3*cfg.regularOpCost+rest := by dsimp [op];omega
  simpa only [ce,Nat.add_assoc,Nat.reduceAdd] using get

theorem wp_record (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (mi : ModuleInst) (index : Nat) (memory : Memory) (out pointer size : UInt32) (post : Post)
    (h0 : frame.locals[0]?=some (.i32 out)) (h1 : frame.locals[1]?=some (.i32 size))
    (h2 : frame.locals[2]?=some (.i32 pointer)) (hm : s.modules[frame.inst]?=some mi)
    (hi : mi.memAddrs[0]?=some index) (hmem : s.mems[index]?=some memory)
    (hw : memory.wf) (hb : out.toNat+8≤memory.byteSize)
    (hc : s.host.gas.Credits (6*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (recordStore s cfg.regularOpCost index memory out pointer size)
      limits stack frame callers code)) rest post) :
    WP cfg (fuel+6) (.next (atCode s limits stack frame callers
      (WNear.Binary.AllocateRecord.record++code))) (6*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  let high := storeI32 (paid s op 3) index (out.toNat+4) memory size
  let written := writeI32 memory (out.toNat+4) size
  have spec := writeI32_spec memory (out.toNat+4) size hw (by omega)
  have m3 : (paid s op 3).mems[index]?=some memory := by rw [mems_paid];exact hmem
  have mm : high.mems[index]?=some written := storeI32_memory _ _ _ _ _ m3
  have hm2 : (paid s op 2).modules[frame.inst]?=some mi := by rw [modules_paid];exact hm
  have hm5 : (paid high op 2).modules[frame.inst]?=some mi := by rw [modules_paid,show high.modules=s.modules by simp only [high,storeI32_modules,modules_paid]];exact hm
  have mm2 : (paid s op 2).mems[index]?=some memory := by rw [mems_paid];exact hmem
  have mm5 : (paid high op 2).mems[index]?=some written := by rw [mems_paid];exact mm
  have c3 : high.host.gas.Credits (3*op+rest) := paid_credits s op 3 _ (hc.mono (by dsimp [op];omega))
  have sn : WP cfg fuel (.next (atCode (storeI32 (paid high op 3) index out.toNat written pointer)
      limits stack frame callers code)) rest post := by simpa only [recordStore,high,written,op] using hnext
  have store := wp_i32_store cfg fuel rest (paid high op 2) limits stack frame callers code {align:=2,offset:=0}
    out pointer mi index written post hm5 hi mm5 (by change out.toNat+0+4≤written.byteSize;rw [spec.2.1];omega)
    (paid_credits high op 2 _ (c3.mono (by omega))) sn
  have g2 := wp_local_get cfg (fuel+1) (op+rest) (paid high op 1) limits (stack.push (.i32 out)) frame callers
    (.store .i32 none {align:=2,offset:=0}::code) 2 (.i32 pointer) post h2
    (paid_credits high op 1 _ (c3.mono (by omega))) store
  have g0 := wp_local_get cfg (fuel+2) (op+(op+rest)) high limits stack frame callers
    (.local_get 2::.store .i32 none {align:=2,offset:=0}::code) 0 (.i32 out) post h0 (c3.mono (by omega)) g2
  have hn : WP cfg (fuel+3) (.next (atCode high limits stack frame callers
      (.local_get 0::.local_get 2::.store .i32 none {align:=2,offset:=0}::code))) (3*op+rest) post := by
    simpa only [show cfg.regularOpCost+(op+(op+rest))=3*op+rest by dsimp [op];omega] using g0
  have highStore := wp_i32_store cfg (fuel+3) (3*op+rest) (paid s op 2) limits stack frame callers
    (.local_get 0::.local_get 2::.store .i32 none {align:=2,offset:=0}::code) {align:=2,offset:=4}
    out size mi index memory post hm2 hi mm2 (by omega) (paid_credits s op 2 _ (hc.mono (by dsimp [op];omega))) hn
  have high1 := wp_local_get cfg (fuel+4) (op+(3*op+rest)) (paid s op 1) limits (stack.push (.i32 out)) frame callers
    (.store .i32 none {align:=2,offset:=4}::.local_get 0::.local_get 2::.store .i32 none {align:=2,offset:=0}::code)
    1 (.i32 size) post h1 (paid_credits s op 1 _ (hc.mono (by dsimp [op];omega))) highStore
  have high0 := wp_local_get cfg (fuel+5) (op+(op+(3*op+rest))) s limits stack frame callers
    (.local_get 1::.store .i32 none {align:=2,offset:=4}::.local_get 0::.local_get 2::.store .i32 none {align:=2,offset:=0}::code)
    0 (.i32 out) post h0 (hc.mono (by dsimp [op];omega)) high1
  have ce : cfg.regularOpCost+(op+(op+(3*op+rest)))=6*cfg.regularOpCost+rest := by dsimp [op];omega
  simpa only [ce,WNear.Binary.AllocateRecord.record,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd] using high0
end WNear.Proofs.AllocateRecord
