import Proofs.StateDecodeScalarOutput

/-! Actual f372/f371 caller output writes use only already cached scalar words. -/
namespace WNear.Proofs.StateDecodeScalar
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode readI64 writeI64 store64Added

def firstValueMemory (memory : Memory) (out : UInt32) (value : UInt64) := writeI64 memory (out+16).toNat value
def valuesStore (wide : Bool) (s : Store NearState) (op index : Nat) (memory : Memory) (out : UInt32) (four five : UInt64) :=
  if wide then store64Added (store64Added s op index memory out 16 four) op index (firstValueMemory memory out four) out 8 five
  else store64Added s op index memory out 8 four

private theorem paid_modules (s : Store NearState) (op n : Nat) : (paid s op n).modules=s.modules := by
  induction n with |zero=>rfl |succ n ih=>exact ih
private theorem paid_mems (s : Store NearState) (op n : Nat) : (paid s op n).mems=s.mems := by
  induction n with |zero=>rfl |succ n ih=>exact ih

theorem wp_output_wide (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame) (code : Expr)
    (out : UInt32) (four five : UInt64) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (h0 : frame.locals[0]?=some (.i32 out)) (h4 : frame.locals[4]?=some (.i64 four)) (h5 : frame.locals[5]?=some (.i64 five))
    (hm : s.modules[frame.inst]?=some mi) (hi : mi.memAddrs[0]?=some index) (hmem : s.mems[index]?=some memory)
    (hw : memory.wf) (hb16 : (out+16).toNat+8≤memory.byteSize) (hb8 : (out+8).toNat+8≤memory.byteSize)
    (hc : s.host.gas.Credits (10*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (valuesStore true s cfg.regularOpCost index memory out four five)
      limits stack frame callers code)) rest post) :
    WP cfg (fuel+10) (.next (atCode s limits stack frame callers
      (WNear.Binary.StateDecodeScalar.outputValues true++code))) (10*cfg.regularOpCost+rest) post := by
  let op:=cfg.regularOpCost
  let first:=store64Added s op index memory out 16 four
  have fm : first.mems[index]?=some (firstValueMemory memory out four) := by
    have before : (paid s op 5).mems[index]?=some memory := by rw [paid_mems];exact hmem
    unfold first store64Added firstValueMemory
    exact storeI64_memory (paid s op 5) index (out+16).toNat memory four before
  have mm : first.modules[frame.inst]?=some mi := by
    unfold first store64Added
    rw [storeI64_modules,paid_modules];exact hm
  have shape := writeI64_spec memory (out+16).toNat four hw hb16
  have bound : (out+8).toNat+8≤(firstValueMemory memory out four).byteSize := by
    unfold firstValueMemory
    rw [shape.2.1];exact hb8
  have credits : first.host.gas.Credits (5*op+rest) := by
    unfold first store64Added
    rw [storeI64_host]
    exact paid_credits s op 5 _ (hc.mono (by dsimp[op];omega))
  have low := wp_store64_added cfg fuel rest first limits stack frame callers code 0 5 out 8 five mi index
    (firstValueMemory memory out four) post h0 h5 mm hi fm bound credits
    (by simpa only [valuesStore,ite_true,first,op] using hnext)
  have high := wp_store64_added cfg (fuel+5) (5*op+rest) s limits stack frame callers
    ([.local_get 0,.i32_const 8,.i32_binop .add,.local_get 5,.store .i64 none {align:=3,offset:=0}]++code)
    0 4 out 16 four mi index memory post h0 h4 hm hi hmem hb16
    (hc.mono (by dsimp[op];omega))
    (by simpa only [first,List.cons_append,List.nil_append] using low)
  simpa only [WNear.Binary.StateDecodeScalar.outputValues,ite_true,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd,
    show 5*cfg.regularOpCost+(5*op+rest)=10*cfg.regularOpCost+rest by dsimp[op];omega] using high

theorem wp_output_narrow (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame) (code : Expr)
    (out : UInt32) (four five : UInt64) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (h0 : frame.locals[0]?=some (.i32 out)) (h4 : frame.locals[4]?=some (.i64 four))
    (hm : s.modules[frame.inst]?=some mi) (hi : mi.memAddrs[0]?=some index) (hmem : s.mems[index]?=some memory)
    (hb : (out+8).toNat+8≤memory.byteSize) (hc : s.host.gas.Credits (5*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (valuesStore false s cfg.regularOpCost index memory out four five)
      limits stack frame callers code)) rest post) :
    WP cfg (fuel+5) (.next (atCode s limits stack frame callers
      (WNear.Binary.StateDecodeScalar.outputValues false++code))) (5*cfg.regularOpCost+rest) post := by
  have step := wp_store64_added cfg fuel rest s limits stack frame callers code 0 4 out 8 four mi index memory post h0 h4 hm hi hmem hb hc hnext
  simpa only [WNear.Binary.StateDecodeScalar.outputValues,Bool.false_eq_true,ite_false,List.cons_append,List.nil_append] using step
end WNear.Proofs.StateDecodeScalar
