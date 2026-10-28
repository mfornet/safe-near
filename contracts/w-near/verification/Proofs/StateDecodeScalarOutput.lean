import Proofs.StateDecodeScalarCache

/-! Cached scalar stores retain the actual added-address and sequential write semantics. -/
namespace WNear.Proofs.StateDecodeScalar
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode readI64 writeI64

private theorem paid_modules (s : Store NearState) (op n : Nat) : (paid s op n).modules=s.modules := by
  induction n with |zero=>rfl |succ n ih=>exact ih
private theorem paid_mems (s : Store NearState) (op n : Nat) : (paid s op n).mems=s.mems := by
  induction n with |zero=>rfl |succ n ih=>exact ih

def store64Local (s : Store NearState) (op index : Nat) (memory : Memory) (pointer : UInt32) (value : UInt64) :=
  storeI64 (paid s op 3) index pointer.toNat memory value

theorem wp_store64_local (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame) (code : Expr)
    (destination source : Nat) (pointer : UInt32) (value : UInt64) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (hp : frame.locals[destination]?=some (.i32 pointer)) (hv : frame.locals[source]?=some (.i64 value))
    (hm : s.modules[frame.inst]?=some mi) (hi : mi.memAddrs[0]?=some index) (hmem : s.mems[index]?=some memory)
    (hb : pointer.toNat+8≤memory.byteSize) (hc : s.host.gas.Credits (3*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (store64Local s cfg.regularOpCost index memory pointer value) limits stack frame callers code)) rest post) :
    WP cfg (fuel+3) (.next (atCode s limits stack frame callers
      (.local_get destination::.local_get source::.store .i64 none {align:=2,offset:=0}::code)))
      (3*cfg.regularOpCost+rest) post := by
  let op:=cfg.regularOpCost
  have st := wp_i64_store cfg fuel rest (paid s op 2) limits stack frame callers code {align:=2,offset:=0}
    pointer value mi index memory post hm hi hmem hb (paid_credits s op 2 _ (hc.mono (by dsimp[op];omega))) hnext
  have gv := wp_local_get cfg (fuel+1) (op+rest) (paid s op 1) limits (stack.push (.i32 pointer)) frame callers
    (.store .i64 none {align:=2,offset:=0}::code) source (.i64 value) post hv
    (paid_credits s op 1 _ (hc.mono (by dsimp[op];omega))) st
  have gp := wp_local_get cfg (fuel+2) (op+(op+rest)) s limits stack frame callers
    (.local_get source::.store .i64 none {align:=2,offset:=0}::code) destination (.i32 pointer) post hp
    (hc.mono (by dsimp[op];omega)) gv
  simpa only [Nat.add_assoc,Nat.reduceAdd,
    show cfg.regularOpCost+(op+(op+rest))=3*cfg.regularOpCost+rest by dsimp[op];omega] using gp

def store64Added (s : Store NearState) (op index : Nat) (memory : Memory) (pointer delta : UInt32) (value : UInt64) :=
  storeI64 (paid s op 5) index (pointer+delta).toNat memory value

theorem wp_store64_added (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame) (code : Expr)
    (destination source : Nat) (pointer delta : UInt32) (value : UInt64)
    (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (hp : frame.locals[destination]?=some (.i32 pointer)) (hv : frame.locals[source]?=some (.i64 value))
    (hm : s.modules[frame.inst]?=some mi) (hi : mi.memAddrs[0]?=some index) (hmem : s.mems[index]?=some memory)
    (hb : (pointer+delta).toNat+8≤memory.byteSize) (hc : s.host.gas.Credits (5*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (store64Added s cfg.regularOpCost index memory pointer delta value) limits stack frame callers code)) rest post) :
    WP cfg (fuel+5) (.next (atCode s limits stack frame callers
      (.local_get destination::.i32_const delta::.i32_binop .add::.local_get source::.store .i64 none {align:=3,offset:=0}::code)))
      (5*cfg.regularOpCost+rest) post := by
  let op:=cfg.regularOpCost
  have mm : (paid s op 4).modules[frame.inst]?=some mi := by rw [paid_modules];exact hm
  have me : (paid s op 4).mems[index]?=some memory := by rw [paid_mems];exact hmem
  have st := wp_i64_store cfg fuel rest (paid s op 4) limits stack frame callers code {align:=3,offset:=0}
    (pointer+delta) value mi index memory post mm hi me hb (paid_credits s op 4 _ (hc.mono (by dsimp[op];omega))) hnext
  have gv := wp_local_get cfg (fuel+1) (op+rest) (paid s op 3) limits (stack.push (.i32 (pointer+delta))) frame callers
    (.store .i64 none {align:=3,offset:=0}::code) source (.i64 value) post hv
    (paid_credits s op 3 _ (hc.mono (by dsimp[op];omega))) st
  have add := wp_i32_add cfg (fuel+2) (op+(op+rest)) (paid s op 2) limits stack frame callers
    (.local_get source::.store .i64 none {align:=3,offset:=0}::code) pointer delta post
    (paid_credits s op 2 _ (hc.mono (by dsimp[op];omega))) gv
  have constant := wp_i32_const cfg (fuel+3) (op+(op+(op+rest))) (paid s op 1) limits (stack.push (.i32 pointer)) frame callers
    (.i32_binop .add::.local_get source::.store .i64 none {align:=3,offset:=0}::code) delta post
    (paid_credits s op 1 _ (hc.mono (by dsimp[op];omega))) add
  have get := wp_local_get cfg (fuel+4) (op+(op+(op+(op+rest)))) s limits stack frame callers
    (.i32_const delta::.i32_binop .add::.local_get source::.store .i64 none {align:=3,offset:=0}::code) destination (.i32 pointer) post hp
    (hc.mono (by dsimp[op];omega)) constant
  simpa only [Nat.add_assoc,Nat.reduceAdd,
    show cfg.regularOpCost+(op+(op+(op+(op+rest))))=5*cfg.regularOpCost+rest by dsimp[op];omega] using get
end WNear.Proofs.StateDecodeScalar
