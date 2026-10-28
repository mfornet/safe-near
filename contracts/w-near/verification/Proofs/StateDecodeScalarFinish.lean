import Proofs.StateDecodeScalarUpdate
import Proofs.InterfaceStack
import NearVM.MeteredI32MemoryRules

/-! Actual success tag store and shadow-stack restoration before explicit return. -/
namespace WNear.Proofs.StateDecodeScalar
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode

def tagStore (s : Store NearState) (op index : Nat) (memory : Memory) (out : UInt32) :=
  storeI32 (paid s op 3) index out.toNat memory 0
def finishStore (s : Store NearState) (op memoryIndex globalIndex : Nat) (memory : Memory) (out scratch : UInt32) :=
  setGlobal (paid (tagStore s op memoryIndex memory out) op 4) globalIndex (.i32 (scratch+48))
private theorem paid_modules (s : Store NearState) (op n : Nat) : (paid s op n).modules=s.modules := by
  induction n with |zero=>rfl |succ n ih=>exact ih
private theorem paid_globals (s : Store NearState) (op n : Nat) : (paid s op n).globals=s.globals := by
  induction n with |zero=>rfl |succ n ih=>exact ih

theorem wp_finish_prefix (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame) (code : Expr)
    (out scratch : UInt32) (mi : ModuleInst) (memoryIndex globalIndex : Nat) (memory : Memory) (global : GlobalInst) (post : Post)
    (h0 : frame.locals[0]?=some (.i32 out)) (h1 : frame.locals[1]?=some (.i32 0)) (h2 : frame.locals[2]?=some (.i32 scratch))
    (hm : s.modules[frame.inst]?=some mi) (hmi : mi.memAddrs[0]?=some memoryIndex)
    (hgi : mi.globalAddrs[0]?=some globalIndex) (hmem : s.mems[memoryIndex]?=some memory)
    (hg : s.globals[globalIndex]?=some global) (hb : out.toNat+4≤memory.byteSize)
    (hc : s.host.gas.Credits (7*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (finishStore s cfg.regularOpCost memoryIndex globalIndex memory out scratch)
      limits stack frame callers (.return::code))) rest post) :
    WP cfg (fuel+7) (.next (atCode s limits stack frame callers
      (WNear.Binary.StateDecodeScalar.finish++code))) (7*cfg.regularOpCost+rest) post := by
  let op:=cfg.regularOpCost
  let tagged:=tagStore s op memoryIndex memory out
  have mm : tagged.modules[frame.inst]?=some mi := by
    unfold tagged tagStore
    rw [storeI32_modules,paid_modules];exact hm
  have gg : tagged.globals[globalIndex]?=some global := by
    unfold tagged tagStore
    rw [storeI32_globals,paid_globals];exact hg
  have ct : tagged.host.gas.Credits (4*op+rest) := by
    unfold tagged tagStore
    rw [storeI32_host]
    exact paid_credits s op 3 _ (hc.mono (by dsimp[op];omega))
  have restore := InterfaceStack.wp_restore cfg fuel rest tagged limits stack frame callers (.return::code)
    mi globalIndex global scratch 2 48 post h2 mm hgi gg ct hnext
  have ms : (paid s op 2).modules[frame.inst]?=some mi := by rw [paid_modules];exact hm
  have before : (paid s op 2).mems[memoryIndex]?=some memory := by
    simp only [paid,chargedStore];exact hmem
  have store := wp_i32_store cfg (fuel+4) (4*op+rest) (paid s op 2) limits stack frame callers
    ([.local_get 2,.i32_const 48,.i32_binop .add,.global_set 0,.return]++code)
    {align:=2,offset:=0} out 0 mi memoryIndex memory post ms hmi before hb
    (paid_credits s op 2 _ (hc.mono (by dsimp[op];omega)))
    (by simpa only [tagged,tagStore,paid,op,Nat.add_zero,List.cons_append,List.nil_append] using restore)
  have zero := wp_local_get cfg (fuel+5) (op+(4*op+rest)) (paid s op 1) limits (stack.push (.i32 out)) frame callers
    (.store .i32 none {align:=2,offset:=0}::[.local_get 2,.i32_const 48,.i32_binop .add,.global_set 0,.return]++code)
    1 (.i32 0) post h1 (paid_credits s op 1 _ (hc.mono (by dsimp[op];omega)))
    (by simpa only [paid,op,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd] using store)
  have outGet := wp_local_get cfg (fuel+6) (op+(op+(4*op+rest))) s limits stack frame callers
    (.local_get 1::.store .i32 none {align:=2,offset:=0}::[.local_get 2,.i32_const 48,.i32_binop .add,.global_set 0,.return]++code)
    0 (.i32 out) post h0 (hc.mono (by dsimp[op];omega))
    (by simpa only [paid,op,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd] using zero)
  simpa only [WNear.Binary.StateDecodeScalar.finish,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd,
    show cfg.regularOpCost+(op+(op+(4*op+rest)))=7*cfg.regularOpCost+rest by dsimp[op];omega] using outGet
end WNear.Proofs.StateDecodeScalar
