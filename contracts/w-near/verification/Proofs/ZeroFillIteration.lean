import Binary.ZeroFill
import NearVM.MeteredByteMemoryRules
import NearVM.MeteredScalarRules
import NearVM.MeteredLoopRules
import Proofs.StorePairCallerState

/-! The actual f952 byte write and pointer/count update, before its branch. -/
namespace WNear.Proofs.ZeroFill
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
attribute [local irreducible] WP atCode
set_option maxRecDepth 16384

def nextCount (count : UInt32) := count+4294967295
def written (s : Store NearState) (op index : Nat) (memory : Memory) (ptr value : UInt32) :=
  storeByte (paid s op 3) index ptr.toNat memory value
def iterationStore (s : Store NearState) (op index : Nat) (memory : Memory) (ptr value : UInt32) :=
  paid (written s op index memory ptr value) op 8
def pointerFrame (frame : CallFrame) (ptr : UInt32) := {frame with locals:=frame.locals.set! 3 (.i32 (ptr+1))}
def iterationFrame (frame : CallFrame) (ptr count : UInt32) :=
  {pointerFrame frame ptr with locals:=(pointerFrame frame ptr).locals.set! 2 (.i32 (nextCount count))}

private theorem wp_update (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (ptr count : UInt32) (post : Post)
    (h2 : frame.locals[2]? = some (.i32 count)) (h3 : frame.locals[3]? = some (.i32 ptr))
    (hc : s.host.gas.Credits (8*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 8) limits (stack.push (.i32 (nextCount count)))
      (iterationFrame frame ptr count) callers code)) rest post) :
    WP cfg (fuel+8) (.next (atCode s limits stack frame callers
      ([.local_get 3,.i32_const 1,.i32_binop .add,.local_set 3,.local_get 2,.i32_const 4294967295,.i32_binop .add,.local_tee 2]++code)))
      (8*cfg.regularOpCost+rest) post := by
  let f := pointerFrame frame ptr
  have f2 : f.locals[2]? = some (.i32 count) := by simpa [f,pointerFrame] using h2
  rw [show 8*cfg.regularOpCost+rest=cfg.regularOpCost+(7*cfg.regularOpCost+rest) by omega]
  apply wp_local_get cfg (fuel+7) _ s limits stack frame callers _ 3 (.i32 ptr) post h3 (hc.mono (by omega))
  rw [show 7*cfg.regularOpCost+rest=cfg.regularOpCost+(6*cfg.regularOpCost+rest) by omega]
  apply wp_i32_const cfg (fuel+6) _ (paid s cfg.regularOpCost 1) limits _ frame callers _ 1 post
  · exact paid_credits s cfg.regularOpCost 1 _ (hc.mono (by omega))
  rw [show 6*cfg.regularOpCost+rest=cfg.regularOpCost+(5*cfg.regularOpCost+rest) by omega]
  apply wp_i32_add cfg (fuel+5) _ (paid s cfg.regularOpCost 2) limits stack frame callers _ ptr 1 post
  · exact paid_credits s cfg.regularOpCost 2 _ (hc.mono (by omega))
  rw [show 5*cfg.regularOpCost+rest=cfg.regularOpCost+(4*cfg.regularOpCost+rest) by omega]
  apply wp_local_set cfg (fuel+4) _ (paid s cfg.regularOpCost 3) limits stack frame callers _ 3 (.i32 (ptr+1)) post
  · exact paid_credits s cfg.regularOpCost 3 _ (hc.mono (by omega))
  rw [show 4*cfg.regularOpCost+rest=cfg.regularOpCost+(3*cfg.regularOpCost+rest) by omega]
  apply wp_local_get cfg (fuel+3) _ (paid s cfg.regularOpCost 4) limits stack f callers _ 2 (.i32 count) post f2
  · exact paid_credits s cfg.regularOpCost 4 _ (hc.mono (by omega))
  rw [show 3*cfg.regularOpCost+rest=cfg.regularOpCost+(2*cfg.regularOpCost+rest) by omega]
  apply wp_i32_const cfg (fuel+2) _ (paid s cfg.regularOpCost 5) limits _ f callers _ 4294967295 post
  · exact paid_credits s cfg.regularOpCost 5 _ (hc.mono (by omega))
  rw [show 2*cfg.regularOpCost+rest=cfg.regularOpCost+(cfg.regularOpCost+rest) by omega]
  apply wp_i32_add cfg (fuel+1) _ (paid s cfg.regularOpCost 6) limits stack f callers _ count 4294967295 post
  · exact paid_credits s cfg.regularOpCost 6 _ (hc.mono (by omega))
  apply wp_local_tee cfg fuel rest (paid s cfg.regularOpCost 7) limits stack f callers code 2 (.i32 (nextCount count)) post
  · exact paid_credits s cfg.regularOpCost 7 _ (hc.mono (by omega))
  · simpa only [iterationFrame,f,nextCount,paid] using hnext

/-- Eleven actual instructions; the subsequent br_if pays its own branch cost. -/
theorem wp_iteration (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (ptr value count : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (h1 : frame.locals[1]? = some (.i32 value)) (h2 : frame.locals[2]? = some (.i32 count)) (h3 : frame.locals[3]? = some (.i32 ptr))
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.memAddrs[0]? = some index) (hmem : s.mems[index]? = some memory)
    (hb : ptr.toNat+1≤memory.byteSize) (hc : s.host.gas.Credits (11*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (iterationStore s cfg.regularOpCost index memory ptr value) limits
      (stack.push (.i32 (nextCount count))) (iterationFrame frame ptr count) callers code)) rest post) :
    WP cfg (fuel+11) (.next (atCode s limits stack frame callers (WNear.Binary.ZeroFill.iteration++code)))
      (11*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  have cut : 3*op+(8*op+rest)≤11*cfg.regularOpCost+rest := by dsimp [op];omega
  have cw : (written s op index memory ptr value).host.gas.Credits (8*op+rest) := by
    unfold written;rw [storeByte_host];exact paid_credits s op 3 _ (hc.mono cut)
  have update := wp_update cfg fuel rest (written s op index memory ptr value) limits stack frame callers code ptr count post h2 h3 cw
    (by simpa only [iterationStore,op] using hnext)
  have hm2 : (paid s op 2).modules[frame.inst]? = some mi := by simpa only [paid,chargedStore] using hm
  have mem2 : (paid s op 2).mems[index]? = some memory := by simpa only [paid,chargedStore] using hmem
  have store := wp_i32_store8 cfg (fuel+8) (8*op+rest) (paid s op 2) limits stack frame callers
    ([.local_get 3,.i32_const 1,.i32_binop .add,.local_set 3,.local_get 2,.i32_const 4294967295,.i32_binop .add,.local_tee 2]++code)
    {align:=0,offset:=0} ptr value mi index memory post hm2 hi mem2 (by simpa using hb)
    (paid_credits s op 2 _ (hc.mono (by dsimp [op];omega)))
    (by simpa only [written,paid,Nat.add_zero,op] using update)
  rw [show 11*cfg.regularOpCost+rest=cfg.regularOpCost+(10*op+rest) by dsimp [op];omega]
  apply wp_local_get cfg (fuel+10) _ s limits stack frame callers _ 3 (.i32 ptr) post h3 (hc.mono (by dsimp [op];omega))
  rw [show 10*op+rest=cfg.regularOpCost+(9*op+rest) by dsimp [op];omega]
  apply wp_local_get cfg (fuel+9) _ (paid s op 1) limits (stack.push (.i32 ptr)) frame callers _ 1 (.i32 value) post h1
  · exact paid_credits s op 1 _ (hc.mono (by dsimp [op];omega))
  · simpa only [WNear.Binary.ZeroFill.iteration,paid,op,List.append_eq,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd,
      show cfg.regularOpCost+(8*op+rest)=9*op+rest by dsimp [op];omega] using store
end WNear.Proofs.ZeroFill
