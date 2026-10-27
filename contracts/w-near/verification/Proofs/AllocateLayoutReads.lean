import Proofs.AllocateLayoutState

/-! Real size-load and alignment-store phases of the accepted layout leaf. -/
namespace WNear.Proofs.AllocateLayout
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
attribute [local irreducible] WP readI32 writeI32

def sizeFrame (frame : CallFrame) (size : UInt32) := {frame with locals := frame.locals.set! 1 (.i32 size)}

theorem wp_size_read (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (input : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (hp : frame.locals[1]? = some (.i32 input)) (hm : s.modules[frame.inst]? = some mi)
    (hi : mi.memAddrs[0]? = some index) (hmem : s.mems[index]? = some memory)
    (hb : input.toNat + 4 ≤ memory.byteSize) (hc : s.host.gas.Credits (3 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 3) limits stack
      (sizeFrame frame (readI32 memory input.toNat)) callers code)) rest post) :
    WP cfg (fuel + 3) (.next (atCode s limits stack frame callers
      ([.local_get 1,.load .i32 none {align := 2,offset := 0},.local_set 1] ++ code))) (3 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  have st := wp_local_set cfg fuel rest (paid s op 2) limits stack frame callers code 1 (.i32 (readI32 memory input.toNat)) post
    (paid_credits s op 2 _ (hc.mono (by dsimp [op]; omega))) hnext
  have hm1 : (paid s op 1).modules[frame.inst]? = some mi := by simpa only [paid,chargedStore] using hm
  have mm1 : (paid s op 1).mems[index]? = some memory := by simpa only [paid,chargedStore] using hmem
  have ld := wp_i32_load cfg (fuel + 1) (op + rest) (paid s op 1) limits stack frame callers (.local_set 1 :: code)
    {align := 2,offset := 0} input mi index memory post hm1 hi mm1 (by simpa only [Nat.add_zero] using hb)
    (paid_credits s op 1 _ (hc.mono (by dsimp [op]; omega))) st
  have gt := wp_local_get cfg (fuel + 2) (op + (op + rest)) s limits stack frame callers
    (.load .i32 none {align := 2,offset := 0} :: .local_set 1 :: code) 1 (.i32 input) post hp
    (hc.mono (by dsimp [op]; omega)) ld
  simpa only [List.cons_append,List.nil_append,
    show cfg.regularOpCost + (op + (op + rest)) = 3 * cfg.regularOpCost + rest by dsimp [op]; omega] using gt

def highStore (s : Store NearState) (op index : Nat) (out : UInt32) (memory : Memory) :=
  storeI32 (paid s op 3) index (out.toNat + 4) memory 1

theorem wp_high (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (out : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (ho : frame.locals[0]? = some (.i32 out)) (ha : frame.locals[3]? = some (.i32 1))
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.memAddrs[0]? = some index)
    (hmem : s.mems[index]? = some memory) (hb : out.toNat + 8 ≤ memory.byteSize)
    (hc : s.host.gas.Credits (3 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (highStore s cfg.regularOpCost index out memory) limits stack frame callers code)) rest post) :
    WP cfg (fuel + 3) (.next (atCode s limits stack frame callers
      ([.local_get 0,.local_get 3,.store .i32 none {align := 2,offset := 4}] ++ code))) (3 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  have hm2 : (paid s op 2).modules[frame.inst]? = some mi := by simpa only [paid,chargedStore] using hm
  have mm2 : (paid s op 2).mems[index]? = some memory := by simpa only [paid,chargedStore] using hmem
  have st := wp_i32_store cfg fuel rest (paid s op 2) limits stack frame callers code {align := 2,offset := 4} out 1 mi index memory post hm2 hi mm2 hb
    (paid_credits s op 2 _ (hc.mono (by dsimp [op]; omega))) hnext
  have ga := wp_local_get cfg (fuel + 1) (op + rest) (paid s op 1) limits (stack.push (.i32 out)) frame callers
    (.store .i32 none {align := 2,offset := 4} :: code) 3 (.i32 1) post ha
    (paid_credits s op 1 _ (hc.mono (by dsimp [op]; omega))) st
  have go := wp_local_get cfg (fuel + 2) (op + (op + rest)) s limits stack frame callers
    (.local_get 3 :: .store .i32 none {align := 2,offset := 4} :: code) 0 (.i32 out) post ho
    (hc.mono (by dsimp [op]; omega)) ga
  simpa only [List.cons_append,List.nil_append,
    show cfg.regularOpCost + (op + (op + rest)) = 3 * cfg.regularOpCost + rest by dsimp [op]; omega] using go

end WNear.Proofs.AllocateLayout
