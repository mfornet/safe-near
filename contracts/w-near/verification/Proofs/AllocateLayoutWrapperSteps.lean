import Proofs.AllocateLayoutResult
import Proofs.InterfaceSetBody

/-! Small concrete instruction groups of the alignment-one layout wrappers. -/
namespace WNear.Proofs.AllocateLayoutWrapper
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
attribute [local irreducible] WP readI32 writeI32

def constantStore (s : Store NearState) (op index offset : Nat) (address value : UInt32) (memory : Memory) :=
  storeI32 (paid s op 3) index (address.toNat + offset) memory value

theorem wp_constant (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (slot offset : Nat) (address value : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (ha : frame.locals[slot]? = some (.i32 address)) (hm : s.modules[frame.inst]? = some mi)
    (hi : mi.memAddrs[0]? = some index) (hmem : s.mems[index]? = some memory)
    (hb : address.toNat + offset + 4 ≤ memory.byteSize) (hc : s.host.gas.Credits (3 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (constantStore s cfg.regularOpCost index offset address value memory) limits stack frame callers code)) rest post) :
    WP cfg (fuel + 3) (.next (atCode s limits stack frame callers
      ([.local_get slot,.i32_const value,.store .i32 none {align := 2,offset}] ++ code))) (3 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  have m : (paid s op 2).modules[frame.inst]? = some mi := hm
  have mm : (paid s op 2).mems[index]? = some memory := hmem
  have st := wp_i32_store cfg fuel rest (paid s op 2) limits stack frame callers code {align := 2,offset} address value mi index memory post m hi mm hb
    (paid_credits s op 2 _ (hc.mono (by dsimp [op]; omega))) hnext
  have co := wp_i32_const cfg (fuel + 1) (op + rest) (paid s op 1) limits (stack.push (.i32 address)) frame callers
    (.store .i32 none {align := 2,offset} :: code) value post (paid_credits s op 1 _ (hc.mono (by dsimp [op]; omega))) st
  have gt := wp_local_get cfg (fuel + 2) (op + (op + rest)) s limits stack frame callers
    (.i32_const value :: .store .i32 none {align := 2,offset} :: code) slot (.i32 address) post ha (hc.mono (by dsimp [op]; omega)) co
  simpa only [List.cons_append,List.nil_append,show cfg.regularOpCost + (op + (op + rest)) = 3 * cfg.regularOpCost + rest by dsimp [op]; omega] using gt

theorem wp_arguments (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (scratch : UInt32) (post : Post) (hs : frame.locals[2]? = some (.i32 scratch))
    (hc : s.host.gas.Credits (4 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 4) limits
      ((stack.push (.i32 scratch)).push (.i32 (scratch + 8))) frame callers code)) rest post) :
    WP cfg (fuel + 4) (.next (atCode s limits stack frame callers
      ([.local_get 2,.local_get 2,.i32_const 8,.i32_binop .add] ++ code))) (4 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  have ad := wp_i32_add cfg fuel rest (paid s op 3) limits (stack.push (.i32 scratch)) frame callers code scratch 8 post
    (paid_credits s op 3 _ (hc.mono (by dsimp [op]; omega))) hnext
  have co := wp_i32_const cfg (fuel + 1) (op + rest) (paid s op 2) limits ((stack.push (.i32 scratch)).push (.i32 scratch)) frame callers
    (.i32_binop .add :: code) 8 post (paid_credits s op 2 _ (hc.mono (by dsimp [op]; omega))) ad
  have g2 := wp_local_get cfg (fuel + 2) (op + (op + rest)) (paid s op 1) limits (stack.push (.i32 scratch)) frame callers
    (.i32_const 8 :: .i32_binop .add :: code) 2 (.i32 scratch) post hs (paid_credits s op 1 _ (hc.mono (by dsimp [op]; omega))) co
  have g1 := wp_local_get cfg (fuel + 3) (op + (op + (op + rest))) s limits stack frame callers
    (.local_get 2 :: .i32_const 8 :: .i32_binop .add :: code) 2 (.i32 scratch) post hs (hc.mono (by dsimp [op]; omega)) g2
  simpa only [List.cons_append,List.nil_append,show cfg.regularOpCost + (op + (op + (op + rest))) = 4 * cfg.regularOpCost + rest by dsimp [op]; omega] using g1

def copyStore (s : Store NearState) (op index : Nat) (out source : UInt32) (memory : Memory) :=
  storeI64 (paid s op 4) index out.toNat memory (readI64 memory source.toNat)

theorem wp_copy (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (out source : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (ho : frame.locals[0]? = some (.i32 out)) (hs : frame.locals[2]? = some (.i32 source))
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.memAddrs[0]? = some index) (hmem : s.mems[index]? = some memory)
    (hr : source.toNat + 8 ≤ memory.byteSize) (hw : out.toNat + 8 ≤ memory.byteSize)
    (hc : s.host.gas.Credits (4 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (copyStore s cfg.regularOpCost index out source memory) limits stack frame callers code)) rest post) :
    WP cfg (fuel + 4) (.next (atCode s limits stack frame callers
      ([.local_get 0,.local_get 2,.load .i64 none {align := 3,offset := 0},.store .i64 none {align := 3,offset := 0}] ++ code)))
      (4 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  have m3 : (paid s op 3).modules[frame.inst]? = some mi := hm
  have mm3 : (paid s op 3).mems[index]? = some memory := hmem
  have st := wp_i64_store cfg fuel rest (paid s op 3) limits stack frame callers code {align := 3,offset := 0} out (readI64 memory source.toNat) mi index memory post
    m3 hi mm3 (by simpa using hw) (paid_credits s op 3 _ (hc.mono (by dsimp [op]; omega))) hnext
  have m2 : (paid s op 2).modules[frame.inst]? = some mi := hm
  have mm2 : (paid s op 2).mems[index]? = some memory := hmem
  have ld := wp_i64_load cfg (fuel + 1) (op + rest) (paid s op 2) limits (stack.push (.i32 out)) frame callers
    (.store .i64 none {align := 3,offset := 0} :: code) {align := 3,offset := 0} source mi index memory post m2 hi mm2
    (by simpa using hr) (paid_credits s op 2 _ (hc.mono (by dsimp [op]; omega))) st
  have g2 := wp_local_get cfg (fuel + 2) (op + (op + rest)) (paid s op 1) limits (stack.push (.i32 out)) frame callers
    (.load .i64 none {align := 3,offset := 0} :: .store .i64 none {align := 3,offset := 0} :: code) 2 (.i32 source) post hs
    (paid_credits s op 1 _ (hc.mono (by dsimp [op]; omega))) ld
  have g1 := wp_local_get cfg (fuel + 3) (op + (op + (op + rest))) s limits stack frame callers
    (.local_get 2 :: .load .i64 none {align := 3,offset := 0} :: .store .i64 none {align := 3,offset := 0} :: code) 0 (.i32 out) post ho
    (hc.mono (by dsimp [op]; omega)) g2
  simpa only [List.cons_append,List.nil_append,show cfg.regularOpCost + (op + (op + (op + rest))) = 4 * cfg.regularOpCost + rest by dsimp [op]; omega] using g1

end WNear.Proofs.AllocateLayoutWrapper
