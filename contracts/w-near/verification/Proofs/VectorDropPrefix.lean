import Proofs.VectorDropEmpty
import NearVM.MeteredLoopRules

/-! Actual nonempty-vector control and argument preparation. The continuations
are immediately at the next deployed call, so no allocator behavior is assumed. -/
namespace WNear.Proofs.VectorDrop
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits paid_gas)
set_option maxRecDepth 16384
set_option maxHeartbeats 300000
attribute [local irreducible] WP

private theorem paid_add (s : Store NearState) (op m n : Nat) :
    paid (paid s op m) op n = paid s op (m + n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [paid, ih]
    rfl

/-- Three actual argument loads, retaining arbitrary lower operands. -/
theorem wp_three_arguments (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (a b c : UInt32) (post : Post)
    (ha : frame.locals[0]? = some (.i32 a)) (hb : frame.locals[1]? = some (.i32 b)) (hcv : frame.locals[2]? = some (.i32 c))
    (hc : s.host.gas.Credits (3 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 3) limits
      (((stack.push (.i32 a)).push (.i32 b)).push (.i32 c)) frame callers code)) rest post) :
    WP cfg (fuel + 3) (.next (atCode s limits stack frame callers
      (.local_get 0 :: .local_get 1 :: .local_get 2 :: code))) (3 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  have get2 := wp_local_get cfg fuel rest (paid s op 2) limits ((stack.push (.i32 a)).push (.i32 b)) frame callers code 2 (.i32 c) post hcv
    (paid_credits s op 2 _ (hc.mono (by dsimp [op]; omega))) hnext
  have get1 := wp_local_get cfg (fuel + 1) (op + rest) (paid s op 1) limits (stack.push (.i32 a)) frame callers (.local_get 2 :: code) 1 (.i32 b) post hb
    (paid_credits s op 1 _ (hc.mono (by dsimp [op]; omega))) get2
  rw [show cfg.regularOpCost + (op + rest) = 2 * op + rest by dsimp [op]; omega] at get1
  have get0 := wp_local_get cfg (fuel + 2) (2 * op + rest) s limits stack frame callers (.local_get 1 :: .local_get 2 :: code) 0 (.i32 a) post ha
    (hc.mono (by dsimp [op]; omega)) get1
  simpa only [Nat.add_assoc, Nat.reduceAdd,
    show cfg.regularOpCost + (2 * op + rest) = 3 * cfg.regularOpCost + rest by dsimp [op]; omega] using get0

/-- The real f311 argument prefix reaches the f237 call and explicit return. -/
theorem wp_forward_prefix (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (a b c : UInt32) (post : Post)
    (ha : frame.locals[0]? = some (.i32 a)) (hb : frame.locals[1]? = some (.i32 b)) (hcv : frame.locals[2]? = some (.i32 c))
    (hc : s.host.gas.Credits (3 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 3) limits
      (((stack.push (.i32 a)).push (.i32 b)).push (.i32 c)) frame callers [.call 237, .return])) rest post) :
    WP cfg (fuel + 3) (.next (atCode s limits stack frame callers WNear.Binary.VectorDrop.body311))
      (3 * cfg.regularOpCost + rest) post := by
  exact wp_three_arguments cfg fuel rest s limits stack frame callers [.call 237, .return] a b c post ha hb hcv hc hnext

/-- A positive capacity falls through f777's branch and reaches its actual
f311 call. No heap/deallocator postcondition is used. -/
theorem wp_capacity_prefix (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (a capacity alignment : UInt32) (post : Post)
    (ha : frame.locals[0]? = some (.i32 a)) (hb : frame.locals[1]? = some (.i32 capacity)) (hv : frame.locals[2]? = some (.i32 alignment))
    (hn : capacity ≠ 0) (hc : s.host.gas.Credits (6 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 6) limits
      (((stack.push (.i32 a)).push (.i32 capacity)).push (.i32 alignment))
      (emptyBlockFrame frame stack.size code) callers [.call 311])) rest post) :
    WP cfg (fuel + 7) (.next (atCode s limits stack frame callers (WNear.Binary.VectorDrop.body777 ++ code)))
      (6 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let blocked := emptyBlockFrame frame stack.size code
  have args := wp_three_arguments cfg fuel rest (paid s op 3) limits stack blocked callers [.call 311] a capacity alignment post ha hb hv
    (paid_credits s op 3 _ (hc.mono (by dsimp [op]; omega))) hnext
  have branch := wp_br_if_zero cfg (fuel + 3) (3 * op + rest) (paid s op 2) limits stack blocked callers
    WNear.Binary.VectorDrop.capacityTail 0 post (paid_credits s op 2 _ (hc.mono (by dsimp [op]; omega))) args
  have boolZero : Numeric.bool (capacity == 0) = 0 := by simp [Numeric.bool, hn]
  have eqz := wp_i32_eqz cfg (fuel + 4) (4 * op + rest) (paid s op 1) limits stack blocked callers
    (.br_if 0 :: WNear.Binary.VectorDrop.capacityTail) capacity post
    (paid_credits s op 1 _ (hc.mono (by dsimp [op]; omega)))
  have eqzNext : WP cfg (fuel + 4) (.next (atCode (paid s op 2) limits (stack.push (.i32 (Numeric.bool (capacity == 0)))) blocked callers
      (.br_if 0 :: WNear.Binary.VectorDrop.capacityTail))) (4 * op + rest) post := by
    rw [show cfg.regularOpCost + (3 * op + rest) = 4 * op + rest by dsimp [op]; omega] at branch
    simpa only [boolZero, Nat.add_assoc, Nat.reduceAdd] using branch
  have tested := eqz eqzNext
  have get := wp_local_get cfg (fuel + 5) (5 * op + rest) s limits stack blocked callers
    (.i32_eqz :: .br_if 0 :: WNear.Binary.VectorDrop.capacityTail) 1 (.i32 capacity) post hb (hc.mono (by dsimp [op]; omega))
  have getNext : WP cfg (fuel + 5) (.next (atCode (paid s op 1) limits (stack.push (.i32 capacity)) blocked callers
      (.i32_eqz :: .br_if 0 :: WNear.Binary.VectorDrop.capacityTail))) (5 * op + rest) post := by
    rw [show cfg.regularOpCost + (4 * op + rest) = 5 * op + rest by dsimp [op]; omega] at tested
    exact tested
  have guarded := get getNext
  have blockNext : WP cfg (fuel + 6) (.next (atCode s limits stack blocked callers
      (WNear.Binary.VectorDrop.capacityGuard ++ WNear.Binary.VectorDrop.capacityTail))) (6 * op + rest) post := by
    simpa only [WNear.Binary.VectorDrop.capacityGuard, List.cons_append, List.nil_append, Nat.add_assoc, Nat.reduceAdd,
      show cfg.regularOpCost + (5 * op + rest) = 6 * op + rest by dsimp [op]; omega] using guarded
  have block := wp_block_empty cfg (fuel + 6) (6 * op + rest) s limits stack frame callers
    (WNear.Binary.VectorDrop.capacityGuard ++ WNear.Binary.VectorDrop.capacityTail) code post hc blockNext
  simpa only [WNear.Binary.VectorDrop.body777, List.cons_append, List.nil_append, Nat.add_assoc, Nat.reduceAdd] using block


/-- The actual header guard on a nonzero capacity retains the block and falls through. -/
theorem wp_nonzero_guard (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (vector : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (hv : frame.locals[0]? = some (.i32 vector))
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.memAddrs[0]? = some index) (hmem : s.mems[index]? = some memory)
    (hb : vector.toNat + 8 ≤ memory.byteSize) (hn : readI32 memory (vector.toNat + 4) ≠ 0)
    (hc : s.host.gas.Credits (5 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 5) limits stack (emptyBlockFrame (capacityFrame frame (readI32 memory (vector.toNat + 4))) stack.size code) callers WNear.Binary.VectorDrop.vectorTail)) rest post) :
    WP cfg (fuel + 5) (.next (atCode s limits stack (emptyBlockFrame frame stack.size code) callers
      (WNear.Binary.VectorDrop.vectorGuard ++ WNear.Binary.VectorDrop.vectorTail))) (5 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let capacity := readI32 memory (vector.toNat + 4)
  let updated := capacityFrame frame capacity
  let blocked := emptyBlockFrame frame stack.size code
  let newblocked := emptyBlockFrame updated stack.size code
  have br := wp_br_if_zero cfg fuel rest (paid s op 4) limits stack newblocked callers
    WNear.Binary.VectorDrop.vectorTail 0 post (paid_credits s op 4 _ (hc.mono (by dsimp [op]; omega))) hnext
  have boolZero : Numeric.bool (capacity == 0) = 0 := by simp [Numeric.bool, capacity, hn]
  have brNext : WP cfg (fuel + 1) (.next (atCode (paid s op 4) limits (stack.push (.i32 (Numeric.bool (capacity == 0)))) newblocked callers
      (.br_if 0 :: WNear.Binary.VectorDrop.vectorTail))) (op + rest) post := by
    simpa only [boolZero, op] using br
  have eqz := wp_i32_eqz cfg (fuel + 1) (op + rest) (paid s op 3) limits stack newblocked callers
    (.br_if 0 :: WNear.Binary.VectorDrop.vectorTail) capacity post (paid_credits s op 3 _ (hc.mono (by dsimp [op]; omega))) brNext
  have tee := wp_local_tee cfg (fuel + 2) (2 * op + rest) (paid s op 2) limits stack blocked callers
    (.i32_eqz :: .br_if 0 :: WNear.Binary.VectorDrop.vectorTail) 1 (.i32 capacity) post
    (paid_credits s op 2 _ (hc.mono (by dsimp [op]; omega)))
  have teeNext : WP cfg (fuel + 2) (.next (atCode (paid s op 3) limits (stack.push (.i32 capacity))
      {blocked with locals := blocked.locals.set! 1 (.i32 capacity)} callers (.i32_eqz :: .br_if 0 :: WNear.Binary.VectorDrop.vectorTail))) (2 * op + rest) post := by
    rw [show cfg.regularOpCost + (op + rest) = 2 * op + rest by dsimp [op]; omega] at eqz
    simpa only [newblocked, updated, blocked, emptyBlockFrame, capacityFrame] using eqz
  have teed := tee teeNext
  have hm1 : (paid s op 1).modules[blocked.inst]? = some mi := by simpa only [paid, chargedStore, blocked, emptyBlockFrame] using hm
  have hmem1 : (paid s op 1).mems[index]? = some memory := by simpa only [paid, chargedStore] using hmem
  have load := wp_i32_load cfg (fuel + 3) (3 * op + rest) (paid s op 1) limits stack blocked callers
    (.local_tee 1 :: .i32_eqz :: .br_if 0 :: WNear.Binary.VectorDrop.vectorTail) {align := 2, offset := 4} vector mi index memory post
    hm1 hi hmem1 (by omega) (paid_credits s op 1 _ (hc.mono (by dsimp [op]; omega)))
  have loadNext : WP cfg (fuel + 3) (.next (atCode (paid s op 2) limits (stack.push (.i32 (readI32 memory (vector.toNat + 4)))) blocked callers
      (.local_tee 1 :: .i32_eqz :: .br_if 0 :: WNear.Binary.VectorDrop.vectorTail))) (3 * op + rest) post := by
    rw [show cfg.regularOpCost + (2 * op + rest) = 3 * op + rest by dsimp [op]; omega] at teed
    simpa only [capacity] using teed
  have loaded := load loadNext
  have get := wp_local_get cfg (fuel + 4) (4 * op + rest) s limits stack blocked callers
    (.load .i32 none {align := 2, offset := 4} :: .local_tee 1 :: .i32_eqz :: .br_if 0 :: WNear.Binary.VectorDrop.vectorTail) 0 (.i32 vector) post hv (hc.mono (by dsimp [op]; omega))
  rw [show cfg.regularOpCost + (3 * op + rest) = 4 * op + rest by dsimp [op]; omega] at loaded
  have got := get loaded
  simpa only [WNear.Binary.VectorDrop.vectorGuard, List.cons_append, List.nil_append, Nat.add_assoc, Nat.reduceAdd,
    show cfg.regularOpCost + (4 * op + rest) = 5 * cfg.regularOpCost + rest by dsimp [op]; omega] using got

/-- f747 reads the pointer only after the nonzero header test, then prepares
exactly pointer, capacity, alignment-one for f777. -/
theorem wp_vector_arguments (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (vector capacity : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (hv : frame.locals[0]? = some (.i32 vector)) (hcap : frame.locals[1]? = some (.i32 capacity))
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.memAddrs[0]? = some index) (hmem : s.mems[index]? = some memory)
    (hb : vector.toNat + 4 ≤ memory.byteSize)
    (hc : s.host.gas.Credits (4 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 4) limits
      (((stack.push (.i32 (readI32 memory vector.toNat))).push (.i32 capacity)).push (.i32 1)) frame callers code)) rest post) :
    WP cfg (fuel + 4) (.next (atCode s limits stack frame callers
      (.local_get 0 :: .load .i32 none {align := 2, offset := 0} :: .local_get 1 :: .i32_const 1 :: code)))
      (4 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let pointer := readI32 memory vector.toNat
  have constant := wp_i32_const cfg fuel rest (paid s op 3) limits ((stack.push (.i32 pointer)).push (.i32 capacity)) frame callers code 1 post
    (paid_credits s op 3 _ (hc.mono (by dsimp [op]; omega))) hnext
  have get1 := wp_local_get cfg (fuel + 1) (op + rest) (paid s op 2) limits (stack.push (.i32 pointer)) frame callers (.i32_const 1 :: code) 1 (.i32 capacity) post hcap
    (paid_credits s op 2 _ (hc.mono (by dsimp [op]; omega))) constant
  have hm1 : (paid s op 1).modules[frame.inst]? = some mi := by simpa only [paid, chargedStore] using hm
  have hmem1 : (paid s op 1).mems[index]? = some memory := by simpa only [paid, chargedStore] using hmem
  have load := wp_i32_load cfg (fuel + 2) (2 * op + rest) (paid s op 1) limits stack frame callers
    (.local_get 1 :: .i32_const 1 :: code) {align := 2, offset := 0} vector mi index memory post hm1 hi hmem1 (by simpa using hb)
    (paid_credits s op 1 _ (hc.mono (by dsimp [op]; omega)))
  have loadNext : WP cfg (fuel + 2) (.next (atCode (paid s op 2) limits (stack.push (.i32 (readI32 memory (vector.toNat + 0)))) frame callers
      (.local_get 1 :: .i32_const 1 :: code))) (2 * op + rest) post := by
    rw [show cfg.regularOpCost + (op + rest) = 2 * op + rest by dsimp [op]; omega] at get1
    simpa only [pointer, Nat.add_zero] using get1
  have loaded := load loadNext
  rw [show cfg.regularOpCost + (2 * op + rest) = 3 * op + rest by dsimp [op]; omega] at loaded
  have get0 := wp_local_get cfg (fuel + 3) (3 * op + rest) s limits stack frame callers
    (.load .i32 none {align := 2, offset := 0} :: .local_get 1 :: .i32_const 1 :: code) 0 (.i32 vector) post hv
    (hc.mono (by dsimp [op]; omega)) loaded
  simpa only [Nat.add_assoc, Nat.reduceAdd,
    show cfg.regularOpCost + (3 * op + rest) = 4 * cfg.regularOpCost + rest by dsimp [op]; omega] using get0



/-- Complete positive f747 prefix, from its real block entry through the
pointer/header reads to the pending f777 call. All functional state is fixed. -/
theorem wp_vector_prefix (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (vector : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (hv : frame.locals[0]? = some (.i32 vector)) (hsize : 2 ≤ frame.locals.size)
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.memAddrs[0]? = some index) (hmem : s.mems[index]? = some memory)
    (hb : vector.toNat + 8 ≤ memory.byteSize) (hn : readI32 memory (vector.toNat + 4) ≠ 0)
    (hc : s.host.gas.Credits (9 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 9) limits
      (((stack.push (.i32 (readI32 memory vector.toNat))).push (.i32 (readI32 memory (vector.toNat + 4)))).push (.i32 1))
      (emptyBlockFrame (capacityFrame frame (readI32 memory (vector.toNat + 4))) stack.size code) callers [.call 777])) rest post) :
    WP cfg (fuel + 10) (.next (atCode s limits stack frame callers (WNear.Binary.VectorDrop.body747 ++ code)))
      (9 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let capacity := readI32 memory (vector.toNat + 4)
  let updated := capacityFrame frame capacity
  let blocked := emptyBlockFrame updated stack.size code
  have hlocal0 : blocked.locals[0]? = some (.i32 vector) := by simpa [blocked, updated, capacityFrame, emptyBlockFrame] using hv
  have hlocal1 : blocked.locals[1]? = some (.i32 capacity) := by
    simp [blocked, updated, capacityFrame, emptyBlockFrame, show 1 < frame.locals.size by omega]
  have hm5 : (paid s op 5).modules[blocked.inst]? = some mi := by simpa only [paid, chargedStore, blocked, updated, capacityFrame, emptyBlockFrame] using hm
  have hmem5 : (paid s op 5).mems[index]? = some memory := by simpa only [paid, chargedStore] using hmem
  have argsNext : WP cfg fuel (.next (atCode (paid (paid s op 5) op 4) limits
      (((stack.push (.i32 (readI32 memory vector.toNat))).push (.i32 capacity)).push (.i32 1)) blocked callers [.call 777])) rest post := by
    simpa only [paid_add, capacity, blocked, updated, Nat.reduceAdd] using hnext
  have args := wp_vector_arguments cfg fuel rest (paid s op 5) limits stack blocked callers [.call 777] vector capacity mi index memory post
    hlocal0 hlocal1 hm5 hi hmem5 (by omega) (paid_credits s op 5 _ (hc.mono (by dsimp [op]; omega))) argsNext
  have guard := wp_nonzero_guard cfg (fuel + 4) (4 * op + rest) s limits stack frame callers code vector mi index memory post
    hv hm hi hmem hb hn (hc.mono (by dsimp [op]; omega)) args
  have blockNext : WP cfg (fuel + 9) (.next (atCode s limits stack (emptyBlockFrame frame stack.size code) callers
      (WNear.Binary.VectorDrop.vectorGuard ++ WNear.Binary.VectorDrop.vectorTail))) (9 * op + rest) post := by
    simpa only [Nat.add_assoc, Nat.reduceAdd, show 5 * cfg.regularOpCost + (4 * op + rest) = 9 * op + rest by dsimp [op]; omega] using guard
  have block := wp_block_empty cfg (fuel + 9) (9 * op + rest) s limits stack frame callers
    (WNear.Binary.VectorDrop.vectorGuard ++ WNear.Binary.VectorDrop.vectorTail) code post hc blockNext
  simpa only [WNear.Binary.VectorDrop.body747, List.cons_append, List.nil_append, Nat.add_assoc, Nat.reduceAdd] using block
end WNear.Proofs.VectorDrop
