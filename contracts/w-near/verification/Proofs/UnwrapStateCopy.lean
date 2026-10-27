import Binary.UnwrapState
import Proofs.StorePairCallerState
import NearVM.MeteredByteMemoryRules
import NearVM.MeteredLoopRules

/-! Actual f951 byte-loop instruction composition. Aliasing remains sequential. -/
namespace WNear.Proofs.UnwrapStateCopy
open Wasm Wasm.Near Wasm.Near.MeteredLogic
open WNear.Proofs.StorePairCaller (paid paid_credits)
set_option maxHeartbeats 1000000
set_option maxRecDepth 12000

/-- Actual local increment, retaining every other local and the operand prefix. -/
theorem wp_add_set (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (slot : Nat) (value delta : UInt32) (post : Post)
    (hlocal : frame.locals[slot]? = some (.i32 value))
    (hc : s.host.gas.Credits (4 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 4) limits stack
      {frame with locals := frame.locals.set! slot (.i32 (value + delta))} callers code)) rest post) :
    WP cfg (fuel + 4) (.next (atCode s limits stack frame callers
      ([.local_get slot, .i32_const delta, .i32_binop .add, .local_set slot] ++ code)))
      (4 * cfg.regularOpCost + rest) post := by
  rw [show 4 * cfg.regularOpCost + rest = cfg.regularOpCost + (3 * cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 3) (3 * cfg.regularOpCost + rest) s limits stack frame callers _ slot (.i32 value) post hlocal
    (hc.mono (by omega))
  rw [show 3 * cfg.regularOpCost + rest = cfg.regularOpCost + (2 * cfg.regularOpCost + rest) by omega]
  apply wp_i32_const cfg (fuel + 2) (2 * cfg.regularOpCost + rest) _ limits _ frame callers _ delta post
  · apply paid_credits s cfg.regularOpCost 1; exact hc.mono (by omega)
  rw [show 2 * cfg.regularOpCost + rest = cfg.regularOpCost + (cfg.regularOpCost + rest) by omega]
  apply wp_i32_add cfg (fuel + 1) (cfg.regularOpCost + rest) _ limits stack frame callers _ value delta post
  · apply paid_credits s cfg.regularOpCost 2; exact hc.mono (by omega)
  apply wp_local_set cfg fuel rest _ limits stack frame callers code slot (.i32 (value + delta)) post
  · apply paid_credits s cfg.regularOpCost 3; exact hc.mono (by omega)
  · simpa only [paid] using hnext

/-- The decrement's tee retains the branch condition while updating local2. -/
theorem wp_add_tee (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (slot : Nat) (value delta : UInt32) (post : Post)
    (hlocal : frame.locals[slot]? = some (.i32 value))
    (hc : s.host.gas.Credits (4 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 4) limits
      (stack.push (.i32 (value + delta)))
      {frame with locals := frame.locals.set! slot (.i32 (value + delta))} callers code)) rest post) :
    WP cfg (fuel + 4) (.next (atCode s limits stack frame callers
      ([.local_get slot, .i32_const delta, .i32_binop .add, .local_tee slot] ++ code)))
      (4 * cfg.regularOpCost + rest) post := by
  rw [show 4 * cfg.regularOpCost + rest = cfg.regularOpCost + (3 * cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 3) (3 * cfg.regularOpCost + rest) s limits stack frame callers _ slot (.i32 value) post hlocal
    (hc.mono (by omega))
  rw [show 3 * cfg.regularOpCost + rest = cfg.regularOpCost + (2 * cfg.regularOpCost + rest) by omega]
  apply wp_i32_const cfg (fuel + 2) (2 * cfg.regularOpCost + rest) _ limits _ frame callers _ delta post
  · apply paid_credits s cfg.regularOpCost 1; exact hc.mono (by omega)
  rw [show 2 * cfg.regularOpCost + rest = cfg.regularOpCost + (cfg.regularOpCost + rest) by omega]
  apply wp_i32_add cfg (fuel + 1) (cfg.regularOpCost + rest) _ limits stack frame callers _ value delta post
  · apply paid_credits s cfg.regularOpCost 2; exact hc.mono (by omega)
  apply wp_local_tee cfg fuel rest _ limits stack frame callers code slot (.i32 (value + delta)) post
  · apply paid_credits s cfg.regularOpCost 3; exact hc.mono (by omega)
  · simpa only [paid] using hnext

/-- Exactly one byte is loaded and stored, with memory effects from the actual
Wasm packed instructions rather than an assumed copy-function result. -/
theorem wp_copy_byte (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (out source : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (hout : frame.locals[3]? = some (.i32 out)) (hsource : frame.locals[1]? = some (.i32 source))
    (hmodule : s.modules[frame.inst]? = some mi) (hindex : mi.memAddrs[0]? = some index)
    (hmemory : s.mems[index]? = some memory)
    (hread : source.toNat + 1 ≤ memory.byteSize) (hwrite : out.toNat + 1 ≤ memory.byteSize)
    (hc : s.host.gas.Credits (4 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode
      (storeByte (paid s cfg.regularOpCost 4) index out.toNat memory (readByteWord memory source.toNat))
      limits stack frame callers code)) rest post) :
    WP cfg (fuel + 4) (.next (atCode s limits stack frame callers
      ([.local_get 3, .local_get 1, .load .i32 (some ⟨8, false⟩) {align := 0, offset := 0},
        .store .i32 (some 8) {align := 0, offset := 0}] ++ code))) (4 * cfg.regularOpCost + rest) post := by
  have hm2 : (paid s cfg.regularOpCost 2).modules[frame.inst]? = some mi := by simpa only [paid, chargedStore] using hmodule
  have hmem2 : (paid s cfg.regularOpCost 2).mems[index]? = some memory := by simpa only [paid, chargedStore] using hmemory
  have hm3 : (paid s cfg.regularOpCost 3).modules[frame.inst]? = some mi := by simpa only [paid, chargedStore] using hmodule
  have hmem3 : (paid s cfg.regularOpCost 3).mems[index]? = some memory := by simpa only [paid, chargedStore] using hmemory
  rw [show 4 * cfg.regularOpCost + rest = cfg.regularOpCost + (3 * cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 3) (3 * cfg.regularOpCost + rest) s limits stack frame callers _ 3 (.i32 out) post hout
    (hc.mono (by omega))
  rw [show 3 * cfg.regularOpCost + rest = cfg.regularOpCost + (2 * cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 2) (2 * cfg.regularOpCost + rest) _ limits _ frame callers _ 1 (.i32 source) post hsource
  · apply paid_credits s cfg.regularOpCost 1; exact hc.mono (by omega)
  rw [show 2 * cfg.regularOpCost + rest = cfg.regularOpCost + (cfg.regularOpCost + rest) by omega]
  apply wp_i32_load8_unsigned cfg (fuel + 1) (cfg.regularOpCost + rest) (paid s cfg.regularOpCost 2) limits _ frame callers _
    {align := 0, offset := 0} source mi index memory post hm2 hindex hmem2
  · simpa only [Nat.add_zero] using hread
  · apply paid_credits s cfg.regularOpCost 2; exact hc.mono (by omega)
  apply wp_i32_store8 cfg fuel rest (paid s cfg.regularOpCost 3) limits stack frame callers code
    {align := 0, offset := 0} out (readByteWord memory source.toNat) mi index memory post hm3 hindex hmem3
  · simpa only [Nat.add_zero] using hwrite
  · apply paid_credits s cfg.regularOpCost 3; exact hc.mono (by omega)
  · simpa only [paid, Nat.add_zero] using hnext

/-- The16scalarinstructions before the loop's conditional backedge. -/
abbrev iterationPrefix : Expr := WNear.Binary.UnwrapState.Copy.loopBody.take 16

def byteStore (s : Store NearState) (op index : Nat) (out source : UInt32) (memory : Memory) : Store NearState :=
  storeByte (paid s op 4) index out.toNat memory (readByteWord memory source.toNat)

def prefixStore (s : Store NearState) (op index : Nat) (out source : UInt32) (memory : Memory) : Store NearState :=
  paid (paid (paid (byteStore s op index out source memory) op 4) op 4) op 4

def prefixFrame (frame : CallFrame) (out source count : UInt32) : CallFrame :=
  {frame with locals := ((frame.locals.set! 1 (.i32 (source + 1))).set! 3 (.i32 (out + 1))).set! 2 (.i32 (count + 4294967295))}

theorem loop_decomposition : WNear.Binary.UnwrapState.Copy.loopBody = iterationPrefix ++ [.br_if 0] := rfl

theorem four_groups (op rest : Nat) : 4 * op + (4 * op + (4 * op + (4 * op + rest))) = 16 * op + rest := by omega

/-- One real loop iteration up to its branch. All16opcodes execute, one byte
is copied, both pointers increment, and the decremented count remains onstack. -/
theorem wp_iteration_prefix (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (out source count : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (hout : frame.locals[3]? = some (.i32 out)) (hsource : frame.locals[1]? = some (.i32 source))
    (hcount : frame.locals[2]? = some (.i32 count))
    (hmodule : s.modules[frame.inst]? = some mi) (hindex : mi.memAddrs[0]? = some index)
    (hmemory : s.mems[index]? = some memory)
    (hread : source.toNat + 1 ≤ memory.byteSize) (hwrite : out.toNat + 1 ≤ memory.byteSize)
    (hc : s.host.gas.Credits (16 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (prefixStore s cfg.regularOpCost index out source memory)
      limits (stack.push (.i32 (count + 4294967295))) (prefixFrame frame out source count) callers code)) rest post) :
    WP cfg (fuel + 16) (.next (atCode s limits stack frame callers (iterationPrefix ++ code)))
      (16 * cfg.regularOpCost + rest) post := by
  let s4 := byteStore s cfg.regularOpCost index out source memory
  let s8 := paid s4 cfg.regularOpCost 4
  let s12 := paid s8 cfg.regularOpCost 4
  let f1 := {frame with locals := frame.locals.set! 1 (.i32 (source + 1))}
  let f2 := {f1 with locals := f1.locals.set! 3 (.i32 (out + 1))}
  let r4 := 4 * cfg.regularOpCost + rest
  let r8 := 4 * cfg.regularOpCost + r4
  let r12 := 4 * cfg.regularOpCost + r8
  have c4 : s4.host.gas.Credits r12 := by
    apply paid_credits s cfg.regularOpCost 4
    exact hc.mono (by dsimp [r12, r8, r4]; omega)
  have c8 : s8.host.gas.Credits r8 := paid_credits s4 cfg.regularOpCost 4 r8 c4
  have c12 : s12.host.gas.Credits r4 := paid_credits s8 cfg.regularOpCost 4 r4 c8
  have fout : f1.locals[3]? = some (.i32 out) := by simpa [f1] using hout
  have fcount : f2.locals[2]? = some (.i32 count) := by simpa [f2, f1] using hcount
  have counterRule := wp_add_tee cfg fuel rest s12 limits stack f2 callers code 2 count 4294967295 post
  have counterLocal := counterRule fcount
  have counterPaid := counterLocal c12
  have counterNext : WP cfg fuel (.next (atCode (paid s12 cfg.regularOpCost 4) limits
      (stack.push (.i32 (count + 4294967295)))
      {f2 with locals := f2.locals.set! 2 (.i32 (count + 4294967295))} callers code)) rest post := by
    simpa only [prefixStore, prefixFrame, s12, s8, s4, f2, f1] using hnext
  have counter := counterPaid counterNext
  have outRule := wp_add_set cfg (fuel + 4) r4 s8 limits stack f1 callers
    ([.local_get 2, .i32_const 4294967295, .i32_binop .add, .local_tee 2] ++ code) 3 out 1 post
  have outLocal := outRule fout
  have outResult := outLocal c8 counter
  have sourceRule := wp_add_set cfg ((fuel + 4) + 4) r8 s4 limits stack frame callers
    ([.local_get 3, .i32_const 1, .i32_binop .add, .local_set 3] ++
      [.local_get 2, .i32_const 4294967295, .i32_binop .add, .local_tee 2] ++ code) 1 source 1 post
  have sourceLocal := sourceRule hsource
  have sourceResult := sourceLocal c4 outResult
  have copyRule := wp_copy_byte cfg (((fuel + 4) + 4) + 4) r12 s limits stack frame callers
    ([.local_get 1, .i32_const 1, .i32_binop .add, .local_set 1] ++
      [.local_get 3, .i32_const 1, .i32_binop .add, .local_set 3] ++
      [.local_get 2, .i32_const 4294967295, .i32_binop .add, .local_tee 2] ++ code)
    out source mi index memory post
  have copyLocals := copyRule hout hsource
  have copyEnv := copyLocals hmodule hindex hmemory hread hwrite
  have copyCredit : s.host.gas.Credits (4 * cfg.regularOpCost + r12) := hc.mono (by dsimp [r12, r8, r4]; omega)
  have result := copyEnv copyCredit sourceResult
  have budget : 4 * cfg.regularOpCost + r12 = 16 * cfg.regularOpCost + rest := four_groups _ _
  rw [budget] at result
  simpa only [iterationPrefix, WNear.Binary.UnwrapState.Copy.loopBody, List.take,
    List.cons_append, List.nil_append, List.append_assoc, Nat.add_assoc, Nat.reduceAdd] using result

theorem count_decrement (n : Nat) (_hn : n + 1 < 2 ^ 32) :
    UInt32.ofNat (n + 1) + 4294967295 = UInt32.ofNat n := by
  apply UInt32.toNat_inj.mp
  simp only [UInt32.toNat_add, UInt32.toNat_ofNat, UInt32.toNat_ofNat']
  omega

theorem count_nonzero (n : Nat) (hpositive : 0 < n) (hn : n < 2 ^ 32) : UInt32.ofNat n ≠ 0 := by
  intro h
  have hnat := congrArg UInt32.toNat h
  simp only [UInt32.toNat_ofNat, UInt32.toNat_ofNat'] at hnat
  omega

theorem pointer_next (address : UInt32) (h : address.toNat + 1 < 2 ^ 32) :
    (address + 1).toNat = address.toNat + 1 := by
  rw [UInt32.toNat_add]
  simp only [UInt32.toNat_ofNat]
  omega

theorem prefixStore_credits (s : Store NearState) (op index : Nat) (out source : UInt32)
    (memory : Memory) (rest : Nat) (hc : s.host.gas.Credits (16 * op + rest)) :
    (prefixStore s op index out source memory).host.gas.Credits rest := by
  apply paid_credits
  apply paid_credits
  apply paid_credits
  apply paid_credits s op 4
  exact hc.mono (by omega)

theorem prefixStore_memory (s : Store NearState) (op index : Nat) (out source : UInt32)
    (memory : Memory) (hmemory : s.mems[index]? = some memory) :
    (prefixStore s op index out source memory).mems[index]? =
      some (writeByte memory out.toNat (readByteWord memory source.toNat)) := by
  have hp : (paid s op 4).mems[index]? = some memory := by simpa only [paid, chargedStore] using hmemory
  have hm := storeByte_memory (paid s op 4) index out.toNat memory (readByteWord memory source.toNat) hp
  simpa only [prefixStore, byteStore, paid, chargedStore] using hm

def loopStore (s : Store NearState) (op index : Nat) (out source : UInt32) (memory : Memory) : Nat → Store NearState
  | 0 => s
  | n + 1 => loopStore
      (chargedStore (prefixStore s op index out source memory) ((if n = 0 then 1 else 2) * op))
      op index (out + 1) (source + 1) (writeByte memory out.toNat (readByteWord memory source.toNat)) n

def loopFrame (frame : CallFrame) (out source : UInt32) : Nat → CallFrame
  | 0 => frame
  | n + 1 => loopFrame (prefixFrame frame out source (UInt32.ofNat (n + 1))) (out + 1) (source + 1) n

theorem loop_cost_step (op n : Nat) (hn : 0 < n) :
    (18 * (n + 1) - 1) * op = 16 * op + (2 * op + (18 * n - 1) * op) := by
  have h : 18 * (n + 1) - 1 = 18 + (18 * n - 1) := by omega
  rw [h, Nat.add_mul]
  omega

theorem loop_fuel_step (fuel n : Nat) : (fuel + (17 * n + 1) + 1) + 16 = fuel + (17 * (n + 1) + 1) := by omega

attribute [local irreducible] prefixStore byteStore chargedStore

theorem loopStore_one (s : Store NearState) (op index : Nat) (out source : UInt32) (memory : Memory) :
    loopStore s op index out source memory 1 = chargedStore (prefixStore s op index out source memory) op := by
  exact congrArg (chargedStore (prefixStore s op index out source memory)) (Nat.one_mul op)

theorem loopFrame_one (frame : CallFrame) (out source : UInt32) :
    loopFrame frame out source 1 = prefixFrame frame out source (UInt32.ofNat 1) := rfl

theorem loopStore_succ (s : Store NearState) (op index : Nat) (out source : UInt32) (memory : Memory) (n : Nat) :
    loopStore s op index out source memory (n + 1) = loopStore
      (chargedStore (prefixStore s op index out source memory) ((if n = 0 then 1 else 2) * op))
      op index (out + 1) (source + 1) (writeByte memory out.toNat (readByteWord memory source.toNat)) n := rfl

theorem loopFrame_succ (frame : CallFrame) (out source : UInt32) (n : Nat) :
    loopFrame frame out source (n + 1) =
      loopFrame (prefixFrame frame out source (UInt32.ofNat (n + 1))) (out + 1) (source + 1) n := rfl

/-- Actual positive-count f951 loop, from the entered loop label through its
free fallthrough. The exact sequential result permits arbitrary aliasing. -/
theorem wp_loop (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (out source : UInt32) (count : Nat)
    (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (hout : frame.locals[3]? = some (.i32 out)) (hsource : frame.locals[1]? = some (.i32 source))
    (hcount : frame.locals[2]? = some (.i32 (UInt32.ofNat count)))
    (hmodule : s.modules[frame.inst]? = some mi) (hindex : mi.memAddrs[0]? = some index)
    (hmemory : s.mems[index]? = some memory) (hwf : memory.wf)
    (hpositive : 0 < count) (hcountWidth : count < 2 ^ 32) (hwidth : memory.byteSize ≤ 2 ^ 32)
    (hread : source.toNat + count ≤ memory.byteSize) (hwrite : out.toNat + count ≤ memory.byteSize)
    (hc : s.host.gas.Credits ((18 * count - 1) * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (loopStore s cfg.regularOpCost index out source memory count)
      limits stack (loopFrame frame out source count) callers code)) rest post) :
    WP cfg (fuel + (17 * count + 1)) (.next (atCode s limits stack
      (emptyLoopFrame frame stack.size WNear.Binary.UnwrapState.Copy.loopBody code) callers
      WNear.Binary.UnwrapState.Copy.loopBody)) ((18 * count - 1) * cfg.regularOpCost + rest) post := by
  induction count generalizing s frame memory out source with
  | zero => omega
  | succ n ih =>
    let ps := prefixStore s cfg.regularOpCost index out source memory
    let pf := prefixFrame frame out source (UInt32.ofNat (n + 1))
    have hr : source.toNat + 1 ≤ memory.byteSize := by omega
    have hw : out.toNat + 1 ≤ memory.byteSize := by omega
    by_cases hn : n = 0
    · subst n
      let last := chargedStore ps cfg.regularOpCost
      have cp : s.host.gas.Credits (16 * cfg.regularOpCost + (cfg.regularOpCost + rest)) := hc.mono (by omega)
      have cb : ps.host.gas.Credits (cfg.regularOpCost + rest) := prefixStore_credits _ _ _ _ _ _ _ cp
      have cr : last.host.gas.Credits rest := WNear.Proofs.StorePair.charged_credits ps _ _ cb
      have finalNext : WP cfg fuel (.next (atCode last limits stack pf callers code)) rest post := by
        simpa only [Nat.reduceAdd, loopStore_one, loopFrame_one] using hnext
      let label : Label := {arity := 0, height := stack.size, rest := code, loop := some WNear.Binary.UnwrapState.Copy.loopBody}
      have hend := wp_end_label cfg fuel rest last limits stack pf callers label post cr finalNext
      have endNext : WP cfg (fuel + 1) (.next (atCode last limits stack
          (prefixFrame (emptyLoopFrame frame stack.size WNear.Binary.UnwrapState.Copy.loopBody code)
            out source (UInt32.ofNat 1)) callers [])) rest post := hend
      have branch := wp_br_if_zero cfg (fuel + 1) rest ps limits stack
        (prefixFrame (emptyLoopFrame frame stack.size WNear.Binary.UnwrapState.Copy.loopBody code)
          out source (UInt32.ofNat 1)) callers [] 0 post cb endNext
      have branchNext : WP cfg ((fuel + 1) + 1) (.next (atCode ps limits
          (stack.push (.i32 (UInt32.ofNat 1 + 4294967295)))
          (prefixFrame (emptyLoopFrame frame stack.size WNear.Binary.UnwrapState.Copy.loopBody code)
            out source (UInt32.ofNat 1)) callers [.br_if 0])) (cfg.regularOpCost + rest) post := branch
      have prefixRule := wp_iteration_prefix cfg ((fuel + 1) + 1) (cfg.regularOpCost + rest) s limits stack
        (emptyLoopFrame frame stack.size WNear.Binary.UnwrapState.Copy.loopBody code) callers [.br_if 0]
        out source (UInt32.ofNat 1) mi index memory post
      have prefixEnv := prefixRule hout hsource hcount hmodule hindex hmemory hr hw
      have result := prefixEnv cp branchNext
      rw [← loop_decomposition] at result
      have budget : 16 * cfg.regularOpCost + (cfg.regularOpCost + rest) = (18 * (0 + 1) - 1) * cfg.regularOpCost + rest := by omega
      rw [budget] at result
      simpa only [Nat.add_assoc, Nat.reduceAdd, Nat.reduceMul] using result
    · have hnPositive : 0 < n := by omega
      let mem1 := writeByte memory out.toNat (readByteWord memory source.toNat)
      let next := chargedStore ps (2 * cfg.regularOpCost)
      let remaining := (18 * n - 1) * cfg.regularOpCost + rest
      have costEq := loop_cost_step cfg.regularOpCost n hnPositive
      have cp : s.host.gas.Credits (16 * cfg.regularOpCost + (2 * cfg.regularOpCost + remaining)) := by
        simpa only [costEq, Nat.add_assoc, remaining] using hc
      have cb : ps.host.gas.Credits (2 * cfg.regularOpCost + remaining) := prefixStore_credits _ _ _ _ _ _ _ cp
      have cn : next.host.gas.Credits remaining := WNear.Proofs.StorePair.charged_credits ps _ _ cb
      have hs := writeByte_spec memory out.toNat (readByteWord memory source.toNat) hwf hw
      have outNext : (out + 1).toNat = out.toNat + 1 := pointer_next out (by omega)
      have sourceNext : (source + 1).toNat = source.toNat + 1 := pointer_next source (by omega)
      have memNext : next.mems[index]? = some mem1 := by
        simpa only [next, chargedStore_mems] using prefixStore_memory s cfg.regularOpCost index out source memory hmemory
      have moduleNext : next.modules[pf.inst]? = some mi := by
        simpa only [next, ps, pf, prefixStore, prefixFrame, byteStore, storeByte, paid, chargedStore] using hmodule
      have cap : 3 < frame.locals.size := (Array.getElem?_eq_some_iff.mp hout).1
      have outLocal : pf.locals[3]? = some (.i32 (out + 1)) := by simp [pf, prefixFrame, cap]
      have sourceLocal : pf.locals[1]? = some (.i32 (source + 1)) := by
        simp [pf, prefixFrame, show 1 < frame.locals.size by omega]
      have countLocal : pf.locals[2]? = some (.i32 (UInt32.ofNat n)) := by
        have raw : pf.locals[2]? = some (.i32 (UInt32.ofNat (n + 1) + 4294967295)) := by
          simp [pf, prefixFrame, show 2 < frame.locals.size by omega]
        rw [raw, count_decrement n hcountWidth]
      have widthNext : mem1.byteSize ≤ 2 ^ 32 := by rw [show mem1.byteSize = memory.byteSize from hs.2.1]; exact hwidth
      have readNext : (source + 1).toNat + n ≤ mem1.byteSize := by rw [sourceNext, show mem1.byteSize = memory.byteSize from hs.2.1]; omega
      have writeNext : (out + 1).toNat + n ≤ mem1.byteSize := by rw [outNext, show mem1.byteSize = memory.byteSize from hs.2.1]; omega
      have countWidthNext : n < 2 ^ 32 := by omega
      have nextContinuation : WP cfg fuel (.next (atCode
          (loopStore next cfg.regularOpCost index (out + 1) (source + 1) mem1 n) limits stack
          (loopFrame pf (out + 1) (source + 1) n) callers code)) rest post := by
        rw [loopStore_succ, ite_eq_right hn, loopFrame_succ] at hnext
        exact hnext
      have recurse := ih next pf (out + 1) (source + 1) mem1 outLocal sourceLocal countLocal moduleNext memNext hs.1
        hnPositive countWidthNext widthNext readNext writeNext cn nextContinuation
      have condition : UInt32.ofNat (n + 1) + 4294967295 ≠ 0 := by
        rw [count_decrement n hcountWidth]
        exact count_nonzero n hnPositive countWidthNext
      have branchRule := wp_br_if_loop_nonzero cfg (fuel + (17 * n + 1)) remaining ps limits stack pf callers
        WNear.Binary.UnwrapState.Copy.loopBody code [] (UInt32.ofNat (n + 1) + 4294967295) post condition cb recurse
      have branchNext : WP cfg ((fuel + (17 * n + 1)) + 1) (.next (atCode ps limits
          (stack.push (.i32 (UInt32.ofNat (n + 1) + 4294967295)))
          (prefixFrame (emptyLoopFrame frame stack.size WNear.Binary.UnwrapState.Copy.loopBody code)
            out source (UInt32.ofNat (n + 1))) callers [.br_if 0])) (2 * cfg.regularOpCost + remaining) post := branchRule
      have prefixRule := wp_iteration_prefix cfg ((fuel + (17 * n + 1)) + 1) (2 * cfg.regularOpCost + remaining) s limits stack
        (emptyLoopFrame frame stack.size WNear.Binary.UnwrapState.Copy.loopBody code) callers [.br_if 0]
        out source (UInt32.ofNat (n + 1)) mi index memory post
      have prefixEnv := prefixRule hout hsource hcount hmodule hindex hmemory hr hw
      have result := prefixEnv cp branchNext
      rw [← loop_decomposition] at result
      have budget : 16 * cfg.regularOpCost + (2 * cfg.regularOpCost + remaining) =
          (18 * (n + 1) - 1) * cfg.regularOpCost + rest := by
        simpa only [remaining, Nat.add_assoc] using congrArg (· + rest) costEq.symm
      rw [budget, loop_fuel_step] at result
      exact result

end WNear.Proofs.UnwrapStateCopy
