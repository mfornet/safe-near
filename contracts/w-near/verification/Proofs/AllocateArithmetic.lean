import Proofs.AllocateFit

/-! Small checked arithmetic capsules for f580's split guards. -/
namespace WNear.Proofs.Allocate
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
set_option maxHeartbeats 500000
attribute [local irreducible] WP atCode

def rightInstruction (slot : Option Nat) (value : UInt32) : Instr :=
  match slot with | none=>.i32_const value | some index=>.local_get index

def arithmeticGuard (leftSlot : Nat) (rightSlot : Option Nat) (right : UInt32)
    (op : IBinOp) (outputSlot boundSlot : Nat) (comparison : IRelOp) (depth : Nat) : Expr :=
  [.local_get leftSlot,rightInstruction rightSlot right,.i32_binop op,.local_tee outputSlot,
    .local_get boundSlot,.i32_relop comparison,.br_if depth]

/-- A seven-opcode arithmetic/update/overflow check. Its only semantic premises
are the primitive word calculation and comparison, never a guest execution. -/
theorem wp_arithmetic_guard (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (leftSlot : Nat) (rightSlot : Option Nat) (outputSlot boundSlot depth : Nat)
    (left right value bound : UInt32) (operation : IBinOp) (comparison : IRelOp) (post : Post)
    (hl : frame.locals[leftSlot]? = some (.i32 left))
    (hr : ∀ slot, rightSlot = some slot → frame.locals[slot]? = some (.i32 right))
    (hb : frame.locals[boundSlot]? = some (.i32 bound)) (hne : boundSlot ≠ outputSlot)
    (hcalc : Numeric.ibinop32 operation left right = .ok value)
    (hcheck : Numeric.irelop32 comparison value bound = false)
    (hc : s.host.gas.Credits (7*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 7) limits stack
      {frame with locals:=frame.locals.set! outputSlot (.i32 value)} callers code)) rest post) :
    WP cfg (fuel+7) (.next (atCode s limits stack frame callers
      (arithmeticGuard leftSlot rightSlot right operation outputSlot boundSlot comparison depth ++ code)))
      (7*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  let updated : CallFrame := {frame with locals:=frame.locals.set! outputSlot (.i32 value)}
  have hb' : updated.locals[boundSlot]? = some (.i32 bound) := by
    change (frame.locals.setIfInBounds outputSlot (.i32 value))[boundSlot]? = _
    rw [Array.getElem?_setIfInBounds_ne (Ne.symm hne)]
    exact hb
  have tail : WP cfg (fuel+5) (.next (atCode (paid s op 2) limits
      ((stack.push (.i32 left)).push (.i32 right)) frame callers
      (.i32_binop operation::.local_tee outputSlot::.local_get boundSlot::.i32_relop comparison::.br_if depth::code)))
      (5*op+rest) post := by
    rw [show 5*op+rest=cfg.regularOpCost+(4*op+rest) by dsimp [op]; omega]
    apply wp_i32_binop_ok cfg (fuel+4) _ (paid s op 2) limits stack frame callers _ operation left right value post hcalc
    · exact paid_credits s op 2 _ (hc.mono (by dsimp [op]; omega))
    rw [show 4*op+rest=cfg.regularOpCost+(3*op+rest) by dsimp [op]; omega]
    apply wp_local_tee cfg (fuel+3) _ (paid s op 3) limits stack frame callers _ outputSlot (.i32 value) post
    · exact paid_credits s op 3 _ (hc.mono (by dsimp [op]; omega))
    rw [show 3*op+rest=cfg.regularOpCost+(2*op+rest) by dsimp [op]; omega]
    apply wp_local_get cfg (fuel+2) _ (paid s op 4) limits _ updated callers _ boundSlot (.i32 bound) post hb'
    · exact paid_credits s op 4 _ (hc.mono (by dsimp [op]; omega))
    rw [show 2*op+rest=cfg.regularOpCost+(op+rest) by dsimp [op]; omega]
    apply wp_i32_relop cfg (fuel+1) _ (paid s op 5) limits stack updated callers _ comparison value bound post
    · exact paid_credits s op 5 _ (hc.mono (by dsimp [op]; omega))
    simp only [hcheck,Numeric.bool]
    apply wp_br_if_zero cfg fuel rest (paid s op 6) limits stack updated callers code depth post
    · exact paid_credits s op 6 _ (hc.mono (by dsimp [op]; omega))
    · simpa only [updated,op,paid] using hnext
  have second : WP cfg (fuel+6) (.next (atCode (paid s op 1) limits (stack.push (.i32 left)) frame callers
      (rightInstruction rightSlot right::.i32_binop operation::.local_tee outputSlot::.local_get boundSlot::.i32_relop comparison::.br_if depth::code)))
      (6*op+rest) post := by
    have cc := paid_credits s op 1 (op+(5*op+rest)) (hc.mono (by dsimp [op]; omega))
    cases rightSlot with
    | none =>
      have result := wp_i32_const cfg (fuel+5) (5*op+rest) (paid s op 1) limits (stack.push (.i32 left)) frame callers _ right post cc tail
      have cost : cfg.regularOpCost+(5*op+rest)=6*op+rest := by dsimp [op]; omega
      rw [cost] at result
      exact result
    | some index =>
      have lookup := hr index rfl
      have result := wp_local_get cfg (fuel+5) (5*op+rest) (paid s op 1) limits (stack.push (.i32 left)) frame callers _ index (.i32 right) post lookup cc tail
      have cost : cfg.regularOpCost+(5*op+rest)=6*op+rest := by dsimp [op]; omega
      rw [cost] at result
      exact result
  have result := wp_local_get cfg (fuel+6) (6*op+rest) s limits stack frame callers _ leftSlot (.i32 left) post hl
    (hc.mono (by dsimp [op]; omega)) second
  have cost : cfg.regularOpCost+(6*op+rest)=7*cfg.regularOpCost+rest := by dsimp [op]; omega
  rw [cost] at result
  simpa only [arithmeticGuard,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd] using result

/-- Original free-block room implies both actual additions used to compute the
minimum viable split end are non-wrapping. -/
theorem split_base_numbers (memory : Memory) (head words : UInt32) (h : SplitNative memory head words) :
    (head+8).toNat = head.toNat+8 ∧
    (head+8+8).toNat = head.toNat+16 ∧
    Numeric.irelop32 .lt_u (head+8+8) (head+8) = false := by
  have room := h.room
  have finish := UInt32.toNat_lt (endWord memory head)
  have first : (head+8).toNat = head.toNat+8 := by
    rw [UInt32.toNat_add]
    simp only [UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod]
    omega
  have second : (head+8+8).toNat = head.toNat+16 := by
    rw [UInt32.toNat_add,first]
    simp only [UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod]
    omega
  have check : ¬ (head+8+8 < head+8) := by rw [UInt32.lt_iff_toNat_lt,first,second]; omega
  exact ⟨first,second,by simpa [Numeric.irelop32] using check⟩

/-- The actual first seven instructions after f580's quantum callback: reserve
another header-sized prefix and verify that its address did not wrap. -/
theorem wp_split_base (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (memory : Memory) (head words : UInt32) (post : Post)
    (hl : frame.locals[9]? = some (.i32 (head+8))) (hn : SplitNative memory head words)
    (hc : s.host.gas.Credits (7*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 7) limits stack
      {frame with locals:=frame.locals.set! 10 (.i32 (head+8+8))} callers code)) rest post) :
    WP cfg (fuel+7) (.next (atCode s limits stack frame callers
      ([.local_get 9,.i32_const 8,.i32_binop .add,.local_tee 10,.local_get 9,.i32_relop .lt_u,.br_if 2]++code)))
      (7*cfg.regularOpCost+rest) post := by
  have numbers := split_base_numbers memory head words hn
  have noSlot : ∀ slot, (none : Option Nat) = some slot → frame.locals[slot]? = some (.i32 8) := by intro slot impossible; cases impossible
  exact wp_arithmetic_guard cfg fuel rest s limits stack frame callers code 9 none 10 9 2
    (head+8) 8 (head+8+8) (head+8) .add .lt_u post hl noSlot hl (by decide) rfl numbers.2.2 hc hnext

theorem split_minimum_numbers (memory : Memory) (head words : UInt32) (h : SplitNative memory head words) :
    (head+8+8+64).toNat = head.toNat+80 ∧
    Numeric.irelop32 .lt_u (head+8+8+64) (head+8+8) = false ∧
    Numeric.irelop32 .gt_u (head+8+8+64) (splitPointer memory head words) = false := by
  have base := split_base_numbers memory head words h
  have room := h.room
  have finish := UInt32.toNat_lt (endWord memory head)
  have pointer := split_pointer_toNat memory head words h
  have sumNat : (head+8+8+64).toNat = head.toNat+80 := by
    rw [UInt32.toNat_add,base.2.1]
    simp only [UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod]
    omega
  have addCheck : ¬ (head+8+8+64 < head+8+8) := by
    rw [UInt32.lt_iff_toNat_lt,sumNat,base.2.1]; omega
  have fitCheck : ¬ (splitPointer memory head words < head+8+8+64) := by
    rw [UInt32.lt_iff_toNat_lt,sumNat,pointer]; omega
  exact ⟨sumNat,by simpa [Numeric.irelop32] using addCheck,by simpa [Numeric.irelop32] using fitCheck⟩

theorem wp_split_minimum (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (memory : Memory) (head words : UInt32) (post : Post)
    (hl : frame.locals[10]? = some (.i32 (head+8+8))) (hq : frame.locals[13]? = some (.i32 64))
    (hn : SplitNative memory head words) (hc : s.host.gas.Credits (7*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 7) limits stack
      {frame with locals:=frame.locals.set! 13 (.i32 (head+8+8+64))} callers code)) rest post) :
    WP cfg (fuel+7) (.next (atCode s limits stack frame callers
      ([.local_get 10,.local_get 13,.i32_binop .add,.local_tee 13,.local_get 10,.i32_relop .lt_u,.br_if 3]++code)))
      (7*cfg.regularOpCost+rest) post := by
  have numbers := split_minimum_numbers memory head words hn
  have lookup : ∀ slot, (some 13 : Option Nat) = some slot → frame.locals[slot]? = some (.i32 64) := by
    intro slot equality
    cases equality
    exact hq
  exact wp_arithmetic_guard cfg fuel rest s limits stack frame callers code 10 (some 13) 13 10 3
    (head+8+8) 64 (head+8+8+64) (head+8+8) .add .lt_u post hl lookup hl (by decide) rfl numbers.2.1 hc hnext

/-- The mask is the actual alignment-one mask, and the fit comparison follows
from original free-block room. No callback or post-allocation pointer is assumed. -/
theorem wp_split_fit (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (memory : Memory) (head words : UInt32) (post : Post)
    (hmin : frame.locals[13]? = some (.i32 (head+8+8+64)))
    (hp : frame.locals[12]? = some (.i32 (splitPointer memory head words)))
    (hmask : frame.locals[6]? = some (.i32 4294967295))
    (hn : SplitNative memory head words) (hc : s.host.gas.Credits (7*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 7) limits stack
      {frame with locals:=frame.locals.set! 10 (.i32 (splitPointer memory head words))} callers code)) rest post) :
    WP cfg (fuel+7) (.next (atCode s limits stack frame callers
      ([.local_get 13,.local_get 12,.local_get 6,.i32_binop .and,.local_tee 10,.i32_relop .gt_u,.br_if 8]++code)))
      (7*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  let pointer := splitPointer memory head words
  let updated : CallFrame := {frame with locals:=frame.locals.set! 10 (.i32 pointer)}
  have check : Numeric.irelop32 .gt_u (head+8+8+64) pointer = false := (split_minimum_numbers memory head words hn).2.2
  have mask : pointer &&& 4294967295 = pointer := UInt32.and_neg_one
  rw [show 7*cfg.regularOpCost+rest=cfg.regularOpCost+(6*op+rest) by dsimp [op]; omega]
  apply wp_local_get cfg (fuel+6) _ s limits stack frame callers _ 13 (.i32 (head+8+8+64)) post hmin (hc.mono (by dsimp [op]; omega))
  rw [show 6*op+rest=cfg.regularOpCost+(5*op+rest) by dsimp [op]; omega]
  apply wp_local_get cfg (fuel+5) _ (paid s op 1) limits _ frame callers _ 12 (.i32 pointer) post hp
  · exact paid_credits s op 1 _ (hc.mono (by dsimp [op]; omega))
  rw [show 5*op+rest=cfg.regularOpCost+(4*op+rest) by dsimp [op]; omega]
  apply wp_local_get cfg (fuel+4) _ (paid s op 2) limits _ frame callers _ 6 (.i32 4294967295) post hmask
  · exact paid_credits s op 2 _ (hc.mono (by dsimp [op]; omega))
  rw [show 4*op+rest=cfg.regularOpCost+(3*op+rest) by dsimp [op]; omega]
  apply wp_i32_and cfg (fuel+3) _ (paid s op 3) limits (stack.push (.i32 (head+8+8+64))) frame callers _ pointer 4294967295 post
  · exact paid_credits s op 3 _ (hc.mono (by dsimp [op]; omega))
  rw [mask]
  rw [show 3*op+rest=cfg.regularOpCost+(2*op+rest) by dsimp [op]; omega]
  apply wp_local_tee cfg (fuel+2) _ (paid s op 4) limits (stack.push (.i32 (head+8+8+64))) frame callers _ 10 (.i32 pointer) post
  · exact paid_credits s op 4 _ (hc.mono (by dsimp [op]; omega))
  rw [show 2*op+rest=cfg.regularOpCost+(op+rest) by dsimp [op]; omega]
  apply wp_i32_relop cfg (fuel+1) _ (paid s op 5) limits stack updated callers _ .gt_u (head+8+8+64) pointer post
  · exact paid_credits s op 5 _ (hc.mono (by dsimp [op]; omega))
  simp only [check,Numeric.bool]
  apply wp_br_if_zero cfg fuel rest (paid s op 6) limits stack updated callers code 8 post
  · exact paid_credits s op 6 _ (hc.mono (by dsimp [op]; omega))
  · simpa only [updated,pointer,op,paid] using hnext

def splitLength (memory : Memory) (head words : UInt32) := endWord memory head - splitHeader memory head words

theorem split_header_numbers (memory : Memory) (head words : UInt32) (h : SplitNative memory head words) :
    splitPointer memory head words + 4294967288 = splitHeader memory head words ∧
    Numeric.irelop32 .gt_u (splitHeader memory head words) (splitPointer memory head words) = false ∧
    (splitLength memory head words).toNat = words.toNat*4+8 ∧
    Numeric.irelop32 .gt_u (splitLength memory head words) (endWord memory head) = false := by
  have hp := split_pointer_toNat memory head words h
  have hh := split_header_toNat memory head words h
  have room := h.room
  have finish := UInt32.toNat_lt (endWord memory head)
  have eq : splitPointer memory head words + 4294967288 = splitHeader memory head words :=
    (UInt32.sub_eq_add_neg _ 8).symm
  have hc : ¬(splitPointer memory head words < splitHeader memory head words) := by
    rw [UInt32.lt_iff_toNat_lt,hh]; omega
  have length : (splitLength memory head words).toNat = words.toNat*4+8 := by
    unfold splitLength
    rw [UInt32.toNat_sub,hh]
    omega
  have lc : ¬(endWord memory head < splitLength memory head words) := by
    rw [UInt32.lt_iff_toNat_lt,length]; omega
  exact ⟨eq,by simpa [Numeric.irelop32] using hc,length,by simpa [Numeric.irelop32] using lc⟩

theorem wp_split_header (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (memory : Memory) (head words : UInt32) (post : Post)
    (hp : frame.locals[10]? = some (.i32 (splitPointer memory head words)))
    (hn : SplitNative memory head words) (hc : s.host.gas.Credits (7*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 7) limits stack
      {frame with locals:=frame.locals.set! 9 (.i32 (splitHeader memory head words))} callers code)) rest post) :
    WP cfg (fuel+7) (.next (atCode s limits stack frame callers
      ([.local_get 10,.i32_const 4294967288,.i32_binop .add,.local_tee 9,.local_get 10,.i32_relop .gt_u,.br_if 4]++code)))
      (7*cfg.regularOpCost+rest) post := by
  have numbers := split_header_numbers memory head words hn
  have noSlot : ∀ slot, (none : Option Nat) = some slot → frame.locals[slot]? = some (.i32 4294967288) := by intro slot impossible; cases impossible
  have check : Numeric.irelop32 .gt_u (splitPointer memory head words+4294967288) (splitPointer memory head words) = false := by rw [numbers.1]; exact numbers.2.1
  have next : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 7) limits stack
      {frame with locals:=frame.locals.set! 9 (.i32 (splitPointer memory head words+4294967288))} callers code)) rest post := by rw [numbers.1]; exact hnext
  exact wp_arithmetic_guard cfg fuel rest s limits stack frame callers code 10 none 9 10 4
    (splitPointer memory head words) 4294967288 (splitPointer memory head words+4294967288) (splitPointer memory head words)
    .add .gt_u post hp noSlot hp (by decide) rfl check hc next

theorem wp_split_length (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (memory : Memory) (head words : UInt32) (post : Post)
    (he : frame.locals[11]? = some (.i32 (endWord memory head)))
    (hh : frame.locals[9]? = some (.i32 (splitHeader memory head words)))
    (hn : SplitNative memory head words) (hc : s.host.gas.Credits (7*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 7) limits stack
      {frame with locals:=frame.locals.set! 2 (.i32 (splitLength memory head words))} callers code)) rest post) :
    WP cfg (fuel+7) (.next (atCode s limits stack frame callers
      ([.local_get 11,.local_get 9,.i32_binop .sub,.local_tee 2,.local_get 11,.i32_relop .gt_u,.br_if 5]++code)))
      (7*cfg.regularOpCost+rest) post := by
  have numbers := split_header_numbers memory head words hn
  have lookup : ∀ slot, (some 9 : Option Nat) = some slot → frame.locals[slot]? = some (.i32 (splitHeader memory head words)) := by intro slot equality; cases equality; exact hh
  exact wp_arithmetic_guard cfg fuel rest s limits stack frame callers code 11 (some 9) 2 11 5
    (endWord memory head) (splitHeader memory head words) (splitLength memory head words) (endWord memory head)
    .sub .gt_u post he lookup he (by decide) rfl numbers.2.2.2 hc hnext
end WNear.Proofs.Allocate
