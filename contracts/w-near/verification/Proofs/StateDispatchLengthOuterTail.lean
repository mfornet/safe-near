import Proofs.InterfaceStack
import NearVM.MeteredWordRules

/-! Actual f524 option stores and shadow-stack restoration, retaining aliases. -/
namespace WNear.Proofs.StateDispatchLengthOuterTail
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
attribute [local irreducible] WP atCode
set_option maxRecDepth 16384

def present (value : UInt64) : UInt64 := (Numeric.bool (Numeric.irelop64 .ne value u64Max)).toUInt64
def highMemory (memory : Memory) (out : UInt32) (value : UInt64) := writeI64 memory (out.toNat + 8) value
def finalMemory (memory : Memory) (out : UInt32) (value : UInt64) := writeI64 (highMemory memory out value) out.toNat (present value)
def highStore (s : Store NearState) (op index : Nat) (memory : Memory) (out : UInt32) (value : UInt64) :=
  storeI64 (paid s op 2) index (out.toNat + 8) memory value
def lowStore (s : Store NearState) (op index : Nat) (memory : Memory) (out : UInt32) (value : UInt64) :=
  storeI64 (paid (highStore s op index memory out value) op 6) index out.toNat (highMemory memory out value) (present value)
def after (s : Store NearState) (op index globalIndex : Nat) (memory : Memory) (out scratch : UInt32) (value : UInt64) :=
  setGlobal (paid (lowStore s op index memory out value) op 4) globalIndex (.i32 (scratch + 16))
def finalFrame (frame : CallFrame) (value : UInt64) := {frame with locals := frame.locals.set! 1 (.i64 value)}
def optionCode : Expr := [.local_tee 1,.store .i64 none {align := 3,offset := 8},.local_get 0,.local_get 1,
  .i64_const u64Max,.i64_relop .ne,.cvt .i64_extend_i32_u,.store .i64 none {align := 3,offset := 0}]
def code : Expr := optionCode ++ [.local_get 2,.i32_const 16,.i32_binop .add,.global_set 0]

theorem present_eq (value : UInt64) : present value = if value ≠ u64Max then 1 else 0 := by
  by_cases h : value = u64Max
  · subst value; rfl
  · simp [present,Numeric.bool,Numeric.irelop64,h]

theorem low_credits (s : Store NearState) (op index rest : Nat) (memory : Memory) (out : UInt32) (value : UInt64)
    (hc : s.host.gas.Credits (8 * op + rest)) : (lowStore s op index memory out value).host.gas.Credits rest := by
  have cut : 2 * op + (6 * op + rest) ≤ 8 * op + rest := by omega
  have h : (highStore s op index memory out value).host.gas.Credits (6 * op + rest) := paid_credits s op 2 _ (hc.mono cut)
  exact paid_credits (highStore s op index memory out value) op 6 rest h

theorem after_credits (s : Store NearState) (op index globalIndex rest : Nat) (memory : Memory)
    (out scratch : UInt32) (value : UInt64) (hc : s.host.gas.Credits (12 * op + rest)) :
    (after s op index globalIndex memory out scratch value).host.gas.Credits rest := by
  have cut : 8 * op + (4 * op + rest) ≤ 12 * op + rest := by omega
  exact paid_credits (lowStore s op index memory out value) op 4 rest (low_credits s op index _ memory out value (hc.mono cut))

private theorem paid_modules (s : Store NearState) (op n : Nat) : (paid s op n).modules = s.modules := by
  induction n with | zero => rfl | succ n ih => exact ih
private theorem paid_mems (s : Store NearState) (op n : Nat) : (paid s op n).mems = s.mems := by
  induction n with | zero => rfl | succ n ih => exact ih

theorem wp_option (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (suffix : Expr) (mi : ModuleInst) (index : Nat) (memory : Memory) (out : UInt32) (value : UInt64) (post : Post)
    (h0 : frame.locals[0]? = some (.i32 out)) (hn : 1 < frame.locals.size)
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.memAddrs[0]? = some index) (hmem : s.mems[index]? = some memory)
    (hw : memory.wf) (hb : out.toNat + 16 ≤ memory.byteSize)
    (hc : s.host.gas.Credits (8 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (lowStore s cfg.regularOpCost index memory out value) limits base
      (finalFrame frame value) callers suffix)) rest post) :
    WP cfg (fuel + 8) (.next (atCode s limits ((base.push (.i32 out)).push (.i64 value)) frame callers (optionCode ++ suffix)))
      (8 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let f := finalFrame frame value
  let high := highStore s op index memory out value
  have hb8 : out.toNat + 8 + 8 ≤ memory.byteSize := by omega
  have hs := writeI64_spec memory (out.toNat + 8) value hw hb8
  have hb0 : out.toNat + 0 + 8 ≤ (highMemory memory out value).byteSize := by rw [show (highMemory memory out value).byteSize = memory.byteSize from hs.2.1]; omega
  have h0' : f.locals[0]? = some (.i32 out) := by simpa [f,finalFrame] using h0
  have h1 : f.locals[1]? = some (.i64 value) := by simp [f,finalFrame,hn]
  have module' (n : Nat) : (paid high op n).modules[f.inst]? = some mi := by
    rw [paid_modules]
    simpa only [high,highStore,storeI64_modules,paid_modules,f,finalFrame] using hm
  have memory' (n : Nat) : (paid high op n).mems[index]? = some (highMemory memory out value) := by
    have m : (paid s op 2).mems[index]? = some memory := by simpa only [paid,chargedStore] using hmem
    have h := storeI64_memory (paid s op 2) index (out.toNat + 8) memory value m
    rw [paid_mems]
    simpa only [high,highStore,highMemory] using h
  have ch : high.host.gas.Credits (6 * op + rest) := paid_credits s op 2 _ (hc.mono (by dsimp [op]; omega))
  have last := wp_i64_store cfg fuel rest (paid high op 5) limits base f callers suffix {align := 3,offset := 0} out (present value)
    mi index (highMemory memory out value) post (module' 5) hi (memory' 5) hb0 (paid_credits high op 5 _ (ch.mono (by omega)))
    (by simpa only [lowStore,high,op,paid,Nat.add_zero] using hnext)
  have ext := wp_i64_extend_i32_u cfg (fuel + 1) (op + rest) (paid high op 4) limits (base.push (.i32 out)) f callers
    (.store .i64 none {align := 3,offset := 0} :: suffix) (Numeric.bool (Numeric.irelop64 .ne value u64Max)) post
    (paid_credits high op 4 _ (ch.mono (by omega))) last
  have cmp := wp_i64_relop cfg (fuel + 2) (op + (op + rest)) (paid high op 3) limits (base.push (.i32 out)) f callers
    (.cvt .i64_extend_i32_u :: .store .i64 none {align := 3,offset := 0} :: suffix) .ne value u64Max post
    (paid_credits high op 3 _ (ch.mono (by omega))) ext
  have max := wp_i64_const cfg (fuel + 3) (op + (op + (op + rest))) (paid high op 2) limits ((base.push (.i32 out)).push (.i64 value)) f callers
    (.i64_relop .ne :: .cvt .i64_extend_i32_u :: .store .i64 none {align := 3,offset := 0} :: suffix) u64Max post
    (paid_credits high op 2 _ (ch.mono (by omega))) cmp
  have get1 := wp_local_get cfg (fuel + 4) (op + (op + (op + (op + rest)))) (paid high op 1) limits (base.push (.i32 out)) f callers
    (.i64_const u64Max :: .i64_relop .ne :: .cvt .i64_extend_i32_u :: .store .i64 none {align := 3,offset := 0} :: suffix) 1 (.i64 value) post h1
    (paid_credits high op 1 _ (ch.mono (by omega))) max
  have get0 := wp_local_get cfg (fuel + 5) (op + (op + (op + (op + (op + rest))))) high limits base f callers
    (.local_get 1 :: .i64_const u64Max :: .i64_relop .ne :: .cvt .i64_extend_i32_u :: .store .i64 none {align := 3,offset := 0} :: suffix) 0 (.i32 out) post h0'
    (ch.mono (by omega)) get1
  have lowNext : WP cfg (fuel + 6) (.next (atCode high limits base f callers
      ([.local_get 0,.local_get 1,.i64_const u64Max,.i64_relop .ne,.cvt .i64_extend_i32_u,.store .i64 none {align := 3,offset := 0}] ++ suffix))) (6 * op + rest) post := by
    simpa only [List.cons_append,List.nil_append,show cfg.regularOpCost + (op + (op + (op + (op + (op + rest))))) = 6 * op + rest by dsimp [op]; omega] using get0
  have highNext := wp_i64_store cfg (fuel + 6) (6 * op + rest) (paid s op 1) limits base f callers
    ([.local_get 0,.local_get 1,.i64_const u64Max,.i64_relop .ne,.cvt .i64_extend_i32_u,.store .i64 none {align := 3,offset := 0}] ++ suffix)
    {align := 3,offset := 8} out value mi index memory post hm hi hmem hb8
    (paid_credits s op 1 _ (hc.mono (by dsimp [op]; omega))) (by simpa only [high,highStore,op,paid] using lowNext)
  have first := wp_local_tee cfg (fuel + 7) (op + (6 * op + rest)) s limits (base.push (.i32 out)) frame callers
    (.store .i64 none {align := 3,offset := 8} :: [.local_get 0,.local_get 1,.i64_const u64Max,.i64_relop .ne,.cvt .i64_extend_i32_u,.store .i64 none {align := 3,offset := 0}] ++ suffix)
    1 (.i64 value) post (hc.mono (by dsimp [op]; omega)) (by simpa only [f,finalFrame,op,paid,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd] using highNext)
  simpa only [optionCode,List.cons_append,List.nil_append,show cfg.regularOpCost + (op + (6 * op + rest)) = 8 * cfg.regularOpCost + rest by dsimp [op]; omega] using first

private theorem paid_globals (s : Store NearState) (op n : Nat) : (paid s op n).globals = s.globals := by
  induction n with | zero => rfl | succ n ih => exact ih

theorem wp_tail (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (suffix : Expr) (mi : ModuleInst) (index globalIndex : Nat) (memory : Memory) (global : GlobalInst)
    (out scratch : UInt32) (value : UInt64) (post : Post)
    (h0 : frame.locals[0]? = some (.i32 out)) (h2 : frame.locals[2]? = some (.i32 scratch))
    (hn : 1 < frame.locals.size) (hm : s.modules[frame.inst]? = some mi)
    (hi : mi.memAddrs[0]? = some index) (hmem : s.mems[index]? = some memory)
    (hgi : mi.globalAddrs[0]? = some globalIndex) (hg : s.globals[globalIndex]? = some global)
    (hw : memory.wf) (hb : out.toNat + 16 ≤ memory.byteSize)
    (hc : s.host.gas.Credits (12 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (after s cfg.regularOpCost index globalIndex memory out scratch value) limits
      base (finalFrame frame value) callers suffix)) rest post) :
    WP cfg (fuel + 12) (.next (atCode s limits ((base.push (.i32 out)).push (.i64 value)) frame callers (code ++ suffix)))
      (12 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  have cut : 8 * op + (4 * op + rest) ≤ 12 * cfg.regularOpCost + rest := by dsimp [op]; omega
  have budget : 8 * cfg.regularOpCost + (4 * op + rest) = 12 * cfg.regularOpCost + rest := by dsimp [op]; omega
  let low := lowStore s op index memory out value
  let f := finalFrame frame value
  have cl : low.host.gas.Credits (4 * op + rest) := low_credits s op index _ memory out value (hc.mono cut)
  have h2' : f.locals[2]? = some (.i32 scratch) := by simpa [f,finalFrame] using h2
  have hml : low.modules[f.inst]? = some mi := by
    simpa only [low,lowStore,highStore,storeI64_modules,paid_modules,f,finalFrame] using hm
  have hgl : low.globals[globalIndex]? = some global := by
    simpa only [low,lowStore,highStore,storeI64_globals,paid_globals] using hg
  have restore := InterfaceStack.wp_restore cfg fuel rest low limits base f callers suffix mi globalIndex global scratch 2 16 post h2' hml hgi hgl cl
    (by simpa only [after,low,op,f] using hnext)
  have pack := wp_option cfg (fuel + 4) (4 * op + rest) s limits base frame callers
    ([.local_get 2,.i32_const 16,.i32_binop .add,.global_set 0] ++ suffix) mi index memory out value post h0 hn hm hi hmem hw hb
    (hc.mono cut) restore
  simpa only [code,List.append_assoc,Nat.add_assoc,Nat.reduceAdd,budget] using pack

end WNear.Proofs.StateDispatchLengthOuterTail
