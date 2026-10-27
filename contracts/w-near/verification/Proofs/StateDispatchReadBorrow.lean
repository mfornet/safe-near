import Proofs.StateDispatchBorrow

/-! Actual f435 nine-op record copy and selected nonnull call. -/
namespace WNear.Proofs.StateDispatchReadBorrow
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
attribute [local irreducible] WP atCode readI32 writeI32
set_option maxRecDepth 16384

def highMemory (memory : Memory) (scratch : UInt32) := writeI32 memory (scratch.toNat + 12) (readI32 memory (scratch.toNat + 4))
def pointer (memory : Memory) (scratch : UInt32) := readI32 (highMemory memory scratch) scratch.toNat
def lowMemory (memory : Memory) (scratch : UInt32) := writeI32 (highMemory memory scratch) (scratch.toNat + 8) (pointer memory scratch)
def selected (memory : Memory) (scratch : UInt32) := if readI32 (lowMemory memory scratch) (pointer memory scratch).toNat ≠ 0 then pointer memory scratch else 0
def high (s : Store NearState) (op index : Nat) (memory : Memory) (scratch : UInt32) := storeI32 (paid s op 4) index (scratch.toNat + 12) memory (readI32 memory (scratch.toNat + 4))
def low (s : Store NearState) (op index : Nat) (memory : Memory) (scratch : UInt32) := storeI32 (paid (high s op index memory scratch) op 5) index (scratch.toNat + 8) (highMemory memory scratch) (pointer memory scratch)
def after (s : Store NearState) (op index : Nat) (memory : Memory) (scratch : UInt32) := ValueReturnOuter.nonnullAfter (paid (paid (low s op index memory scratch) op 2) op 6) op
def copiedFrame (frame : CallFrame) (memory : Memory) (scratch : UInt32) := {frame with locals := frame.locals.set! 4 (.i32 (pointer memory scratch))}

def finalFrame (frame : CallFrame) (memory : Memory) (scratch : UInt32) :=
  {copiedFrame frame memory scratch with locals := (copiedFrame frame memory scratch).locals.set! 0 (.i32 0)}

private theorem wp_copy_record_high (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (scratch : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (hl : frame.locals[3]? = some (.i32 scratch)) (hm : s.modules[frame.inst]? = some mi)
    (hi : mi.memAddrs[0]? = some index) (hmem : s.mems[index]? = some memory)
    (hb : scratch.toNat + 16 ≤ memory.byteSize)
    (hc : s.host.gas.Credits (4 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode
      (storeI32 (paid s cfg.regularOpCost 4) index (scratch.toNat + 12) memory (readI32 memory (scratch.toNat + 4)))
      limits stack frame callers code)) rest post) :
    WP cfg (fuel + 4) (.next (atCode s limits stack frame callers
      ([.local_get 3, .local_get 3, .load .i32 none {align := 2, offset := 4},
        .store .i32 none {align := 2, offset := 12}] ++ code))) (4 * cfg.regularOpCost + rest) post := by
  have hm2 : (paid s cfg.regularOpCost 2).modules[frame.inst]? = some mi := by simpa only [paid, chargedStore] using hm
  have hm3 : (paid s cfg.regularOpCost 3).modules[frame.inst]? = some mi := by simpa only [paid, chargedStore] using hm
  have hmem2 : (paid s cfg.regularOpCost 2).mems[index]? = some memory := by simpa only [paid, chargedStore] using hmem
  have hmem3 : (paid s cfg.regularOpCost 3).mems[index]? = some memory := by simpa only [paid, chargedStore] using hmem
  rw [show 4 * cfg.regularOpCost + rest = cfg.regularOpCost + (3 * cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 3) _ s limits stack frame callers _ 3 (.i32 scratch) post hl (hc.mono (by omega))
  rw [show 3 * cfg.regularOpCost + rest = cfg.regularOpCost + (2 * cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 2) _ (paid s cfg.regularOpCost 1) limits _ frame callers _ 3 (.i32 scratch) post hl
  · apply paid_credits; exact hc.mono (by omega)
  rw [show 2 * cfg.regularOpCost + rest = cfg.regularOpCost + (cfg.regularOpCost + rest) by omega]
  apply wp_i32_load cfg (fuel + 1) _ (paid s cfg.regularOpCost 2) limits _ frame callers _
    {align := 2, offset := 4} scratch mi index memory post hm2 hi hmem2 (by dsimp only; omega)
  · apply paid_credits; exact hc.mono (by omega)
  apply wp_i32_store cfg fuel rest (paid s cfg.regularOpCost 3) limits stack frame callers code
    {align := 2, offset := 12} scratch (readI32 memory (scratch.toNat + 4)) mi index memory post hm3 hi hmem3 (by dsimp only; omega)
  · apply paid_credits; exact hc.mono (by omega)
  · exact hnext

 theorem wp_borrow (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (mi : ModuleInst) (index address : Nat) (memory : Memory) (scratch : UInt32) (post : Post)
    (hl : frame.locals[3]? = some (.i32 scratch)) (hn : 5 ≤ frame.locals.size)
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.memAddrs[0]? = some index) (hmem : s.mems[index]? = some memory)
    (ha : mi.funcAddrs[430]? = some address)
    (hf : s.funcs[address]? = some (.wasm WNear.Binary.ValueReturnBorrow.nonnullSignature frame.inst WNear.Binary.ValueReturnBorrow.nonnullFunction))
    (hh : scratch.toNat + 16 ≤ memory.byteSize) (hlow : scratch.toNat + 12 ≤ (highMemory memory scratch).byteSize)
    (hb : (pointer memory scratch).toNat + 4 ≤ (lowMemory memory scratch).byteSize) (hsel : selected memory scratch ≠ 0)
    (hd : callers.length + 1 < limits.maxCallDepth)
    (hc : s.host.gas.Credits (30 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (after s cfg.regularOpCost index memory scratch) limits
      (base.toArray.push (.i32 (selected memory scratch))) (finalFrame frame memory scratch) callers code)) rest post) :
    WP cfg (fuel + 23) (.next (atCode s limits base.toArray frame callers
      ([.local_get 3,.local_get 3,.load .i32 none {align := 2,offset := 4},.store .i32 none {align := 2,offset := 12},
        .local_get 3,.local_get 3,.load .i32 none {align := 2,offset := 0},.local_tee 4,.store .i32 none {align := 2,offset := 8},
        .i32_const 0,.local_set 0,.local_get 4,.i32_const 0,.local_get 4,.load .i32 none {align := 2,offset := 0},.select none,.i32_const 1055208,.call 430] ++ code)))
      (30 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let sh := high s op index memory scratch
  let sl := low s op index memory scratch
  let ss := paid sl op 2
  let ps := paid ss op 6
  let f := finalFrame frame memory scratch
  have ch : sh.host.gas.Credits (26 * op + rest) := paid_credits s op 4 _ (hc.mono (by dsimp [op]; omega))
  have cl : sl.host.gas.Credits (21 * op + rest) := paid_credits sh op 5 _ (ch.mono (by omega))
  have css : ss.host.gas.Credits (19 * op + rest) := paid_credits sl op 2 _ (cl.mono (by omega))
  have cs : ps.host.gas.Credits (13 * op + rest) := paid_credits ss op 6 _ (css.mono (by omega))
  have mh : (paid s op 4).mems[index]? = some memory := by simpa only [paid,chargedStore] using hmem
  have hmh : sh.mems[index]? = some (highMemory memory scratch) := storeI32_memory (paid s op 4) index (scratch.toNat + 12) memory (readI32 memory (scratch.toNat + 4)) mh
  have ml : (paid sh op 5).mems[index]? = some (highMemory memory scratch) := by simpa only [paid,chargedStore] using hmh
  have hml : sl.mems[index]? = some (lowMemory memory scratch) := storeI32_memory (paid sh op 5) index (scratch.toNat + 8) (highMemory memory scratch) (pointer memory scratch) ml
  have hmsh : sh.modules[frame.inst]? = some mi := by simpa only [sh,high,storeI32_modules,paid,chargedStore] using hm
  have hmsl : sl.modules[f.inst]? = some mi := by simpa only [sl,low,high,storeI32_modules,paid,chargedStore,f,finalFrame,copiedFrame] using hm
  have hfps : ps.funcs[address]? = some (.wasm WNear.Binary.ValueReturnBorrow.nonnullSignature frame.inst WNear.Binary.ValueReturnBorrow.nonnullFunction) := by
    simpa only [ps,ss,sl,low,high,storeI32_funcs,paid,chargedStore] using hf
  have hmps : ps.modules[f.inst]? = some mi := by simpa only [ps,ss,paid,chargedStore] using hmsl
  have hptr : f.locals[4]? = some (.i32 (pointer memory scratch)) := by simp [f,finalFrame,copiedFrame,show 4 < frame.locals.size by omega]
  have stackEq : (base ++ [Value.i32 (selected memory scratch)]).toArray = base.toArray.push (.i32 (selected memory scratch)) := by apply Array.toList_inj.mp; simp
  have cn : WP cfg fuel (.next (atCode (ValueReturnOuter.nonnullAfter ps op) limits (base ++ [Value.i32 (selected memory scratch)]).toArray f callers code)) rest post := by
    simpa only [after,ps,sl,op,f,stackEq] using hnext
  have call := ValueReturnOuter.wp_call_nonnull cfg fuel rest ps limits base f callers code (selected memory scratch) 1055208 address frame.inst mi post hmps ha hfps hsel hd cs cn
  have cnext : WP cfg (fuel + 6) (.next (atCode ps limits
      ((base.toArray.push (.i32 (selected memory scratch))).push (.i32 1055208)) f callers (.call 430 :: code))) (13 * op + rest) post := by
    have argsEq : (base ++ [Value.i32 (selected memory scratch),.i32 1055208]).toArray =
        (base.toArray.push (.i32 (selected memory scratch))).push (.i32 1055208) := by apply Array.toList_inj.mp; simp
    simpa only [argsEq,op] using call
  have selectRule := StateDispatchBorrow.wp_select_record cfg (fuel + 6) (13 * op + rest) ss limits base.toArray f callers (.call 430 :: code)
    4 1055208 (pointer memory scratch) mi index (lowMemory memory scratch) post hptr (by simpa only [ss,paid,chargedStore] using hmsl) hi (by simpa only [ss,paid,chargedStore] using hml) hb (css.mono (by dsimp [op]; omega)) cnext
  have sn : WP cfg (fuel + 12) (.next (atCode ss limits base.toArray f callers
      ([.local_get 4,.i32_const 0,.local_get 4,.load .i32 none {align := 2,offset := 0},.select none,.i32_const 1055208,.call 430] ++ code))) (19 * op + rest) post := by
    simpa only [selected,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd,
      show 6 * cfg.regularOpCost + (13 * op + rest) = 19 * op + rest by dsimp [op]; omega] using selectRule
  have setNext : WP cfg (fuel + 12) (.next (atCode (paid sl op 2) limits base.toArray
      {(copiedFrame frame memory scratch) with locals := (copiedFrame frame memory scratch).locals.set! 0 (.i32 0)} callers
      ([.local_get 4,.i32_const 0,.local_get 4,.load .i32 none {align := 2,offset := 0},.select none,.i32_const 1055208,.call 430] ++ code))) (19 * op + rest) post := by
    simpa only [ss,f,finalFrame] using sn
  have set := wp_local_set cfg (fuel + 12) (19 * op + rest) (paid sl op 1) limits base.toArray (copiedFrame frame memory scratch) callers
    ([.local_get 4,.i32_const 0,.local_get 4,.load .i32 none {align := 2,offset := 0},.select none,.i32_const 1055208,.call 430] ++ code) 0 (.i32 0) post
    (paid_credits sl op 1 _ (cl.mono (by dsimp [op]; omega))) (by simpa only [paid,op] using setNext)
  have status := wp_i32_const cfg (fuel + 13) (op + (19 * op + rest)) sl limits base.toArray (copiedFrame frame memory scratch) callers
    ([.local_set 0,.local_get 4,.i32_const 0,.local_get 4,.load .i32 none {align := 2,offset := 0},.select none,.i32_const 1055208,.call 430] ++ code) 0 post
    (cl.mono (by dsimp [op]; omega)) (by simpa only [paid,op,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd] using set)
  have statusNext : WP cfg (fuel + 14) (.next (atCode sl limits base.toArray (copiedFrame frame memory scratch) callers
      ([.i32_const 0,.local_set 0,.local_get 4,.i32_const 0,.local_get 4,.load .i32 none {align := 2,offset := 0},.select none,.i32_const 1055208,.call 430] ++ code))) (21 * op + rest) post := by
    simpa only [List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd,show cfg.regularOpCost + (op + (19 * op + rest)) = 21 * op + rest by dsimp [op]; omega] using status
  have lowRule := StateDispatchBorrow.wp_copy_record_low cfg (fuel + 14) (21 * op + rest) sh limits base.toArray frame callers
    ([.i32_const 0,.local_set 0,.local_get 4,.i32_const 0,.local_get 4,.load .i32 none {align := 2,offset := 0},.select none,.i32_const 1055208,.call 430] ++ code)
    3 4 scratch mi index (highMemory memory scratch) post hl hmsh hi hmh hlow (ch.mono (by dsimp [op]; omega)) (by simpa only [sl,low,sh,pointer,copiedFrame,op] using statusNext)
  have ln : WP cfg (fuel + 19) (.next (atCode sh limits base.toArray frame callers
      ([.local_get 3,.local_get 3,.load .i32 none {align := 2,offset := 0},.local_tee 4,.store .i32 none {align := 2,offset := 8},
        .i32_const 0,.local_set 0,.local_get 4,.i32_const 0,.local_get 4,.load .i32 none {align := 2,offset := 0},.select none,.i32_const 1055208,.call 430] ++ code))) (26 * op + rest) post := by
    simpa only [List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd,
      show 5 * cfg.regularOpCost + (21 * op + rest) = 26 * op + rest by dsimp [op]; omega] using lowRule
  have first := wp_copy_record_high cfg (fuel + 19) (26 * op + rest) s limits base.toArray frame callers
    ([.local_get 3,.local_get 3,.load .i32 none {align := 2,offset := 0},.local_tee 4,.store .i32 none {align := 2,offset := 8},
      .i32_const 0,.local_set 0,.local_get 4,.i32_const 0,.local_get 4,.load .i32 none {align := 2,offset := 0},.select none,.i32_const 1055208,.call 430] ++ code)
    scratch mi index memory post hl hm hi hmem hh (hc.mono (by dsimp [op]; omega)) (by simpa only [sh,high,op] using ln)
  simpa only [List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd,
    show 4 * cfg.regularOpCost + (26 * op + rest) = 30 * cfg.regularOpCost + rest by dsimp [op]; omega] using first
end WNear.Proofs.StateDispatchReadBorrow
