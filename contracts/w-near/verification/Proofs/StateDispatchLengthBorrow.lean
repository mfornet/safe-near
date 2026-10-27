import Proofs.StateDispatchBorrow

/-! Actual f440 nine-op record copy and selected nonnull call. -/
namespace WNear.Proofs.StateDispatchLengthBorrow
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
def after (s : Store NearState) (op index : Nat) (memory : Memory) (scratch : UInt32) := ValueReturnOuter.nonnullAfter (paid (low s op index memory scratch) op 6) op
def finalFrame (frame : CallFrame) (memory : Memory) (scratch : UInt32) := {frame with locals := frame.locals.set! 0 (.i32 (pointer memory scratch))}

 theorem wp_borrow (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (mi : ModuleInst) (index address : Nat) (memory : Memory) (scratch : UInt32) (post : Post)
    (hl : frame.locals[2]? = some (.i32 scratch)) (hn : 0 < frame.locals.size)
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.memAddrs[0]? = some index) (hmem : s.mems[index]? = some memory)
    (ha : mi.funcAddrs[430]? = some address)
    (hf : s.funcs[address]? = some (.wasm WNear.Binary.ValueReturnBorrow.nonnullSignature frame.inst WNear.Binary.ValueReturnBorrow.nonnullFunction))
    (hh : scratch.toNat + 16 ≤ memory.byteSize) (hlow : scratch.toNat + 12 ≤ (highMemory memory scratch).byteSize)
    (hb : (pointer memory scratch).toNat + 4 ≤ (lowMemory memory scratch).byteSize) (hsel : selected memory scratch ≠ 0)
    (hd : callers.length + 1 < limits.maxCallDepth)
    (hc : s.host.gas.Credits (28 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (after s cfg.regularOpCost index memory scratch) limits
      (base.toArray.push (.i32 (selected memory scratch))) (finalFrame frame memory scratch) callers code)) rest post) :
    WP cfg (fuel + 21) (.next (atCode s limits base.toArray frame callers
      ([.local_get 2,.local_get 2,.load .i32 none {align := 2,offset := 4},.store .i32 none {align := 2,offset := 12},
        .local_get 2,.local_get 2,.load .i32 none {align := 2,offset := 0},.local_tee 0,.store .i32 none {align := 2,offset := 8},
        .local_get 0,.i32_const 0,.local_get 0,.load .i32 none {align := 2,offset := 0},.select none,.i32_const 1055240,.call 430] ++ code)))
      (28 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let sh := high s op index memory scratch
  let sl := low s op index memory scratch
  let ps := paid sl op 6
  let f := finalFrame frame memory scratch
  have ch : sh.host.gas.Credits (24 * op + rest) := paid_credits s op 4 _ (hc.mono (by dsimp [op]; omega))
  have cl : sl.host.gas.Credits (19 * op + rest) := paid_credits sh op 5 _ (ch.mono (by omega))
  have cs : ps.host.gas.Credits (13 * op + rest) := paid_credits sl op 6 _ (cl.mono (by omega))
  have mh : (paid s op 4).mems[index]? = some memory := by simpa only [paid,chargedStore] using hmem
  have hmh : sh.mems[index]? = some (highMemory memory scratch) := storeI32_memory (paid s op 4) index (scratch.toNat + 12) memory (readI32 memory (scratch.toNat + 4)) mh
  have ml : (paid sh op 5).mems[index]? = some (highMemory memory scratch) := by simpa only [paid,chargedStore] using hmh
  have hml : sl.mems[index]? = some (lowMemory memory scratch) := storeI32_memory (paid sh op 5) index (scratch.toNat + 8) (highMemory memory scratch) (pointer memory scratch) ml
  have hmsh : sh.modules[frame.inst]? = some mi := by simpa only [sh,high,storeI32_modules,paid,chargedStore] using hm
  have hmsl : sl.modules[f.inst]? = some mi := by simpa only [sl,low,high,storeI32_modules,paid,chargedStore,f,finalFrame] using hm
  have hfps : ps.funcs[address]? = some (.wasm WNear.Binary.ValueReturnBorrow.nonnullSignature frame.inst WNear.Binary.ValueReturnBorrow.nonnullFunction) := by
    simpa only [ps,sl,low,high,storeI32_funcs,paid,chargedStore] using hf
  have hmps : ps.modules[f.inst]? = some mi := by simpa only [ps,paid,chargedStore] using hmsl
  have hptr : f.locals[0]? = some (.i32 (pointer memory scratch)) := by simp [f,finalFrame,hn]
  have stackEq : (base ++ [Value.i32 (selected memory scratch)]).toArray = base.toArray.push (.i32 (selected memory scratch)) := by apply Array.toList_inj.mp; simp
  have cn : WP cfg fuel (.next (atCode (ValueReturnOuter.nonnullAfter ps op) limits (base ++ [Value.i32 (selected memory scratch)]).toArray f callers code)) rest post := by
    simpa only [after,ps,sl,op,f,stackEq] using hnext
  have call := ValueReturnOuter.wp_call_nonnull cfg fuel rest ps limits base f callers code (selected memory scratch) 1055240 address frame.inst mi post hmps ha hfps hsel hd cs cn
  have cnext : WP cfg (fuel + 6) (.next (atCode ps limits
      ((base.toArray.push (.i32 (selected memory scratch))).push (.i32 1055240)) f callers (.call 430 :: code))) (13 * op + rest) post := by
    have argsEq : (base ++ [Value.i32 (selected memory scratch),.i32 1055240]).toArray =
        (base.toArray.push (.i32 (selected memory scratch))).push (.i32 1055240) := by apply Array.toList_inj.mp; simp
    simpa only [argsEq,op] using call
  have selectRule := StateDispatchBorrow.wp_select_record cfg (fuel + 6) (13 * op + rest) sl limits base.toArray f callers (.call 430 :: code)
    0 1055240 (pointer memory scratch) mi index (lowMemory memory scratch) post hptr hmsl hi hml hb (cl.mono (by dsimp [op]; omega)) cnext
  have sn : WP cfg (fuel + 12) (.next (atCode sl limits base.toArray f callers
      ([.local_get 0,.i32_const 0,.local_get 0,.load .i32 none {align := 2,offset := 0},.select none,.i32_const 1055240,.call 430] ++ code))) (19 * op + rest) post := by
    simpa only [selected,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd,
      show 6 * cfg.regularOpCost + (13 * op + rest) = 19 * op + rest by dsimp [op]; omega] using selectRule
  have lowRule := StateDispatchBorrow.wp_copy_record_low cfg (fuel + 12) (19 * op + rest) sh limits base.toArray frame callers
    ([.local_get 0,.i32_const 0,.local_get 0,.load .i32 none {align := 2,offset := 0},.select none,.i32_const 1055240,.call 430] ++ code)
    2 0 scratch mi index (highMemory memory scratch) post hl hmsh hi hmh hlow (ch.mono (by dsimp [op]; omega)) (by simpa only [sl,low,sh,pointer,f,finalFrame,op] using sn)
  have ln : WP cfg (fuel + 17) (.next (atCode sh limits base.toArray frame callers
      ([.local_get 2,.local_get 2,.load .i32 none {align := 2,offset := 0},.local_tee 0,.store .i32 none {align := 2,offset := 8},
        .local_get 0,.i32_const 0,.local_get 0,.load .i32 none {align := 2,offset := 0},.select none,.i32_const 1055240,.call 430] ++ code))) (24 * op + rest) post := by
    simpa only [List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd,
      show 5 * cfg.regularOpCost + (19 * op + rest) = 24 * op + rest by dsimp [op]; omega] using lowRule
  have first := ValueReturnOuter.wp_copy_record_high cfg (fuel + 17) (24 * op + rest) s limits base.toArray frame callers
    ([.local_get 2,.local_get 2,.load .i32 none {align := 2,offset := 0},.local_tee 0,.store .i32 none {align := 2,offset := 8},
      .local_get 0,.i32_const 0,.local_get 0,.load .i32 none {align := 2,offset := 0},.select none,.i32_const 1055240,.call 430] ++ code)
    scratch mi index memory post hl hm hi hmem hh (hc.mono (by dsimp [op]; omega)) (by simpa only [sh,high,op] using ln)
  simpa only [List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd,
    show 4 * cfg.regularOpCost + (24 * op + rest) = 28 * cfg.regularOpCost + rest by dsimp [op]; omega] using first
end WNear.Proofs.StateDispatchLengthBorrow
