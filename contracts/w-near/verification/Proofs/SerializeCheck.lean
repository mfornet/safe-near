import Binary.SerializeHelpers
import Proofs.ValueReturnBorrow

/-! Actual f365 successful formatting-status guard. -/
namespace WNear.Proofs.SerializeCheck
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
open ValueReturnBorrow (wp_reserve wp_restore paid_add)
set_option maxRecDepth 16384
set_option maxHeartbeats 300000
attribute [local irreducible] WP
abbrev after := ValueReturnBorrow.checkedStore
theorem wp_zero_guard (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame)
    (callers : List CallFrame) (code : List Instr) (post : Post)
    (hstatus : frame.locals[0]? = some (.i32 0))
    (hc : s.host.gas.Credits (3 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 3) limits
      stack frame callers code)) rest post) :
    WP cfg (fuel + 3) (.next (atCode s limits stack
      (emptyBlockFrame frame stack.size code) callers
      ([.local_get 0, .i32_eqz, .br_if 0] ++ WNear.Binary.SerializeHelpers.panic)))
      (3 * cfg.regularOpCost + rest) post := by
  rw [show 3 * cfg.regularOpCost + rest = cfg.regularOpCost + (2 * cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 2) _ s limits stack (emptyBlockFrame frame stack.size code)
    callers _ 0 (.i32 0) post hstatus (hc.mono (by omega))
  rw [show 2 * cfg.regularOpCost + rest = cfg.regularOpCost + (cfg.regularOpCost + rest) by omega]
  apply wp_i32_eqz cfg (fuel + 1) _ (paid s cfg.regularOpCost 1) limits stack
    (emptyBlockFrame frame stack.size code) callers _ 0 post
  · exact paid_credits s cfg.regularOpCost 1 _ (hc.mono (by omega))
  apply wp_br_if_block_nonzero cfg fuel rest (paid s cfg.regularOpCost 2) limits stack frame callers
    code WNear.Binary.SerializeHelpers.panic _ post (by decide)
  · exact paid_credits s cfg.regularOpCost 2 _ (hc.mono (by omega))
  · exact hnext

theorem wp_body (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame)
    (callers : List CallFrame) (code : List Instr) (mi : ModuleInst) (index : Nat)
    (global : GlobalInst) (sp : UInt32) (post : Post)
    (hstatus : frame.locals[0]? = some (.i32 0)) (hsize : 2 ≤ frame.locals.size)
    (hmodule : s.modules[frame.inst]? = some mi) (hindex : mi.globalAddrs[0]? = some index)
    (hglobal : s.globals[index]? = some global) (hsp : global.value = .i32 sp)
    (hc : s.host.gas.Credits (12 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (after s cfg.regularOpCost index sp) limits stack
      {frame with locals := frame.locals.set! 1 (.i32 (sp - 16))} callers code)) rest post) :
    WP cfg (fuel + 13) (.next (atCode s limits stack frame callers
      (WNear.Binary.SerializeHelpers.checkBody ++ code))) (12 * cfg.regularOpCost + rest) post := by
  let reserved := setGlobal (paid s cfg.regularOpCost 5) index (.i32 (sp - 16))
  let nextFrame := {frame with locals := frame.locals.set! 1 (.i32 (sp - 16))}
  have hr : reserved.host.gas.Credits (7 * cfg.regularOpCost + rest) :=
    paid_credits s cfg.regularOpCost 5 _ (hc.mono (by omega))
  have hmoduleR : reserved.modules[frame.inst]? = some mi := by simpa only [reserved, setGlobal, paid, chargedStore] using hmodule
  have hglobalR : reserved.globals[index]? = some {global with value := .i32 (sp - 16)} := by
    simp [reserved, setGlobal, hglobal, paid, chargedStore, Array.getElem?_modify]
  have hstatusR : nextFrame.locals[0]? = some (.i32 0) := by
    simpa [nextFrame] using hstatus
  have hscratch : nextFrame.locals[1]? = some (.i32 (sp - 16)) := by
    simp [nextFrame, show 1 < frame.locals.size by omega]
  have hrestore := wp_restore cfg fuel rest (paid reserved cfg.regularOpCost 3) limits stack nextFrame callers code mi index
    {global with value := .i32 (sp - 16)} (sp - 16) 1 post hscratch
    (by simpa only [paid, chargedStore] using hmoduleR) hindex
    (by simpa only [paid, chargedStore] using hglobalR)
    (paid_credits reserved cfg.regularOpCost 3 _ (hr.mono (by omega)))
  have htail : WP cfg (fuel + 4) (.next (atCode (paid reserved cfg.regularOpCost 3) limits stack
      nextFrame callers (WNear.Binary.ValueReturnBorrow.checkEpilogue ++ code)))
      (4 * cfg.regularOpCost + rest) post := by
    have hpost : WP cfg fuel (.next (atCode
        (setGlobal (paid (paid reserved cfg.regularOpCost 3) cfg.regularOpCost 4) index (.i32 (sp - 16 + 16)))
        limits stack nextFrame callers code)) rest post := by
      simpa only [UInt32.sub_add_cancel, paid_add, after, ValueReturnBorrow.checkedStore, Nat.reduceAdd, reserved, nextFrame] using hnext
    simpa only [WNear.Binary.ValueReturnBorrow.checkEpilogue] using hrestore hpost
  have hguard := wp_zero_guard cfg (fuel + 4) (4 * cfg.regularOpCost + rest) reserved limits stack nextFrame callers
    (WNear.Binary.ValueReturnBorrow.checkEpilogue ++ code) post hstatusR
    (hr.mono (by omega)) htail
  rw [show fuel + 4 + 3 = fuel + 7 by omega,
    show 3 * cfg.regularOpCost + (4 * cfg.regularOpCost + rest) = 7 * cfg.regularOpCost + rest by omega] at hguard
  have hblock := wp_block_empty cfg (fuel + 7) (7 * cfg.regularOpCost + rest) reserved limits stack nextFrame callers
    ([.local_get 0, .i32_eqz, .br_if 0] ++ WNear.Binary.SerializeHelpers.panic)
    (WNear.Binary.ValueReturnBorrow.checkEpilogue ++ code) post hr
  have hblock' := hblock hguard
  rw [show fuel + 7 + 1 = fuel + 8 by omega] at hblock'
  have hentry := wp_reserve cfg (fuel + 8) (7 * cfg.regularOpCost + rest) s limits stack frame callers
    (.block .empty ([.local_get 0, .i32_eqz, .br_if 0] ++ WNear.Binary.SerializeHelpers.panic) ::
      (WNear.Binary.ValueReturnBorrow.checkEpilogue ++ code)) mi index global sp 1 post hmodule hindex hglobal hsp
    (hc.mono (by omega))
  have hentry' := hentry hblock'
  rw [show fuel + 8 + 5 = fuel + 13 by omega,
    show 5 * cfg.regularOpCost + (7 * cfg.regularOpCost + rest) = 12 * cfg.regularOpCost + rest by omega] at hentry'
  simpa only [WNear.Binary.SerializeHelpers.checkBody,
    WNear.Binary.ValueReturnBorrow.checkPrologue, WNear.Binary.ValueReturnBorrow.checkEpilogue, List.append_assoc, List.cons_append, List.nil_append] using hentry'



def entered (s : Store NearState) (op : Nat) := chargedStore (chargedStore s op) (9 * op)
def callAfter (s : Store NearState) (op index : Nat) (sp : UInt32) := after (entered s op) op index sp

theorem callAfter_credits (s : Store NearState) (op index rest : Nat) (sp : UInt32)
    (hc : s.host.gas.Credits (22 * op + rest)) : (callAfter s op index sp).host.gas.Credits rest := by
  have co := StorePair.charged_credits s op (9 * op + (12 * op + rest)) (hc.mono (by omega))
  have ca := StorePair.charged_credits (chargedStore s op) (9 * op) (12 * op + rest) co
  exact (ValueReturnBorrow.checkedStore_gas (entered s op) op index rest sp ca).2.2

/-- Complete actual successful formatting-status check. No panic callee, SP
lower bound or memory span is a premise, because no memory access is executed. -/
theorem wp_call (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (mi : ModuleInst) (index address : Nat) (global : GlobalInst) (sp : UInt32) (post : Post)
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.globalAddrs[0]? = some index)
    (hg : s.globals[index]? = some global) (hsp : global.value = .i32 sp)
    (hfi : mi.funcAddrs[365]? = some address)
    (hf : s.funcs[address]? = some (.wasm WNear.Binary.SerializeHelpers.checkSignature frame.inst WNear.Binary.SerializeHelpers.checkFunction))
    (hd : callers.length + 1 < limits.maxCallDepth)
    (hc : s.host.gas.Credits (22 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (callAfter s cfg.regularOpCost index sp) limits base.toArray frame callers code)) rest post) :
    WP cfg (fuel + 15) (.next (atCode s limits (base ++ [Value.i32 0]).toArray frame callers (.call 365 :: code)))
      (22 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let active := entered s op
  let leaf : CallFrame := {locals := #[Value.i32 0, .i32 0], inst := frame.inst, arity := 0, height := base.length, labels := [], code := []}
  let updated := {leaf with locals := leaf.locals.set! 1 (.i32 (sp - 16))}
  let saved := {frame with code}
  have co := StorePair.charged_credits s op (9 * op + (12 * op + rest)) (hc.mono (by dsimp [op]; omega))
  have ca := StorePair.charged_credits (chargedStore s op) (9 * op) (12 * op + rest) co
  have cf := callAfter_credits s op index rest sp hc
  have leaving := wp_leave_wasm cfg fuel rest (callAfter s op index sp) limits base [] updated saved callers post rfl rfl rfl cf
  have resume : WP cfg fuel (.next (atCode (callAfter s op index sp) limits (base ++ []).toArray saved callers saved.code)) rest post := by
    simpa only [saved, atCode, op, List.append_nil] using hnext
  have left := leaving resume
  have hm' : active.modules[leaf.inst]? = some mi := by simpa only [active, entered, chargedStore, leaf] using hm
  have hg' : active.globals[index]? = some global := by simpa only [active, entered, chargedStore] using hg
  have bodyNext : WP cfg (fuel + 1) (.next (atCode (after active op index sp) limits base.toArray {leaf with locals := leaf.locals.set! 1 (.i32 (sp - 16))} (saved :: callers) [])) rest post := by
    simpa only [callAfter, active, updated, List.append_nil] using left
  have body := wp_body cfg (fuel + 1) rest active limits base.toArray leaf (saved :: callers) [] mi index global sp post rfl (by simp [leaf]) hm' hi hg' hsp ca bodyNext
  have rule := wp_call_wasm cfg ((fuel + 1) + 13) (12 * op + rest) s limits base [.i32 0] frame callers code 365 address mi
    WNear.Binary.SerializeHelpers.checkSignature frame.inst WNear.Binary.SerializeHelpers.checkFunction post hm hfi hf rfl hd
  have ha : activationGas op (wasmLocals WNear.Binary.SerializeHelpers.checkFunction [.i32 0]) = 9 * op := by
    simp [activationGas, wasmLocals, WNear.Binary.SerializeHelpers.checkFunction, ValType.default]
  rw [ha] at rule
  have arrays : #[Value.i32 0] ++ #[Value.i32 0] = #[Value.i32 0, Value.i32 0] := by apply Array.toList_inj.mp; simp
  have next : WP cfg ((fuel + 1) + 13) (.next (wasmCallee active limits base frame callers code WNear.Binary.SerializeHelpers.checkSignature frame.inst WNear.Binary.SerializeHelpers.checkFunction [.i32 0])) (12 * op + rest) post := by
    simpa only [wasmCallee, wasmLocals, WNear.Binary.SerializeHelpers.checkFunction, WNear.Binary.SerializeHelpers.checkSignature, leaf, saved, atCode,
      List.map_cons, List.map_nil, ValType.default, List.append_nil, List.length_nil, arrays] using body
  have result := rule (hc.mono (by dsimp [op]; omega)) next
  simpa only [Nat.add_assoc, Nat.reduceAdd, show cfg.regularOpCost + (9 * op + (12 * op + rest)) = 22 * cfg.regularOpCost + rest by dsimp [op]; omega] using result

theorem callAfter_resources (s : Store NearState) (op index : Nat) (sp : UInt32) (global : GlobalInst)
    (hg : s.globals[index]? = some global) (hsp : global.value = .i32 sp) :
    {callAfter s op index sp with host := s.host} = s := by
  have h := ValueReturnBorrow.checkedStore_resources (entered s op) op index sp global hg hsp
  have h' := congrArg (fun t : Store NearState => {t with host := s.host}) h
  simpa only [callAfter, after, entered, chargedStore] using h'
end WNear.Proofs.SerializeCheck
