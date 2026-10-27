import Proofs.UnwrapStateCopy
import Proofs.UnwrapStateCopyState
import NearVM.MeteredNumericRules
import NearVM.MeteredWasmCall

/-! Actual setup and typed return of deployed forward byte-copy f951. -/
namespace WNear.Proofs.UnwrapStateCopyEntry
open Wasm Wasm.Near Wasm.Near.MeteredLogic
open WNear.Proofs.StorePairCaller (paid paid_credits)
open WNear.Proofs.UnwrapStateCopy
set_option maxHeartbeats 800000
set_option maxRecDepth 12000

/-- The nonzero count takes the actual zero branch condition, then assigns
local3 from the destination. No block or function execution is assumed. -/
theorem wp_prepare (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (out count : UInt32) (post : Post)
    (hout : frame.locals[0]? = some (.i32 out)) (hcount : frame.locals[2]? = some (.i32 count))
    (hpositive : count ≠ 0) (hc : s.host.gas.Credits (5 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 5) limits stack
      {frame with locals := frame.locals.set! 3 (.i32 out)} callers code)) rest post) :
    WP cfg (fuel + 5) (.next (atCode s limits stack frame callers
      ([.local_get 2, .i32_eqz, .br_if 0, .local_get 0, .local_set 3] ++ code)))
      (5 * cfg.regularOpCost + rest) post := by
  have hz : Numeric.bool (count == 0) = 0 := by simp [Numeric.bool, hpositive]
  rw [show 5 * cfg.regularOpCost + rest = cfg.regularOpCost + (4 * cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 4) (4 * cfg.regularOpCost + rest) s limits stack frame callers _ 2 (.i32 count) post hcount
    (hc.mono (by omega))
  rw [show 4 * cfg.regularOpCost + rest = cfg.regularOpCost + (3 * cfg.regularOpCost + rest) by omega]
  apply wp_i32_eqz cfg (fuel + 3) (3 * cfg.regularOpCost + rest) _ limits stack frame callers _ count post
  · apply paid_credits s cfg.regularOpCost 1; exact hc.mono (by omega)
  rw [hz]
  rw [show 3 * cfg.regularOpCost + rest = cfg.regularOpCost + (2 * cfg.regularOpCost + rest) by omega]
  apply wp_br_if_zero cfg (fuel + 2) (2 * cfg.regularOpCost + rest) _ limits stack frame callers _ 0 post
  · apply paid_credits s cfg.regularOpCost 2; exact hc.mono (by omega)
  rw [show 2 * cfg.regularOpCost + rest = cfg.regularOpCost + (cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 1) (cfg.regularOpCost + rest) _ limits stack frame callers _ 0 (.i32 out) post hout
  · apply paid_credits s cfg.regularOpCost 3; exact hc.mono (by omega)
  apply wp_local_set cfg fuel rest _ limits stack frame callers code 3 (.i32 out) post
  · apply paid_credits s cfg.regularOpCost 4; exact hc.mono (by omega)
  · simpa only [paid] using hnext

/-- Five paid setup instructions followed by actual loop activation. -/
def prepared (s : Store NearState) (op : Nat) : Store NearState := chargedStore (paid s op 5) op

def finalStore (s : Store NearState) (op index : Nat) (out source : UInt32) (memory : Memory) (count : Nat) : Store NearState :=
  chargedStore (loopStore (prepared s op) op index out source memory count) op

def afterFrame (frame : CallFrame) (out source : UInt32) (count : Nat) : CallFrame :=
  loopFrame {frame with locals := frame.locals.set! 3 (.i32 out)} out source count

/-- Typed one-result root frame for the actual memcpy signature. -/
def resultFrame (locals : Array Value) (inst : Nat) : CallFrame :=
  {locals, inst, arity := 1, height := 0, labels := [], code := []}

theorem wp_finish_value (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (locals : Array Value) (inst : Nat) (value : Value) (post : Post)
    (hgas : s.host.gas.Credits rest) (hpost : post rest (.done [value] s) none) :
    WP cfg (fuel + 1) (.next (atCode s limits #[value] (resultFrame locals inst) [] [])) rest post := by
  let c := atCode s limits #[value] (resultFrame locals inst) [] []
  have hz := chargeWasm_zero (.next c) (hgas.mono (Nat.zero_le rest))
  have hc : chargeConfig c 0 = (c, none) := by
    cases he : chargeConfig c 0 with
    | mk c' error =>
      simp only [chargeWasm, he] at hz
      cases hz
      rfl
  have hstep : Exec.step c = .done [value] s := rfl
  have h := wp_pure_next (cfg := cfg) (fuel := fuel) (c := c) (rest := rest) (post := post)
  have hcost : nextInstructionGas cfg c = 0 := rfl
  rw [hcost, hc, hstep] at h
  simp only [Nat.zero_add] at h
  apply h hgas
  · rfl
  · rfl
  · exact wp_done cfg fuel [value] s rest post hgas hpost

theorem body_budget (op count rest : Nat) (hpositive : 0 < count) :
    (18 * count + 6) * op + rest =
      5 * op + (op + ((18 * count - 1) * op + (op + rest))) := by
  have h : 18 * count = 1 + (18 * count - 1) := by omega
  conv_lhs => rw [h]
  simp only [Nat.add_mul, Nat.one_mul]
  omega

theorem body_fuel (fuel count : Nat) : ((fuel + 2 + (17 * count + 1) + 1) + 5) + 1 =
    fuel + (17 * count + 10) := by omega

theorem prepared_credits (s : Store NearState) (op rest : Nat)
    (hc : s.host.gas.Credits (6 * op + rest)) : (prepared s op).host.gas.Credits rest := by
  apply WNear.Proofs.StorePair.charged_credits
  apply paid_credits s op 5
  exact hc.mono (by omega)

/-- Credits at the actual result store, including the final destination read. -/
theorem finalStore_credits (s : Store NearState) (op index : Nat) (out source : UInt32)
    (memory : Memory) (count rest : Nat) (hpositive : 0 < count)
    (hc : s.host.gas.Credits ((18 * count + 6) * op + rest)) :
    (finalStore s op index out source memory count).host.gas.Credits rest := by
  have initial : s.host.gas.Credits
      (5 * op + (op + ((18 * count - 1) * op + (op + rest)))) := by
    rw [← body_budget op count rest hpositive]; exact hc
  have paidSetup := paid_credits s op 5 _ initial
  have loopCredit := WNear.Proofs.StorePair.charged_credits (paid s op 5) op _ paidSetup
  have finished := UnwrapStateCopyState.loopStore_credits (prepared s op) op index out source memory count (op + rest) loopCredit
  exact WNear.Proofs.StorePair.charged_credits _ op rest finished

/-- Complete actual positive-count memcpy body. Setup, loop activation, all
iterations, both free label exits and the destination result are composed. -/
theorem wp_body (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (out source : UInt32) (count : Nat)
    (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (hout : frame.locals[0]? = some (.i32 out)) (hsource : frame.locals[1]? = some (.i32 source))
    (hcount : frame.locals[2]? = some (.i32 (UInt32.ofNat count))) (hsize : 3 < frame.locals.size)
    (hmodule : s.modules[frame.inst]? = some mi) (hindex : mi.memAddrs[0]? = some index)
    (hmemory : s.mems[index]? = some memory) (hwf : memory.wf)
    (hpositive : 0 < count) (hcountWidth : count < 2 ^ 32) (hwidth : memory.byteSize ≤ 2 ^ 32)
    (hread : source.toNat + count ≤ memory.byteSize) (hwrite : out.toNat + count ≤ memory.byteSize)
    (hc : s.host.gas.Credits ((18 * count + 6) * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (finalStore s cfg.regularOpCost index out source memory count)
      limits (stack.push (.i32 out)) (afterFrame frame out source count) callers code)) rest post) :
    WP cfg (fuel + (17 * count + 10)) (.next (atCode s limits stack frame callers
      (WNear.Binary.UnwrapState.Copy.body ++ code))) ((18 * count + 6) * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let base := {frame with locals := frame.locals.set! 3 (.i32 out)}
  let outer := emptyBlockFrame frame stack.size (.local_get 0 :: code)
  let inside := {outer with locals := outer.locals.set! 3 (.i32 out)}
  let copied := loopStore (prepared s op) op index out source memory count
  let doneFrame := afterFrame frame out source count
  let loopBudget := (18 * count - 1) * op + (op + rest)
  have c0 : s.host.gas.Credits (5 * op + (op + loopBudget)) := by
    rw [← body_budget op count rest hpositive]; exact hc
  have c5 := paid_credits s op 5 (op + loopBudget) c0
  have c6 : (prepared s op).host.gas.Credits loopBudget :=
    WNear.Proofs.StorePair.charged_credits (paid s op 5) op loopBudget c5
  have copiedCredits : copied.host.gas.Credits (op + rest) :=
    UnwrapStateCopyState.loopStore_credits (prepared s op) op index out source memory count (op + rest) c6
  have finalLocal : doneFrame.locals[0]? = some (.i32 out) := by
    simpa [doneFrame, afterFrame, UnwrapStateCopyState.loopFrame_local_zero, base] using hout
  have getRule := wp_local_get cfg fuel rest copied limits stack doneFrame callers code 0 (.i32 out) post
  have getLocal := getRule finalLocal
  have getNext : WP cfg fuel (.next (atCode (chargedStore copied op) limits (stack.push (.i32 out))
      doneFrame callers code)) rest post := hnext
  have got := getLocal copiedCredits getNext
  let label : Label := {arity := 0, height := stack.size, rest := .local_get 0 :: code, loop := none}
  have ended := wp_end_label cfg (fuel + 1) (op + rest) copied limits stack doneFrame callers label post copiedCredits got
  have frameResult : loopFrame inside out source count = {doneFrame with labels := label :: doneFrame.labels} := by
    have labels := UnwrapStateCopyState.loopFrame_set_labels base out source count (label :: base.labels)
    simpa only [inside, outer, afterFrame, doneFrame, emptyBlockFrame, base, label,
      UnwrapStateCopyState.loopFrame_labels] using labels
  have loopNext : WP cfg (fuel + 2) (.next (atCode copied limits stack
      (loopFrame inside out source count) callers [])) (op + rest) post := by
    rw [frameResult]
    exact ended
  have outInside : inside.locals[3]? = some (.i32 out) := by simp [inside, outer, emptyBlockFrame, hsize]
  have sourceInside : inside.locals[1]? = some (.i32 source) := by simpa [inside, outer, emptyBlockFrame] using hsource
  have countInside : inside.locals[2]? = some (.i32 (UInt32.ofNat count)) := by simpa [inside, outer, emptyBlockFrame] using hcount
  have hm : (prepared s op).modules[inside.inst]? = some mi := by simpa only [prepared, paid, chargedStore, inside, outer, emptyBlockFrame] using hmodule
  have hmem : (prepared s op).mems[index]? = some memory := by simpa only [prepared, paid, chargedStore] using hmemory
  have loopRule := wp_loop cfg (fuel + 2) (op + rest) (prepared s op) limits stack inside callers [] out source count mi index memory post
  have loopLocals := loopRule outInside sourceInside countInside
  have loopEnv := loopLocals hm hindex hmem hwf
  have loopBounds := loopEnv hpositive hcountWidth hwidth hread hwrite
  have loopPaid := loopBounds c6
  have loopResult := loopPaid loopNext
  have activationRule := wp_loop_empty cfg (fuel + 2 + (17 * count + 1)) loopBudget (paid s op 5)
    limits stack inside callers WNear.Binary.UnwrapState.Copy.loopBody [] post
  have activated := activationRule c5 loopResult
  have setupRule := wp_prepare cfg (fuel + 2 + (17 * count + 1) + 1) (op + loopBudget) s limits stack outer callers
    [.loop .empty WNear.Binary.UnwrapState.Copy.loopBody] out (UInt32.ofNat count) post
  have setupLocals := setupRule hout hcount
  have setupPositive := setupLocals (count_nonzero count hpositive hcountWidth)
  have setup := setupPositive c0 activated
  have blockRule := wp_block_empty cfg ((fuel + 2 + (17 * count + 1) + 1) + 5)
    (5 * op + (op + loopBudget)) s limits stack frame callers
    [.local_get 2, .i32_eqz, .br_if 0, .local_get 0, .local_set 3, .loop .empty WNear.Binary.UnwrapState.Copy.loopBody]
    (.local_get 0 :: code) post
  have whole := blockRule c0 setup
  have budget : 5 * op + (op + loopBudget) = (18 * count + 6) * cfg.regularOpCost + rest :=
    (body_budget op count rest hpositive).symm
  rw [budget, body_fuel] at whole
  simpa only [WNear.Binary.UnwrapState.Copy.body, List.cons_append, List.nil_append] using whole

/-- Complete actual positive-count root return, with the destination value. -/
theorem wp_return (cfg : WasmConfig) (rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (inst : Nat) (out source : UInt32) (count : Nat)
    (mi : ModuleInst) (index : Nat) (memory : Memory)
    (hmodule : s.modules[inst]? = some mi) (hindex : mi.memAddrs[0]? = some index)
    (hmemory : s.mems[index]? = some memory) (hwf : memory.wf)
    (hpositive : 0 < count) (hcountWidth : count < 2 ^ 32) (hwidth : memory.byteSize ≤ 2 ^ 32)
    (hread : source.toNat + count ≤ memory.byteSize) (hwrite : out.toNat + count ≤ memory.byteSize)
    (hc : s.host.gas.Credits ((18 * count + 6) * cfg.regularOpCost + rest)) :
    WP cfg (17 * count + 11) (.next (atCode s limits #[]
      (resultFrame #[Value.i32 out, .i32 source, .i32 (UInt32.ofNat count), .i32 0] inst) [] WNear.Binary.UnwrapState.Copy.body))
      ((18 * count + 6) * cfg.regularOpCost + rest)
      (fun remaining outcome error => remaining = rest ∧
        outcome = .done [Value.i32 out] (finalStore s cfg.regularOpCost index out source memory count) ∧ error = none) := by
  let post : Post := fun remaining outcome error => remaining = rest ∧
    outcome = .done [Value.i32 out] (finalStore s cfg.regularOpCost index out source memory count) ∧ error = none
  let frame := resultFrame #[Value.i32 out, .i32 source, .i32 (UInt32.ofNat count), .i32 0] inst
  have finalCredit := finalStore_credits s cfg.regularOpCost index out source memory count rest hpositive hc
  have finish := wp_finish_value cfg 0 rest (finalStore s cfg.regularOpCost index out source memory count)
    limits (afterFrame frame out source count).locals inst (.i32 out) post finalCredit ⟨rfl, rfl, rfl⟩
  have continuation : WP cfg 1 (.next (atCode (finalStore s cfg.regularOpCost index out source memory count)
      limits #[Value.i32 out] (afterFrame frame out source count) [] [])) rest post := by
    simpa only [atCode, resultFrame, afterFrame, frame, UnwrapStateCopyState.loopFrame_inst,
      UnwrapStateCopyState.loopFrame_arity, UnwrapStateCopyState.loopFrame_height,
      UnwrapStateCopyState.loopFrame_labels] using finish
  have bodyRule := wp_body cfg 1 rest s limits #[] frame [] [] out source count mi index memory post
  have bodyLocals := bodyRule rfl rfl rfl (by simp [frame, resultFrame])
  have bodyEnv := bodyLocals hmodule hindex hmemory hwf
  have bodyBounds := bodyEnv hpositive hcountWidth hwidth hread hwrite
  have result := bodyBounds hc continuation
  have fuel : 1 + (17 * count + 10) = 17 * count + 11 := by omega
  simpa only [List.append_nil, fuel] using result

theorem run_return (cfg : WasmConfig) (rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (inst : Nat) (out source : UInt32) (count : Nat)
    (mi : ModuleInst) (index : Nat) (memory : Memory)
    (hmodule : s.modules[inst]? = some mi) (hindex : mi.memAddrs[0]? = some index)
    (hmemory : s.mems[index]? = some memory) (hwf : memory.wf)
    (hpositive : 0 < count) (hcountWidth : count < 2 ^ 32) (hwidth : memory.byteSize ≤ 2 ^ 32)
    (hread : source.toNat + count ≤ memory.byteSize) (hwrite : out.toNat + count ≤ memory.byteSize)
    (hc : s.host.gas.Credits ((18 * count + 6) * cfg.regularOpCost + rest)) :
    runMetered cfg (17 * count + 11) (.next (atCode s limits #[]
      (resultFrame #[Value.i32 out, .i32 source, .i32 (UInt32.ofNat count), .i32 0] inst) [] WNear.Binary.UnwrapState.Copy.body)) =
      (.done [Value.i32 out] (finalStore s cfg.regularOpCost index out source memory count), none) := by
  have h := wp_return cfg rest s limits inst out source count mi index memory hmodule hindex hmemory hwf
    hpositive hcountWidth hwidth hread hwrite hc
  obtain ⟨_, hp, _⟩ := h.result
  exact Prod.ext hp.2.1 hp.2.2

/-- Actual caller opcode and the four-i32 callee activation. -/
def calledStore (s : Store NearState) (op : Nat) : Store NearState :=
  chargedStore (chargedStore s op) (10 * op)

def callAfter (s : Store NearState) (op index : Nat) (out source : UInt32) (memory : Memory) (count : Nat) : Store NearState :=
  finalStore (calledStore s op) op index out source memory count

theorem call_budget (op count rest : Nat) :
    (18 * count + 17) * op + rest = op + (10 * op + ((18 * count + 6) * op + rest)) := by
  simp only [Nat.add_mul]
  omega

theorem call_fuel (fuel count : Nat) : ((fuel + 1) + (17 * count + 10)) + 1 = fuel + (17 * count + 12) := by omega

theorem callAfter_credits (s : Store NearState) (op index : Nat) (out source : UInt32)
    (memory : Memory) (count rest : Nat) (hpositive : 0 < count)
    (hc : s.host.gas.Credits ((18 * count + 17) * op + rest)) :
    (callAfter s op index out source memory count).host.gas.Credits rest := by
  rw [call_budget] at hc
  have h1 := WNear.Proofs.StorePair.charged_credits s op _ hc
  have h2 := WNear.Proofs.StorePair.charged_credits (chargedStore s op) (10 * op) _ h1
  exact finalStore_credits (calledStore s op) op index out source memory count rest hpositive h2

/-- Actual f951 local call above any operand prefix and saved callers. The
returned destination value is retained for the real caller's following drop.
No root invocation, copy callback, or assumed execution equation is used. -/
theorem wp_call (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (out source : UInt32) (count : Nat) (address : Nat)
    (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (hmodule : s.modules[frame.inst]? = some mi) (haddress : mi.funcAddrs[951]? = some address)
    (hfunction : s.funcs[address]? = some (.wasm WNear.Binary.UnwrapState.Copy.signature frame.inst WNear.Binary.UnwrapState.Copy.function))
    (hindex : mi.memAddrs[0]? = some index) (hmemory : s.mems[index]? = some memory) (hwf : memory.wf)
    (hpositive : 0 < count) (hcountWidth : count < 2 ^ 32) (hwidth : memory.byteSize ≤ 2 ^ 32)
    (hread : source.toNat + count ≤ memory.byteSize) (hwrite : out.toNat + count ≤ memory.byteSize)
    (hdepth : callers.length + 1 < limits.maxCallDepth)
    (hc : s.host.gas.Credits ((18 * count + 17) * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (callAfter s cfg.regularOpCost index out source memory count)
      limits (base ++ [Value.i32 out]).toArray frame callers code)) rest post) :
    WP cfg (fuel + (17 * count + 12)) (.next (atCode s limits
      (base ++ [Value.i32 out, .i32 source, .i32 (UInt32.ofNat count)]).toArray frame callers (.call 951 :: code)))
      ((18 * count + 17) * cfg.regularOpCost + rest) post := by
  let active := calledStore s cfg.regularOpCost
  let leaf : CallFrame := {locals := #[Value.i32 out, .i32 source, .i32 (UInt32.ofNat count), .i32 0], inst := frame.inst, arity := 1, height := base.length, labels := [], code := []}
  let saved := {frame with code := code}
  have activation : activationGas cfg.regularOpCost (wasmLocals WNear.Binary.UnwrapState.Copy.function
      [Value.i32 out, .i32 source, .i32 (UInt32.ofNat count)]) = 10 * cfg.regularOpCost :=
    WNear.Binary.UnwrapState.Copy.activation_cost _ _ _ _
  have h0 : s.host.gas.Credits
      (cfg.regularOpCost + (10 * cfg.regularOpCost + ((18 * count + 6) * cfg.regularOpCost + rest))) := by
    rw [← call_budget]; exact hc
  have h1 := WNear.Proofs.StorePair.charged_credits s cfg.regularOpCost _ h0
  have h2 : active.host.gas.Credits ((18 * count + 6) * cfg.regularOpCost + rest) :=
    WNear.Proofs.StorePair.charged_credits (chargedStore s cfg.regularOpCost) (10 * cfg.regularOpCost) _ h1
  have finalCredit := finalStore_credits active cfg.regularOpCost index out source memory count rest hpositive h2
  have arity : [Value.i32 out].length = (afterFrame leaf out source count).arity := by
    simp [afterFrame, leaf, UnwrapStateCopyState.loopFrame_arity]
  have height : (afterFrame leaf out source count).height = base.length := by
    simp [afterFrame, leaf, UnwrapStateCopyState.loopFrame_height]
  have labels : (afterFrame leaf out source count).labels = [] := by
    simp [afterFrame, leaf, UnwrapStateCopyState.loopFrame_labels]
  have leaveRule := wp_leave_wasm cfg fuel rest (callAfter s cfg.regularOpCost index out source memory count)
    limits base [Value.i32 out] (afterFrame leaf out source count) saved callers post
  have leaveShape := leaveRule arity height labels
  have leave := leaveShape finalCredit hnext
  have stackResult : (base ++ [Value.i32 out]).toArray = base.toArray.push (.i32 out) := by
    apply Array.toList_inj.mp; simp
  have bodyNext : WP cfg (fuel + 1) (.next (atCode (finalStore active cfg.regularOpCost index out source memory count)
      limits (base.toArray.push (.i32 out)) (afterFrame leaf out source count) (saved :: callers) [])) rest post := by
    simpa only [stackResult, callAfter, active] using leave
  have hm : active.modules[leaf.inst]? = some mi := by simpa only [active, calledStore, chargedStore, leaf] using hmodule
  have hmem : active.mems[index]? = some memory := by simpa only [active, calledStore, chargedStore] using hmemory
  have bodyRule := wp_body cfg (fuel + 1) rest active limits base.toArray leaf (saved :: callers) [] out source count mi index memory post
  have bodyLocals := bodyRule rfl rfl rfl (by simp [leaf])
  have bodyEnv := bodyLocals hm hindex hmem hwf
  have bodyBounds := bodyEnv hpositive hcountWidth hwidth hread hwrite
  have hbody := bodyBounds h2 bodyNext
  have callRule := wp_call_wasm cfg ((fuel + 1) + (17 * count + 10)) ((18 * count + 6) * cfg.regularOpCost + rest)
    s limits base [Value.i32 out, .i32 source, .i32 (UInt32.ofNat count)] frame callers code 951 address mi
    WNear.Binary.UnwrapState.Copy.signature frame.inst WNear.Binary.UnwrapState.Copy.function post
  have callEnv := callRule hmodule haddress hfunction
  have callTyped := callEnv rfl hdepth
  rw [activation] at callTyped
  have callPaid := callTyped h0
  have locals_eq : #[Value.i32 out, .i32 source, .i32 (UInt32.ofNat count)] ++ #[Value.i32 0] =
      #[Value.i32 out, .i32 source, .i32 (UInt32.ofNat count), .i32 0] := rfl
  have nextBody : WP cfg ((fuel + 1) + (17 * count + 10)) (.next (wasmCallee active limits base frame callers code
      WNear.Binary.UnwrapState.Copy.signature frame.inst WNear.Binary.UnwrapState.Copy.function
      [Value.i32 out, .i32 source, .i32 (UInt32.ofNat count)])) ((18 * count + 6) * cfg.regularOpCost + rest) post := by
    simpa only [wasmCallee, wasmLocals, WNear.Binary.UnwrapState.Copy.function, WNear.Binary.UnwrapState.Copy.signature,
      atCode, leaf, saved, ValType.default, List.map_cons, List.map_nil, List.append_nil, locals_eq, List.length_cons, List.length_nil] using hbody
  have result := callPaid nextBody
  rw [← call_budget, call_fuel] at result
  exact result

end WNear.Proofs.UnwrapStateCopyEntry
