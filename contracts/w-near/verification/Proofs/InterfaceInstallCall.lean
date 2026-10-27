import Proofs.InterfaceSetLazyCall
import Proofs.TotalSupply

/-! Actual f520 installation wrapper, including the complete lazy setter path. -/
namespace WNear.Proofs.InterfaceInstallCall
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.StorePairCaller (paid paid_credits)
open InterfaceSetState (Layout)
set_option maxRecDepth 16384
set_option maxHeartbeats 300000
attribute [local irreducible] WP

theorem setup_charge (s : Store NearState) (cost : Nat) (limits : ExecLimits) (frame : CallFrame)
    (callers : List CallFrame) (p : Layout) (initializerAddress : Nat)
    (hr : InterfaceSetLazyState.Setup s limits frame callers p initializerAddress) :
    InterfaceSetLazyState.Setup (chargedStore s cost) limits frame callers p initializerAddress := by
  exact {
    code := hr.code.transport s (chargedStore s cost) p frame.inst rfl rfl rfl
    interfaceLocal := hr.interfaceLocal
    receiverLocal := hr.receiverLocal
    vtableLocal := hr.vtableLocal
    localSize := hr.localSize
    memory := hr.memory
    global := hr.global
    sp := hr.sp
    firstBound := hr.firstBound
    secondBound := hr.secondBound
    interfaceBound := hr.interfaceBound
    interfaceRead := hr.interfaceRead
    statusBound := hr.statusBound
    status := hr.status
    lazyIndex := hr.lazyIndex
    lazyFunction := hr.lazyFunction
    initializerElement := hr.initializerElement
    initializerType := hr.initializerType
    initializerFunction := hr.initializerFunction
    initializerBound := hr.initializerBound
    tail := hr.tail
    depth := hr.depth }

theorem setup_paid (s : Store NearState) (op n : Nat) (limits : ExecLimits) (frame : CallFrame)
    (callers : List CallFrame) (p : Layout) (initializerAddress : Nat)
    (hr : InterfaceSetLazyState.Setup s limits frame callers p initializerAddress) :
    InterfaceSetLazyState.Setup (paid s op n) limits frame callers p initializerAddress := by
  induction n with
  | zero => exact hr
  | succ n ih => exact setup_charge _ op limits frame callers p initializerAddress ih

/-- Saved code suffixes, stack height and labels do not change the structural
setter obligations. Only the active module, locals and caller depth matter. -/
theorem setup_reframe (s : Store NearState) (limits : ExecLimits) (frame frame' : CallFrame)
    (callers callers' : List CallFrame) (p : Layout) (initializerAddress : Nat)
    (hr : InterfaceSetLazyState.Setup s limits frame callers p initializerAddress)
    (hinst : frame'.inst = frame.inst) (hlocals : frame'.locals = frame.locals)
    (hdepth : callers'.length ≤ callers.length) :
    InterfaceSetLazyState.Setup s limits frame' callers' p initializerAddress := by
  exact {
    code := by simpa only [hinst] using hr.code
    interfaceLocal := by simpa only [hlocals] using hr.interfaceLocal
    receiverLocal := by simpa only [hlocals] using hr.receiverLocal
    vtableLocal := by simpa only [hlocals] using hr.vtableLocal
    localSize := by simpa only [hlocals] using hr.localSize
    memory := hr.memory
    global := hr.global
    sp := hr.sp
    firstBound := hr.firstBound
    secondBound := hr.secondBound
    interfaceBound := hr.interfaceBound
    interfaceRead := hr.interfaceRead
    statusBound := hr.statusBound
    status := hr.status
    lazyIndex := hr.lazyIndex
    lazyFunction := by simpa only [hinst] using hr.lazyFunction
    initializerElement := hr.initializerElement
    initializerType := hr.initializerType
    initializerFunction := by simpa only [hinst] using hr.initializerFunction
    initializerBound := hr.initializerBound
    tail := hr.tail
    depth := by have hd := hr.depth; omega }

def bodyAfter (s : Store NearState) (op : Nat) (p : Layout) (initializerAddress : Nat) :=
  InterfaceSetLazyCall.callAfter (paid s op 3) op p initializerAddress

theorem bodyAfter_credits (s : Store NearState) (op rest : Nat) (p : Layout) (initializerAddress : Nat)
    (hc : s.host.gas.Credits (318 * op + rest)) :
    (bodyAfter s op p initializerAddress).host.gas.Credits rest := by
  have prefixCredits := paid_credits s op 3 (315 * op + rest) (hc.mono (by omega))
  have call := StorePair.charged_credits (paid s op 3) op (10 * op + (304 * op + rest)) (prefixCredits.mono (by omega))
  have activation := StorePair.charged_credits (chargedStore (paid s op 3) op) (10 * op) (304 * op + rest) call
  exact InterfaceSetLazyBody.finalStore_credits (InterfaceSetCall.entered (paid s op 3) op) op rest p initializerAddress activation

/-- The deployed three scalar arguments and actual221-step lazy f463 call. -/
theorem wp_body (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (p : Layout) (initializerAddress setterAddress : Nat) (post : Post)
    (hinterface : p.interface = 1055020)
    (hreceiver : frame.locals[0]? = some (.i32 p.receiver)) (hvtable : frame.locals[1]? = some (.i32 p.vtable))
    (hr : InterfaceSetLazyState.Setup s limits (InterfaceSetCall.leaf frame.inst base.length p) (frame :: callers) p initializerAddress)
    (hb : InterfaceSetLazyState.Bounds p initializerAddress)
    (hindex : p.mi.funcAddrs[463]? = some setterAddress)
    (hfunction : s.funcs[setterAddress]? = some (.wasm WNear.Binary.InterfaceSet.signature frame.inst WNear.Binary.InterfaceSet.function))
    (hc : s.host.gas.Credits (318 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (bodyAfter s cfg.regularOpCost p initializerAddress) limits
      base.toArray frame callers code)) rest post) :
    WP cfg (fuel + 224) (.next (atCode s limits base.toArray frame callers
      (WNear.Binary.InterfaceSet.wrapperBody ++ code))) (318 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let prepared := paid s op 3
  let active := InterfaceSetCall.entered prepared op
  let leaf := InterfaceSetCall.leaf frame.inst base.length p
  have r0 := setup_paid s op 3 limits leaf (frame :: callers) p initializerAddress hr
  have r1 := setup_charge prepared op limits leaf (frame :: callers) p initializerAddress r0
  have r2 := setup_charge (chargedStore prepared op) (10 * op) limits leaf (frame :: callers) p initializerAddress r1
  have ready : InterfaceSetLazyState.Setup active limits leaf ({frame with code} :: callers) p initializerAddress :=
    setup_reframe active limits leaf leaf (frame :: callers) ({frame with code} :: callers) p initializerAddress r2 rfl rfl (by simp)
  have hm : prepared.modules[frame.inst]? = some p.mi := by simpa only [prepared, paid, chargedStore, InterfaceSetCall.leaf] using hr.code.module
  have function : prepared.funcs[setterAddress]? = some (.wasm WNear.Binary.InterfaceSet.signature frame.inst WNear.Binary.InterfaceSet.function) := by
    simpa only [prepared, paid, chargedStore] using hfunction
  have callRule := InterfaceSetLazyCall.wp_call cfg fuel rest prepared limits base frame callers code p initializerAddress setterAddress post
    hm hindex function ready hb (paid_credits s op 3 _ (hc.mono (by dsimp [op]; omega)))
  have callNext : WP cfg fuel (.next (atCode (InterfaceSetLazyCall.callAfter prepared op p initializerAddress) limits base.toArray frame callers code)) rest post := by
    simpa only [bodyAfter, prepared, op] using hnext
  have call := callRule callNext
  have callStack : WP cfg (fuel + 221) (.next (atCode prepared limits
      (((base.toArray.push (.i32 1055020)).push (.i32 p.receiver)).push (.i32 p.vtable)) frame callers (.call 463 :: code)))
      (315 * op + rest) post := by
    simpa [hinterface, op] using call
  have prefixRule := InterfaceInstall.wp_wrapper_arguments cfg (fuel + 221) (315 * op + rest) s limits base.toArray frame callers
    (.call 463 :: code) p.receiver p.vtable post hreceiver hvtable (hc.mono (by dsimp [op]; omega))
  have result := prefixRule callStack
  rw [show 3 * cfg.regularOpCost + (315 * op + rest) = 318 * cfg.regularOpCost + rest by dsimp [op]; omega] at result
  simpa only [WNear.Binary.InterfaceSet.wrapperBody, List.cons_append, List.nil_append, Nat.add_assoc, Nat.reduceAdd] using result

def entered (s : Store NearState) (op : Nat) := chargedStore (chargedStore s op) (9 * op)
def calledAfter (s : Store NearState) (op : Nat) (p : Layout) (initializerAddress : Nat) := bodyAfter (entered s op) op p initializerAddress

def leaf (inst height : Nat) (p : Layout) : CallFrame :=
  {locals := #[.i32 p.receiver, .i32 p.vtable], inst, arity := 0, height, labels := [], code := []}

/-- All facts refer to the original store. Native post-initialization words in
Bounds are computed memories; there is no future array lookup or call result. -/
structure Resources (s : Store NearState) (limits : ExecLimits) (frame : CallFrame)
    (p : Layout) (initializerAddress : Nat) : Prop where
  interface : p.interface = 1055020
  wrapper : ∃ address, p.mi.funcAddrs[520]? = some address ∧ s.funcs[address]? = some
    (.wasm WNear.Binary.InterfaceSet.wrapperSignature frame.inst WNear.Binary.InterfaceSet.wrapperFunction)
  setter : ∃ address, p.mi.funcAddrs[463]? = some address ∧ s.funcs[address]? = some
    (.wasm WNear.Binary.InterfaceSet.signature frame.inst WNear.Binary.InterfaceSet.function)
  setup : InterfaceSetLazyState.Setup s limits (InterfaceSetCall.leaf frame.inst 0 p) [frame, frame] p initializerAddress
  bounds : InterfaceSetLazyState.Bounds p initializerAddress

theorem calledAfter_credits (s : Store NearState) (op rest : Nat) (p : Layout) (initializerAddress : Nat)
    (hc : s.host.gas.Credits (328 * op + rest)) :
    (calledAfter s op p initializerAddress).host.gas.Credits rest := by
  have hop := StorePair.charged_credits s op (9 * op + (318 * op + rest)) (hc.mono (by omega))
  have activation := StorePair.charged_credits (chargedStore s op) (9 * op) (318 * op + rest) hop
  exact bodyAfter_credits (entered s op) op rest p initializerAddress activation

/-- Complete actual f520 call. Its final free leave restores the original
caller frame; lazy initialization, borrowing and installation are all executed. -/
theorem wp_call (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (frame : CallFrame) (code : List Instr) (p : Layout) (initializerAddress : Nat) (post : Post)
    (hr : Resources s limits frame p initializerAddress)
    (hc : s.host.gas.Credits (328 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (calledAfter s cfg.regularOpCost p initializerAddress) limits #[] frame [] code)) rest post) :
    WP cfg (fuel + 226) (.next (atCode s limits #[.i32 p.receiver, .i32 p.vtable] frame [] (.call 520 :: code)))
      (328 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let active := entered s op
  let callee := leaf frame.inst 0 p
  let saved := {frame with code}
  have r0 := setup_charge s op limits (InterfaceSetCall.leaf frame.inst 0 p) [frame, frame] p initializerAddress hr.setup
  have r1 := setup_charge (chargedStore s op) (9 * op) limits (InterfaceSetCall.leaf frame.inst 0 p) [frame, frame] p initializerAddress r0
  have ready : InterfaceSetLazyState.Setup active limits (InterfaceSetCall.leaf callee.inst 0 p) [callee, saved] p initializerAddress :=
    setup_reframe active limits (InterfaceSetCall.leaf frame.inst 0 p) (InterfaceSetCall.leaf callee.inst 0 p)
      [frame, frame] [callee, saved] p initializerAddress r1 rfl rfl (by simp)
  have c0 := StorePair.charged_credits s op (9 * op + (318 * op + rest)) (hc.mono (by dsimp [op]; omega))
  have ca : active.host.gas.Credits (318 * op + rest) := StorePair.charged_credits (chargedStore s op) (9 * op) (318 * op + rest) c0
  have cf := calledAfter_credits s op rest p initializerAddress hc
  have leaveRule := wp_leave_wasm cfg fuel rest (calledAfter s op p initializerAddress) limits [] [] callee saved [] post rfl rfl rfl cf
  have leaveNext : WP cfg fuel (.next (atCode (calledAfter s op p initializerAddress) limits #[] saved [] saved.code)) rest post := by
    simpa only [saved, atCode, op] using hnext
  have leaving := leaveRule leaveNext
  rcases hr.setter with ⟨setterAddress, hsi, hsf⟩
  have setter : active.funcs[setterAddress]? = some (.wasm WNear.Binary.InterfaceSet.signature callee.inst WNear.Binary.InterfaceSet.function) := by
    simpa only [active, entered, chargedStore, callee, leaf] using hsf
  have bodyRule := wp_body cfg (fuel + 1) rest active limits [] callee [saved] [] p initializerAddress setterAddress post
    hr.interface rfl rfl ready hr.bounds hsi setter ca
  have bodyNext : WP cfg (fuel + 1) (.next (atCode (bodyAfter active op p initializerAddress) limits #[] callee [saved] [])) rest post := by
    simpa only [calledAfter, active, List.append_nil] using leaving
  have body := bodyRule bodyNext
  rcases hr.wrapper with ⟨wrapperAddress, hwi, hwf⟩
  have hm : s.modules[frame.inst]? = some p.mi := by simpa only [InterfaceSetCall.leaf] using hr.setup.code.module
  have depth : 1 < limits.maxCallDepth := by have hd := hr.setup.depth; simp only [List.length_cons, List.length_nil] at hd; omega
  have callRule := wp_call_wasm cfg ((fuel + 1) + 224) (318 * op + rest) s limits [] [.i32 p.receiver, .i32 p.vtable] frame [] code
    520 wrapperAddress p.mi WNear.Binary.InterfaceSet.wrapperSignature frame.inst WNear.Binary.InterfaceSet.wrapperFunction post hm hwi hwf rfl depth
  have activation : activationGas op (wasmLocals WNear.Binary.InterfaceSet.wrapperFunction [.i32 p.receiver, .i32 p.vtable]) = 9 * op := by
    simp [activationGas, wasmLocals, WNear.Binary.InterfaceSet.wrapperFunction]
  rw [activation] at callRule
  have next : WP cfg ((fuel + 1) + 224) (.next (wasmCallee active limits [] frame [] code WNear.Binary.InterfaceSet.wrapperSignature frame.inst
      WNear.Binary.InterfaceSet.wrapperFunction [.i32 p.receiver, .i32 p.vtable])) (318 * op + rest) post := by
    simpa only [wasmCallee, wasmLocals, WNear.Binary.InterfaceSet.wrapperFunction, WNear.Binary.InterfaceSet.wrapperSignature,
      atCode, callee, leaf, saved, List.map_nil, List.append_nil, Array.append_empty, List.length_cons, List.length_nil, Nat.reduceAdd, op] using body
  have result := callRule (hc.mono (by dsimp [op]; omega)) next
  rw [show cfg.regularOpCost + (9 * op + (318 * op + rest)) = 328 * cfg.regularOpCost + rest by dsimp [op]; omega] at result
  simpa only [List.nil_append, Nat.add_assoc, Nat.reduceAdd] using result

/-- The independent total-supply frontier can use the actual installed f520
contract instead of assuming its successful execution. -/
theorem calleeContract (cfg : WasmConfig) (s : Store NearState) (limits : ExecLimits) (frame : CallFrame)
    (p : Layout) (initializerAddress : Nat) (hr : Resources s limits frame p initializerAddress) :
    TotalSupply.CalleeContract cfg limits frame 520 [.i32 p.receiver, .i32 p.vtable] s
      (calledAfter s cfg.regularOpCost p initializerAddress) (328 * cfg.regularOpCost) 226 := by
  constructor
  · intro rest hc
    exact calledAfter_credits s cfg.regularOpCost rest p initializerAddress hc
  · intro fuel rest code post hc hnext
    exact wp_call cfg fuel rest s limits frame code p initializerAddress post hr hc hnext

end WNear.Proofs.InterfaceInstallCall
