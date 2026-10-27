import Proofs.InterfaceSetLazyReady

/-! Complete actual f463 body on the lazy first-installation path. -/
namespace WNear.Proofs.InterfaceSetLazyBody
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.StorePairCaller (paid paid_credits)
open WNear.Proofs.InterfaceSetState WNear.Proofs.InterfaceSetLazyState
set_option maxRecDepth 16384
set_option maxHeartbeats 300000
attribute [local irreducible] WP

def continuation : List Instr := WNear.Binary.InterfaceSet.acquire ++ WNear.Binary.InterfaceSet.copyBorrow ++
  WNear.Binary.InterfaceSet.guard ++ WNear.Binary.InterfaceSet.install ++ WNear.Binary.InterfaceSet.release

theorem finalStore_credits (s : Store NearState) (op rest : Nat) (p : Layout) (initializerAddress : Nat)
    (hc : s.host.gas.Credits (304 * op + rest)) :
    (finalStore s op p initializerAddress).host.gas.Credits rest := by
  have cs := InterfaceSetPhases.savedArguments_credits s op (293 * op + rest) p (hc.mono (by omega))
  have cl := paid_credits (savedArguments s op p) op 2 (111 * op + (180 * op + rest)) (cs.mono (by omega))
  have ck := ValueReturnLazyLookup.indirectAfter_credits (lookupBefore s op p) op (180 * op + rest)
    (lookupLayout p initializerAddress) cl
  exact InterfaceSetCore.after_credits (looked s op p initializerAddress) op rest p (memory p initializerAddress) ck

/-- Full real lazy565/468/467/564 lookup, exclusive borrow, installation,
release and shadow-stack restoration. There is no whole-callee WP premise. -/
theorem wp_body (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (p : Layout) (initializerAddress : Nat) (post : Post)
    (hr : Setup s limits frame callers p initializerAddress) (hb : Bounds p initializerAddress)
    (hc : s.host.gas.Credits (304 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (finalStore s cfg.regularOpCost p initializerAddress) limits base.toArray
      (finalFrame frame p initializerAddress) callers code)) rest post) :
    WP cfg (fuel + 219) (.next (atCode s limits base.toArray frame callers
      (WNear.Binary.InterfaceSet.body ++ code))) (304 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let nf := nested (reservedFrame frame p) base.toArray.size code
  let q := lookupLayout p initializerAddress
  have cs : (savedArguments s op p).host.gas.Credits (293 * op + rest) :=
    InterfaceSetPhases.savedArguments_credits s op _ p (hc.mono (by dsimp [op]; omega))
  have cl : (lookupBefore s op p).host.gas.Credits (111 * op + (180 * op + rest)) :=
    paid_credits (savedArguments s op p) op 2 _ (cs.mono (by omega))
  have ck : (looked s op p initializerAddress).host.gas.Credits (180 * op + rest) :=
    ValueReturnLazyLookup.indirectAfter_credits (lookupBefore s op p) op _ q cl
  have core := InterfaceSetCore.wp_core cfg fuel rest (looked s op p initializerAddress) limits base
    (reservedFrame frame p) callers code p (memory p initializerAddress) post
    (coreReady s op limits frame callers p initializerAddress hr hb) ck hnext
  have oneStack : (base ++ [Value.i32 1074904]).toArray = base.toArray.push (.i32 1074904) := by
    apply Array.toList_inj.mp; simp
  have coreNext : WP cfg (fuel + 125) (.next (atCode
      (ValueReturnLazyLookup.indirectAfter (lookupBefore s op p) op q) limits
      (base ++ [Value.i32 1074904]).toArray nf callers continuation)) (180 * op + rest) post := by
    simpa only [oneStack, nf, continuation, looked, q, op] using core
  have cL : Code (lookupBefore s op p) p nf.inst := by
    simpa only [nf, nested, emptyBlockFrame, reservedFrame] using InterfaceSetPhases.lookupBefore_code s op p frame.inst hr.code
  have lazyFunction : (lookupBefore s op p).funcs[467]? = some
      (.wasm WNear.Binary.InterfaceLazy.signature nf.inst WNear.Binary.InterfaceLazy.function) := by
    rw [lookupBefore_funcs]
    simpa only [nf, nested, emptyBlockFrame, reservedFrame] using hr.lazyFunction
  have res : ValueReturnLazyLookup.Resources (lookupBefore s op p) limits nf.inst (callers.length + 3) q := by
    simpa only [nf, nested, emptyBlockFrame, reservedFrame, q] using resources s op limits frame callers p initializerAddress hr
  have indirect := ValueReturnLazyLookup.wp_indirect_lookup cfg (fuel + 125) (180 * op + rest) (lookupBefore s op p)
    limits base nf callers continuation q 565 468 467 p.lookupElement post res rfl rfl cL.lookupElement cL.lookupType
    cL.lookupFunction cL.helperIndex cL.helperFunction hr.lazyIndex lazyFunction hr.statusBound hr.status cl coreNext
  have cS : Code (savedArguments s op p) p nf.inst := by
    simpa only [nf, nested, emptyBlockFrame, reservedFrame] using InterfaceSetPhases.savedArguments_code s op p frame.inst hr.code
  have hinterface : nf.locals[0]? = some (.i32 p.interface) := by
    simpa [nf, nested, emptyBlockFrame, reservedFrame] using hr.interfaceLocal
  have lookupNext : WP cfg ((fuel + 125) + 79) (.next (atCode (lookupBefore s op p) limits
      (base.toArray.push (.i32 (readI32 (savedMemory p) p.interface.toNat))) nf callers
      (.call_indirect 1 0 :: continuation))) (111 * op + (180 * op + rest)) post := by
    simpa only [hr.interfaceRead, op] using indirect
  have lookup := ValueReturnOuter.wp_lookup_argument cfg ((fuel + 125) + 79) (111 * op + (180 * op + rest))
    (savedArguments s op p) limits base.toArray nf callers (.call_indirect 1 0 :: continuation) p.interface p.mi p.memoryIndex
    (savedMemory p) post hinterface cS.module cS.memoryIndex (InterfaceSetPhases.savedArguments_memory s op p hr.memory)
    hr.interfaceBound (cs.mono (by omega)) lookupNext
  have inner : WP cfg (fuel + 206) (.next (atCode (savedArguments s op p) limits base.toArray nf callers
      WNear.Binary.InterfaceSet.inner)) (293 * op + rest) post := by
    have fe : fuel + 125 + 79 + 2 = fuel + 206 := by omega
    have ge : 2 * cfg.regularOpCost + (111 * op + (180 * op + rest)) = 293 * op + rest := by dsimp [op]; omega
    have ce : [.local_get 0, .load .i32 none {align := 2, offset := 0}] ++ (.call_indirect 1 0 :: continuation) =
        WNear.Binary.InterfaceSet.inner := by
      simp only [WNear.Binary.InterfaceSet.inner, WNear.Binary.InterfaceSet.lookup, continuation,
        List.append_assoc, List.cons_append, List.nil_append]
    exact ValueReturnOuterBody.cast_phase cfg _ _ _ _ (savedArguments s op p) limits base.toArray nf callers _ _ post fe ge ce lookup
  have setup := InterfaceSetSetup.wp_setup_blocks cfg (fuel + 206) (293 * op + rest) s limits base frame callers code p post
    hr.receiverLocal hr.vtableLocal hr.localSize hr.code hr.global hr.sp hr.memory hr.firstBound hr.secondBound
    (hc.mono (by dsimp [op]; omega)) inner
  have fe : fuel + 206 + 13 = fuel + 219 := by omega
  have ge : 11 * cfg.regularOpCost + (293 * op + rest) = 304 * cfg.regularOpCost + rest := by dsimp [op]; omega
  exact ValueReturnOuterBody.cast_phase cfg _ _ _ _ s limits base.toArray frame callers _ _ post fe ge rfl setup

end WNear.Proofs.InterfaceSetLazyBody
