import Proofs.ValueReturnOuterState

namespace WNear.Proofs.ValueReturnOuterBody
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.StorePairCaller (paid paid_credits)
open WNear.Proofs.ValueReturnOuter
set_option maxHeartbeats 1000000
set_option maxRecDepth 16384

def fee (cfg : WasmConfig) (s : Store NearState) (p : Layout) :=
  ValueReturnHost.cost (dispatchBefore s cfg.regularOpCost p).host p.len.toNat

def budget (cfg : WasmConfig) (s : Store NearState) (p : Layout) := 237 * cfg.regularOpCost + fee cfg s p

structure PhaseCredits (cfg : WasmConfig) (s : Store NearState) (p : Layout) (rest : Nat) : Prop where
  c_reserved : (reserved s cfg.regularOpCost p).host.gas.Credits (232 * cfg.regularOpCost + fee cfg s p + rest)
  c_lookup : (lookupBefore s cfg.regularOpCost p).host.gas.Credits (230 * cfg.regularOpCost + fee cfg s p + rest)
  c_looked : (looked s cfg.regularOpCost p).host.gas.Credits (201 * cfg.regularOpCost + fee cfg s p + rest)
  c_guarded : (paid (looked s cfg.regularOpCost p) cfg.regularOpCost 3).host.gas.Credits (198 * cfg.regularOpCost + fee cfg s p + rest)
  c_arguments : (arguments s cfg.regularOpCost p).host.gas.Credits (195 * cfg.regularOpCost + fee cfg s p + rest)
  c_acquired : (acquired s cfg.regularOpCost p).host.gas.Credits (123 * cfg.regularOpCost + fee cfg s p + rest)
  c_high : (high s cfg.regularOpCost p).host.gas.Credits (119 * cfg.regularOpCost + fee cfg s p + rest)
  c_low : (low s cfg.regularOpCost p).host.gas.Credits (114 * cfg.regularOpCost + fee cfg s p + rest)
  c_status : (status s cfg.regularOpCost p).host.gas.Credits (112 * cfg.regularOpCost + fee cfg s p + rest)
  c_select : (paid (status s cfg.regularOpCost p) cfg.regularOpCost 6).host.gas.Credits (106 * cfg.regularOpCost + fee cfg s p + rest)
  c_dispatch : (dispatchBefore s cfg.regularOpCost p).host.gas.Credits (93 * cfg.regularOpCost + fee cfg s p + rest)
  c_returned : (returned cfg s p).host.gas.Credits (69 * cfg.regularOpCost + rest)

theorem phase_credits (cfg : WasmConfig) (extra rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (frame : CallFrame) (callers : List CallFrame) (p : Layout)
    (hr : Ready cfg extra s limits frame callers p)
    (hc : s.host.gas.Credits (budget cfg s p + rest)) : PhaseCredits cfg s p rest := by
  let op := cfg.regularOpCost
  let f := fee cfg s p
  have cr : (reserved s op p).host.gas.Credits (232 * op + f + rest) :=
by
      unfold reserved
      change (paid s op 5).host.gas.Credits _
      exact paid_credits s op 5 _ (hc.mono (by dsimp [budget, op, f]; omega))
  have cl : (lookupBefore s op p).host.gas.Credits (230 * op + f + rest) :=
    paid_credits (reserved s op p) op 2 _ (cr.mono (by omega))
  have ck : (looked s op p).host.gas.Credits (201 * op + f + rest) :=
    ValueReturnThreadLocal.indirectAfter_credits (lookupBefore s op p) op _ (cl.mono (by omega))
  have cg : (paid (looked s op p) op 3).host.gas.Credits (198 * op + f + rest) :=
    paid_credits (looked s op p) op 3 _ (ck.mono (by omega))
  have ca : (arguments s op p).host.gas.Credits (195 * op + f + rest) :=
    paid_credits (paid (looked s op p) op 3) op 3 _ (cg.mono (by omega))
  have cw : (acquired s op p).host.gas.Credits (123 * op + f + rest) :=
    (ValueReturnAcquire.calledAcquireStore_gas (arguments s op p) op p.globalIndex p.memoryIndex _
      (scratch p) (scratch p) 1074904 p.memory (ca.mono (by omega))).2.2
  have ch : (high s op p).host.gas.Credits (119 * op + f + rest) :=
by
      unfold high
      rw [storeI32_host]
      exact paid_credits (acquired s op p) op 4 _ (cw.mono (by omega))
  have co : (low s op p).host.gas.Credits (114 * op + f + rest) :=
by
      unfold low
      rw [storeI32_host]
      exact paid_credits (high s op p) op 5 _ (ch.mono (by omega))
  have cs : (status s op p).host.gas.Credits (112 * op + f + rest) :=
    paid_credits (low s op p) op 2 _ (co.mono (by omega))
  have csel : (paid (status s op p) op 6).host.gas.Credits (106 * op + f + rest) :=
    paid_credits (status s op p) op 6 _ (cs.mono (by omega))
  have cd : (dispatchBefore s op p).host.gas.Credits (93 * op + f + rest) :=
    nonnullAfter_credits (paid (status s op p) op 6) op _ (csel.mono (by omega))
  have cout : (returned cfg s p).host.gas.Credits (69 * op + rest) := by
    apply ValueReturnDispatchGas.fragmentAfter_credits cfg extra (69 * op + rest)
      (dispatchBefore s op p) p.mi p.memoryIndex (lowMemory p) p.len p.ptr
      hr.code.memoryIndex hr.dispatchMemoryLookup hr.fixedLength hr.returnBound hr.returnLimit
    exact cd.mono (by dsimp [f, fee, op]; omega)
  exact ⟨cr, cl, ck, cg, ca, cw, ch, co, cs, csel, cd, cout⟩

theorem frames (frame : CallFrame) (p : Layout)
    (hi : frame.locals[0]? = some (.i32 p.interface))
    (hs : frame.locals[1]? = some (.i32 p.slice)) (hn : 4 ≤ frame.locals.size) :
    (reservedFrame frame p).locals[0]? = some (.i32 p.interface) ∧
    (guardedFrame frame p).locals[0]? = some (.i32 1074904) ∧
    (guardedFrame frame p).locals[2]? = some (.i32 (scratch p)) ∧
    (statusFrame frame p).locals[3]? = some (.i32 (borrowed p)) ∧
    (statusFrame frame p).locals[1]? = some (.i32 p.slice) ∧
    4 ≤ (statusFrame frame p).locals.size ∧
    (finalFrame frame p).locals[0]? = some (.i32 0) ∧
    (finalFrame frame p).locals[2]? = some (.i32 (scratch p)) := by
  have h0 : 0 < frame.locals.size := by omega
  have h1 : 1 < frame.locals.size := by omega
  have h2 : 2 < frame.locals.size := by omega
  have h3 : 3 < frame.locals.size := by omega
  simp only [Array.getElem?_eq_getElem h0, Option.some.injEq] at hi
  simp only [Array.getElem?_eq_getElem h1, Option.some.injEq] at hs
  simp [reservedFrame, guardedFrame, pointerFrame, statusFrame, finalFrame,
    ValueReturnDispatch.dispatchFrame, h0, h1, h2, h3, hi, hs, hn]

/-- Enclosing labels are fixed by the actual nested block instructions. -/
def nested (frame : CallFrame) (height : Nat) (code : List Instr) :=
  emptyBlockFrame (emptyBlockFrame frame height (WNear.Binary.ValueReturnOuter.epilogue ++ code))
    height WNear.Binary.ValueReturnOuter.fallback

theorem cast_phase (cfg : WasmConfig) (fuel fuel' gas gas' : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code code' : List Instr) (post : Post)
    (hf : fuel = fuel') (hg : gas = gas') (hc : code = code')
    (h : WP cfg fuel (.next (atCode s limits stack frame callers code)) gas post) :
    WP cfg fuel' (.next (atCode s limits stack frame callers code')) gas' post := by
  subst fuel' gas' code'
  exact h

theorem dispatch_nested (frame : CallFrame) (height : Nat) (code : List Instr) (cell : UInt32) :
    ValueReturnDispatch.dispatchFrame (nested frame height code) cell =
      nested (ValueReturnDispatch.dispatchFrame frame cell) height code := rfl

/-- Abstracting the acquired store keeps this twenty-three-step kernel proof
independent of the preceding acquisition's implementation term. -/
def borrowHigh (s : Store NearState) (op index : Nat) (scratch : UInt32) (memory : Memory) :=
  storeI32 (paid s op 4) index (scratch.toNat + 12) memory (readI32 memory (scratch.toNat + 4))
def borrowLow (s : Store NearState) (op index : Nat) (scratch : UInt32) (m0 m1 : Memory) :=
  storeI32 (paid (borrowHigh s op index scratch m0) op 5) index (scratch.toNat + 8) m1 (readI32 m1 scratch.toNat)
def borrowStatus (s : Store NearState) (op index : Nat) (scratch : UInt32) (m0 m1 : Memory) :=
  paid (borrowLow s op index scratch m0 m1) op 2

def borrowSelected (s : Store NearState) (op index : Nat) (scratch : UInt32) (m0 m1 : Memory) :=
  paid (borrowStatus s op index scratch m0 m1) op 6

def borrowAfter (s : Store NearState) (op index : Nat) (scratch : UInt32) (m0 m1 : Memory) :=
  nonnullAfter (borrowSelected s op index scratch m0 m1) op

def borrowFrame (frame : CallFrame) (memory : Memory) (scratch : UInt32) :=
  {frame with locals := (frame.locals.set! 3 (.i32 (readI32 memory scratch.toNat))).set! 0 (.i32 0)}

theorem wp_borrow_tail (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (scratch : UInt32) (mi : ModuleInst) (index address inst : Nat)
    (m0 m1 m2 : Memory) (post : Post)
    (hlocal : frame.locals[2]? = some (.i32 scratch)) (hsize : 4 ≤ frame.locals.size)
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.memAddrs[0]? = some index)
    (hmem : s.mems[index]? = some m0)
    (hmem1 : (borrowHigh s cfg.regularOpCost index scratch m0).mems[index]? = some m1)
    (hmem2 : (borrowStatus s cfg.regularOpCost index scratch m0 m1).mems[index]? = some m2)
    (hhigh : scratch.toNat + 16 ≤ m0.byteSize) (hlow : scratch.toNat + 12 ≤ m1.byteSize)
    (hselect : (readI32 m1 scratch.toNat).toNat + 4 ≤ m2.byteSize)
    (hnonzero : (if readI32 m2 (readI32 m1 scratch.toNat).toNat ≠ 0 then readI32 m1 scratch.toNat else 0) ≠ 0)
    (ha : mi.funcAddrs[430]? = some address)
    (hf : s.funcs[address]? = some (.wasm WNear.Binary.ValueReturnBorrow.nonnullSignature inst WNear.Binary.ValueReturnBorrow.nonnullFunction))
    (hd : callers.length + 1 < limits.maxCallDepth)
    (hc : s.host.gas.Credits (30 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (borrowAfter s cfg.regularOpCost index scratch m0 m1) limits
      (base ++ [Value.i32 (if readI32 m2 (readI32 m1 scratch.toNat).toNat ≠ 0 then readI32 m1 scratch.toNat else 0)]).toArray
      (borrowFrame frame m1 scratch) callers code)) rest post) :
    WP cfg (fuel + 23) (.next (atCode s limits base.toArray frame callers
      (WNear.Binary.ValueReturnOuter.saveBorrow ++ WNear.Binary.ValueReturnOuter.nonnull ++ code))) (30 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let pointer := readI32 m1 scratch.toNat
  let cell := if readI32 m2 pointer.toNat ≠ 0 then pointer else 0
  let fPointer := {frame with locals := frame.locals.set! 3 (.i32 pointer)}
  let fStatus := borrowFrame frame m1 scratch
  let callCode := .call 430 :: code
  let selectCode := [.local_get 3, .i32_const 0, .local_get 3, .load .i32 none {align := 2, offset := 0}, .select none, .i32_const 1056164] ++ callCode
  let statusCode := [.i32_const 0, .local_set 0] ++ selectCode
  let lowCode := [.local_get 2, .local_get 2, .load .i32 none {align := 2, offset := 0}, .local_tee 3,
    .store .i32 none {align := 2, offset := 8}] ++ statusCode
  have c4 : (borrowHigh s op index scratch m0).host.gas.Credits (26 * op + rest) := by
    unfold borrowHigh; rw [storeI32_host]
    exact paid_credits s op 4 _ (hc.mono (by dsimp [op]; omega))
  have c9 : (borrowLow s op index scratch m0 m1).host.gas.Credits (21 * op + rest) := by
    unfold borrowLow; rw [storeI32_host]
    exact paid_credits (borrowHigh s op index scratch m0) op 5 _ (c4.mono (by omega))
  have c11 : (borrowStatus s op index scratch m0 m1).host.gas.Credits (19 * op + rest) :=
    paid_credits (borrowLow s op index scratch m0 m1) op 2 _ (c9.mono (by omega))
  have c17 : (borrowSelected s op index scratch m0 m1).host.gas.Credits (13 * op + rest) :=
    paid_credits (borrowStatus s op index scratch m0 m1) op 6 _ (c11.mono (by omega))
  have hs3 : 3 < frame.locals.size := by omega
  have hpointer : fStatus.locals[3]? = some (.i32 pointer) := by simp [fStatus, borrowFrame, pointer, hs3]
  have hmSel : (borrowSelected s op index scratch m0 m1).modules[fStatus.inst]? = some mi := by
    simpa only [borrowSelected, borrowStatus, borrowLow, borrowHigh, fStatus, borrowFrame, paid, chargedStore, storeI32_modules] using hm
  have hfSel : (borrowSelected s op index scratch m0 m1).funcs[address]? = some (.wasm WNear.Binary.ValueReturnBorrow.nonnullSignature inst WNear.Binary.ValueReturnBorrow.nonnullFunction) := by
    simpa only [borrowSelected, borrowStatus, borrowLow, borrowHigh, paid, chargedStore, storeI32_funcs] using hf
  have callRule := wp_call_nonnull cfg fuel rest (borrowSelected s op index scratch m0 m1) limits base fStatus callers code cell 1056164 address inst mi post
    hmSel ha hfSel hnonzero hd c17 hnext
  have pairStack : (base ++ [Value.i32 cell, .i32 1056164]).toArray = (base.toArray.push (.i32 cell)).push (.i32 1056164) := by
    apply Array.toList_inj.mp; simp
  have callNext : WP cfg (fuel + 6) (.next (atCode (borrowSelected s op index scratch m0 m1) limits
      ((base.toArray.push (.i32 cell)).push (.i32 1056164)) fStatus callers callCode)) (13 * op + rest) post := by
    simpa only [pairStack] using callRule
  have hmStatus : (borrowStatus s op index scratch m0 m1).modules[fStatus.inst]? = some mi := by
    simpa only [borrowStatus, borrowLow, borrowHigh, fStatus, borrowFrame, paid, chargedStore, storeI32_modules] using hm
  have selectedProof := wp_select_record cfg (fuel + 6) (13 * op + rest) (borrowStatus s op index scratch m0 m1) limits base.toArray fStatus callers callCode pointer mi index m2 post
    hpointer hmStatus hi hmem2 hselect (c11.mono (by omega)) callNext
  have statusNext : WP cfg ((fuel + 6) + 6) (.next (atCode (borrowStatus s op index scratch m0 m1) limits base.toArray
      {fPointer with locals := fPointer.locals.set! 0 (.i32 0)} callers selectCode)) (6 * op + (13 * op + rest)) post := by
    simpa only [fPointer, fStatus, borrowFrame, pointer, selectCode] using selectedProof
  have statusProof := wp_success_status cfg ((fuel + 6) + 6) (6 * op + (13 * op + rest)) (borrowLow s op index scratch m0 m1)
    limits base.toArray fPointer callers selectCode post (c9.mono (by omega)) statusNext
  have hmHigh : (borrowHigh s op index scratch m0).modules[frame.inst]? = some mi := by
    simpa only [borrowHigh, paid, chargedStore, storeI32_modules] using hm
  have lowNext : WP cfg (((fuel + 6) + 6) + 2) (.next (atCode (borrowLow s op index scratch m0 m1) limits base.toArray
      {frame with locals := frame.locals.set! 3 (.i32 (readI32 m1 scratch.toNat))} callers statusCode))
      (2 * op + (6 * op + (13 * op + rest))) post := by simpa only [statusCode, fPointer, pointer] using statusProof
  have lowProof := wp_copy_record_low cfg (((fuel + 6) + 6) + 2) (2 * op + (6 * op + (13 * op + rest)))
    (borrowHigh s op index scratch m0) limits base.toArray frame callers statusCode scratch mi index m1 post hlocal hmHigh hi hmem1 hlow (c4.mono (by omega)) lowNext
  have highNext : WP cfg ((((fuel + 6) + 6) + 2) + 5) (.next (atCode (borrowHigh s op index scratch m0) limits base.toArray frame callers lowCode))
      (5 * op + (2 * op + (6 * op + (13 * op + rest)))) post := by simpa only [lowCode] using lowProof
  have result := wp_copy_record_high cfg ((((fuel + 6) + 6) + 2) + 5) (5 * op + (2 * op + (6 * op + (13 * op + rest))))
    s limits base.toArray frame callers lowCode scratch mi index m0 post hlocal hm hi hmem hhigh (hc.mono (by dsimp [op]; omega)) highNext
  have fuelEq : fuel + 6 + 6 + 2 + 5 + 4 = fuel + 23 := by omega
  have gasEq : 4 * cfg.regularOpCost + (5 * op + (2 * op + (6 * op + (13 * op + rest)))) = 30 * cfg.regularOpCost + rest := by dsimp [op]; omega
  have codeEq : ([.local_get 2, .local_get 2, .load .i32 none {align := 2, offset := 4}, .store .i32 none {align := 2, offset := 12}] ++ lowCode) =
      (WNear.Binary.ValueReturnOuter.saveBorrow ++ WNear.Binary.ValueReturnOuter.nonnull ++ code) := by
    simp only [lowCode, statusCode, selectCode, callCode, WNear.Binary.ValueReturnOuter.saveBorrow, WNear.Binary.ValueReturnOuter.nonnull,
      List.cons_append, List.nil_append]
  exact cast_phase cfg _ _ _ _ s limits base.toArray frame callers _ _ post fuelEq gasEq codeEq result

end WNear.Proofs.ValueReturnOuterBody
