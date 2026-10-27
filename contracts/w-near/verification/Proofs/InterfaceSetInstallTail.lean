import Proofs.InterfaceSetBody
import Proofs.InterfaceInstall
import Proofs.ValueReturnOuterBody

/-! Actual borrow-record copies, empty-interface guard and installation stores. -/
namespace WNear.Proofs.InterfaceSetInstallTail
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.StorePairCaller (paid paid_credits)
open WNear.Proofs.InterfaceSetBody
set_option maxRecDepth 16384
set_option maxHeartbeats 600000

def highStore (s : Store NearState) (op index : Nat) (scratch : UInt32) (memory : Memory) :=
  copiedWord s op index 12 28 scratch memory

def lowStore (s : Store NearState) (op index : Nat) (scratch : UInt32) (m0 m1 : Memory) :=
  copiedTeeWord (highStore s op index scratch m0) op index 8 24 scratch m1

def guardedStore (s : Store NearState) (op index : Nat) (scratch : UInt32) (m0 m1 : Memory) :=
  InterfaceInstall.guardAfter (paid (lowStore s op index scratch m0 m1) op 1) op

def after (s : Store NearState) (op index : Nat) (scratch receiver vtable : UInt32) (m0 m1 m2 : Memory) :=
  twoWordsStore (guardedStore s op index scratch m0 m1) op index 4 0 (readI32 m1 (scratch.toNat + 8)) vtable receiver m2

def afterFrame (frame : CallFrame) (scratch : UInt32) (memory : Memory) :=
  {frame with locals := frame.locals.set! 0 (.i32 (readI32 memory (scratch.toNat + 8)))}

/-- All23actual instructions following accepted acquisition through installation.
The old memory words are read sequentially; no disjointness premise is imposed. -/
theorem wp_tail (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (scratch receiver vtable : UInt32) (mi : ModuleInst) (index address : Nat)
    (m0 m1 m2 : Memory) (post : Post)
    (hs : frame.locals[3]? = some (.i32 scratch)) (hr : frame.locals[1]? = some (.i32 receiver))
    (hv : frame.locals[2]? = some (.i32 vtable)) (hsize : 4 ≤ frame.locals.size)
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.memAddrs[0]? = some index)
    (hmem : s.mems[index]? = some m0)
    (hmem1 : (highStore s cfg.regularOpCost index scratch m0).mems[index]? = some m1)
    (hmem2 : (lowStore s cfg.regularOpCost index scratch m0 m1).mems[index]? = some m2)
    (hhighRead : scratch.toNat + 12 + 4 ≤ m0.byteSize) (hhighWrite : scratch.toNat + 28 + 4 ≤ m0.byteSize)
    (hlowRead : scratch.toNat + 8 + 4 ≤ m1.byteSize) (hlowWrite : scratch.toNat + 24 + 4 ≤ m1.byteSize)
    (hwf : m2.wf) (hpointer : (readI32 m1 (scratch.toNat + 8)).toNat + 8 ≤ m2.byteSize)
    (hempty : readI32 m2 (readI32 m1 (scratch.toNat + 8)).toNat = 0)
    (ha : mi.funcAddrs[464]? = some address)
    (hf : s.funcs[address]? = some (.wasm WNear.Binary.InterfaceInstall.guardSignature frame.inst WNear.Binary.InterfaceInstall.guardFunction))
    (hd : callers.length + 1 < limits.maxCallDepth)
    (hc : s.host.gas.Credits (30 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (after s cfg.regularOpCost index scratch receiver vtable m0 m1 m2) limits base.toArray
      (afterFrame frame scratch m1) callers code)) rest post) :
    WP cfg (fuel + 23) (.next (atCode s limits base.toArray frame callers
      (WNear.Binary.InterfaceSet.copyBorrow ++ WNear.Binary.InterfaceSet.guard ++ WNear.Binary.InterfaceSet.install ++ code)))
      (30 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let pointer := readI32 m1 (scratch.toNat + 8)
  let f := afterFrame frame scratch m1
  let installCode := WNear.Binary.InterfaceSet.install ++ code
  let guardCode := WNear.Binary.InterfaceSet.guard ++ installCode
  let lowCode := [.local_get 3, .local_get 3, .load .i32 none {align := 2, offset := 8}, .local_tee 0,
    .store .i32 none {align := 2, offset := 24}] ++ guardCode
  have c4 : (highStore s op index scratch m0).host.gas.Credits (26 * op + rest) :=
    copiedWord_credits s op index 12 28 (26 * op + rest) scratch m0 (hc.mono (by dsimp [op]; omega))
  have c9 : (lowStore s op index scratch m0 m1).host.gas.Credits (21 * op + rest) :=
    copiedTeeWord_credits (highStore s op index scratch m0) op index 8 24 (21 * op + rest) scratch m1 (c4.mono (by omega))
  have c10 : (paid (lowStore s op index scratch m0 m1) op 1).host.gas.Credits (14 * op + (6 * op + rest)) :=
    paid_credits (lowStore s op index scratch m0 m1) op 1 _ (c9.mono (by omega))
  have cguard : (guardedStore s op index scratch m0 m1).host.gas.Credits (6 * op + rest) :=
    InterfaceInstall.guardAfter_credits _ op _ c10
  have h0 : 0 < frame.locals.size := by omega
  have hpLocal : f.locals[0]? = some (.i32 pointer) := by simp [f, afterFrame, pointer, h0]
  have hrLocal : f.locals[1]? = some (.i32 receiver) := by simpa [f, afterFrame] using hr
  have hvLocal : f.locals[2]? = some (.i32 vtable) := by simpa [f, afterFrame] using hv
  have hmGuarded : (guardedStore s op index scratch m0 m1).modules[f.inst]? = some mi := by
    simpa only [guardedStore, InterfaceInstall.guardAfter, InterfaceInstall.guardEntry, paid, chargedStore,
      lowStore, highStore, copiedWord, copiedTeeWord, storeI32_modules, f, afterFrame] using hm
  have hmemGuarded : (guardedStore s op index scratch m0 m1).mems[index]? = some m2 := by
    simpa only [guardedStore, InterfaceInstall.guardAfter, InterfaceInstall.guardEntry, paid, chargedStore] using hmem2
  have hw : pointer.toNat + 4 + 4 ≤ m2.byteSize := by dsimp [pointer]; omega
  have spec := writeI32_spec m2 (pointer.toNat + 4) vtable hwf hw
  have hsecond : pointer.toNat + 0 + 4 ≤ (writeI32 m2 (pointer.toNat + 4) vtable).byteSize := by rw [spec.2.1]; omega
  have installRule := wp_two_words cfg fuel rest (guardedStore s op index scratch m0 m1) limits base.toArray f callers code
    0 2 1 4 0 pointer vtable receiver mi index m2 post hpLocal hvLocal hrLocal hmGuarded hi hmemGuarded hw hsecond cguard hnext
  have hmLow : (paid (lowStore s op index scratch m0 m1) op 1).modules[f.inst]? = some mi := by
    simpa only [paid, chargedStore, lowStore, highStore, copiedWord, copiedTeeWord, storeI32_modules, f, afterFrame] using hm
  have hfLow : (paid (lowStore s op index scratch m0 m1) op 1).funcs[address]? = some (.wasm WNear.Binary.InterfaceInstall.guardSignature f.inst WNear.Binary.InterfaceInstall.guardFunction) := by
    simpa only [paid, chargedStore, lowStore, highStore, copiedWord, copiedTeeWord, storeI32_funcs, f, afterFrame] using hf
  have hmemLow : (paid (lowStore s op index scratch m0 m1) op 1).mems[index]? = some m2 := by simpa only [paid, chargedStore] using hmem2
  have guardRule := InterfaceInstall.wp_call_guard cfg (fuel + 6) (6 * op + rest) (paid (lowStore s op index scratch m0 m1) op 1)
    limits base f callers installCode pointer address mi index m2 post hmLow ha hfLow hi hmemLow (by dsimp [pointer]; omega) hempty hd c10 installRule
  have oneStack : (base ++ [Value.i32 pointer]).toArray = base.toArray.push (.i32 pointer) := by apply Array.toList_inj.mp; simp
  have guardNext : WP cfg ((fuel + 6) + 7) (.next (atCode (paid (lowStore s op index scratch m0 m1) op 1) limits
      (base.toArray.push (.i32 pointer)) f callers (.call 464 :: installCode))) (14 * op + (6 * op + rest)) post := by
    simpa only [oneStack] using guardRule
  have guardArg := wp_local_get cfg ((fuel + 6) + 7) (14 * op + (6 * op + rest)) (lowStore s op index scratch m0 m1)
    limits base.toArray f callers (.call 464 :: installCode) 0 (.i32 pointer) post hpLocal (c9.mono (by omega)) guardNext
  have hmHigh : (highStore s op index scratch m0).modules[frame.inst]? = some mi := by simpa only [highStore, copiedWord, paid, chargedStore, storeI32_modules] using hm
  have lowNext : WP cfg (((fuel + 6) + 7) + 1) (.next (atCode (lowStore s op index scratch m0 m1) limits base.toArray
      {frame with locals := frame.locals.set! 0 (.i32 (readI32 m1 (scratch.toNat + 8)))} callers guardCode))
      (cfg.regularOpCost + (14 * op + (6 * op + rest))) post := by
    simpa only [guardCode, WNear.Binary.InterfaceSet.guard, List.cons_append, List.nil_append, f, afterFrame] using guardArg
  have lowProof := wp_copy_tee_word cfg (((fuel + 6) + 7) + 1) (cfg.regularOpCost + (14 * op + (6 * op + rest)))
    (highStore s op index scratch m0) limits base.toArray frame callers guardCode 3 0 8 24 scratch mi index m1 post hs hmHigh hi hmem1 hlowRead hlowWrite (c4.mono (by dsimp [op]; omega)) lowNext
  have highNext : WP cfg ((((fuel + 6) + 7) + 1) + 5) (.next (atCode (highStore s op index scratch m0) limits base.toArray frame callers lowCode))
      (5 * op + (cfg.regularOpCost + (14 * op + (6 * op + rest)))) post := by simpa only [lowCode] using lowProof
  have result := wp_copy_word cfg ((((fuel + 6) + 7) + 1) + 5) (5 * op + (cfg.regularOpCost + (14 * op + (6 * op + rest))))
    s limits base.toArray frame callers lowCode 3 12 28 scratch mi index m0 post hs hm hi hmem hhighRead hhighWrite (hc.mono (by dsimp [op]; omega)) highNext
  have fuelEq : fuel + 6 + 7 + 1 + 5 + 4 = fuel + 23 := by omega
  have gasEq : 4 * cfg.regularOpCost + (5 * op + (cfg.regularOpCost + (14 * op + (6 * op + rest)))) = 30 * cfg.regularOpCost + rest := by dsimp [op]; omega
  have codeEq : ([.local_get 3, .local_get 3, .load .i32 none {align := 2, offset := 12}, .store .i32 none {align := 2, offset := 28}] ++ lowCode) =
      (WNear.Binary.InterfaceSet.copyBorrow ++ WNear.Binary.InterfaceSet.guard ++ WNear.Binary.InterfaceSet.install ++ code) := by
    simp only [lowCode, guardCode, installCode, WNear.Binary.InterfaceSet.copyBorrow, List.append_assoc, List.cons_append, List.nil_append]
  exact ValueReturnOuterBody.cast_phase cfg _ _ _ _ s limits base.toArray frame callers _ _ post fuelEq gasEq codeEq result

end WNear.Proofs.InterfaceSetInstallTail
