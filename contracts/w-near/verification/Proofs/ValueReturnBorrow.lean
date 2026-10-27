import Binary.ValueReturnBorrow
import Proofs.StorePairCallerState
import Proofs.StorePair
import NearVM.MeteredNumericRules

/-! Kernel-checked normal paths of the deployed RefCell pointer/cleanup helpers.
The panic branches are skipped by their actual branch instructions. -/
namespace WNear.Proofs.ValueReturnBorrow
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.StorePairCaller (paid paid_credits paid_gas paid_resources)
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384

/-- Actual f430 body: any nonzero pointer is returned without touching memory. -/
theorem wp_nonnull (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame)
    (callers : List CallFrame) (code : List Instr) (ptr : UInt32) (post : Post)
    (hptr : frame.locals[0]? = some (.i32 ptr)) (hnonzero : ptr ≠ 0)
    (hc : s.host.gas.Credits (3 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 3) limits
      (stack.push (.i32 ptr)) frame callers code)) rest post) :
    WP cfg (fuel + 4) (.next (atCode s limits stack frame callers (WNear.Binary.ValueReturnBorrow.nonnullBody ++ code)))
      (3 * cfg.regularOpCost + rest) post := by
  apply wp_block_empty cfg (fuel + 3) _ s limits stack frame callers _ _ post hc
  rw [show 3 * cfg.regularOpCost + rest = cfg.regularOpCost + (2 * cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 2) _ s limits stack
    (emptyBlockFrame frame stack.size (.local_get 0 :: code)) callers _ 0 (.i32 ptr) post hptr (hc.mono (by omega))
  rw [show 2 * cfg.regularOpCost + rest = cfg.regularOpCost + (cfg.regularOpCost + rest) by omega]
  apply wp_br_if_block_nonzero cfg (fuel + 1) _ (paid s cfg.regularOpCost 1) limits stack frame callers
    (.local_get 0 :: code) WNear.Binary.ValueReturnBorrow.nonnullPanic ptr post hnonzero
  · exact paid_credits s cfg.regularOpCost 1 _ (hc.mono (by omega))
  apply wp_local_get cfg fuel rest (paid s cfg.regularOpCost 2) limits stack frame callers code 0 (.i32 ptr) post hptr
  · exact paid_credits s cfg.regularOpCost 2 _ (hc.mono (by omega))
  · exact hnext

theorem wp_reserve (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame)
    (callers : List CallFrame) (code : List Instr) (mi : ModuleInst) (index : Nat)
    (global : GlobalInst) (sp : UInt32) (slot : Nat) (post : Post)
    (hmodule : s.modules[frame.inst]? = some mi) (hindex : mi.globalAddrs[0]? = some index)
    (hglobal : s.globals[index]? = some global) (hsp : global.value = .i32 sp)
    (hc : s.host.gas.Credits (5 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode
      (setGlobal (paid s cfg.regularOpCost 5) index (.i32 (sp - 16))) limits stack
      {frame with locals := frame.locals.set! slot (.i32 (sp - 16))} callers code)) rest post) :
    WP cfg (fuel + 5) (.next (atCode s limits stack frame callers
      ([.global_get 0, .i32_const 16, .i32_binop .sub, .local_tee slot, .global_set 0] ++ code)))
      (5 * cfg.regularOpCost + rest) post := by
  have h0 : s.host.gas.Credits (cfg.regularOpCost + (4 * cfg.regularOpCost + rest)) := hc.mono (by omega)
  have h1 := paid_credits s cfg.regularOpCost 1 (4 * cfg.regularOpCost + rest) (hc.mono (by omega))
  have h2 := paid_credits s cfg.regularOpCost 2 (3 * cfg.regularOpCost + rest) (hc.mono (by omega))
  have h3 := paid_credits s cfg.regularOpCost 3 (2 * cfg.regularOpCost + rest) (hc.mono (by omega))
  have h4 := paid_credits s cfg.regularOpCost 4 (cfg.regularOpCost + rest) (hc.mono (by omega))
  have hm4 : (paid s cfg.regularOpCost 4).modules[frame.inst]? = some mi := by simpa only [paid, chargedStore] using hmodule
  have hg4 : (paid s cfg.regularOpCost 4).globals[index]? = some global := by simpa only [paid, chargedStore] using hglobal
  have hget := wp_global_get cfg (fuel + 4) (4 * cfg.regularOpCost + rest) s limits stack frame callers
    ([.i32_const 16, .i32_binop .sub, .local_tee slot, .global_set 0] ++ code)
    0 index mi global post hmodule hindex hglobal h0
  rw [hsp] at hget
  rw [show 5 * cfg.regularOpCost + rest = cfg.regularOpCost + (4 * cfg.regularOpCost + rest) by omega]
  apply hget
  rw [show 4 * cfg.regularOpCost + rest = cfg.regularOpCost + (3 * cfg.regularOpCost + rest) by omega]
  apply wp_i32_const cfg (fuel + 3) (3 * cfg.regularOpCost + rest) _ limits _ frame callers _ 16 post
    (by simpa only [paid, show 4 * cfg.regularOpCost + rest = cfg.regularOpCost + (3 * cfg.regularOpCost + rest) by omega] using h1)
  rw [show 3 * cfg.regularOpCost + rest = cfg.regularOpCost + (2 * cfg.regularOpCost + rest) by omega]
  apply wp_i32_sub cfg (fuel + 2) (2 * cfg.regularOpCost + rest) _ limits stack frame callers _ sp 16 post
    (by simpa only [paid, show 3 * cfg.regularOpCost + rest = cfg.regularOpCost + (2 * cfg.regularOpCost + rest) by omega] using h2)
  rw [show 2 * cfg.regularOpCost + rest = cfg.regularOpCost + (cfg.regularOpCost + rest) by omega]
  apply wp_local_tee cfg (fuel + 1) (cfg.regularOpCost + rest) _ limits stack frame callers _ slot (.i32 (sp - 16)) post
    (by simpa only [paid, show 2 * cfg.regularOpCost + rest = cfg.regularOpCost + (cfg.regularOpCost + rest) by omega] using h3)
  apply wp_global_set cfg fuel rest (paid s cfg.regularOpCost 4) limits stack {frame with locals := frame.locals.set! slot (.i32 (sp - 16))} callers code 0 index mi (.i32 (sp - 16)) global post
    hm4 hindex hg4
  · simpa only [paid] using h4
  · simpa only [paid] using hnext

theorem wp_restore (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame)
    (callers : List CallFrame) (code : List Instr) (mi : ModuleInst) (index : Nat)
    (global : GlobalInst) (scratch : UInt32) (slot : Nat) (post : Post)
    (hscratch : frame.locals[slot]? = some (.i32 scratch))
    (hmodule : s.modules[frame.inst]? = some mi) (hindex : mi.globalAddrs[0]? = some index)
    (hglobal : s.globals[index]? = some global)
    (hc : s.host.gas.Credits (4 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode
      (setGlobal (paid s cfg.regularOpCost 4) index (.i32 (scratch + 16))) limits stack frame callers code)) rest post) :
    WP cfg (fuel + 4) (.next (atCode s limits stack frame callers
      ([.local_get slot, .i32_const 16, .i32_binop .add, .global_set 0] ++ code)))
      (4 * cfg.regularOpCost + rest) post := by
  have hm3 : (paid s cfg.regularOpCost 3).modules[frame.inst]? = some mi := by simpa only [paid, chargedStore] using hmodule
  have hg3 : (paid s cfg.regularOpCost 3).globals[index]? = some global := by simpa only [paid, chargedStore] using hglobal
  rw [show 4 * cfg.regularOpCost + rest = cfg.regularOpCost + (3 * cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 3) (3 * cfg.regularOpCost + rest) s limits stack frame callers _ slot (.i32 scratch) post hscratch
    (hc.mono (by omega))
  rw [show 3 * cfg.regularOpCost + rest = cfg.regularOpCost + (2 * cfg.regularOpCost + rest) by omega]
  apply wp_i32_const cfg (fuel + 2) (2 * cfg.regularOpCost + rest) _ limits _ frame callers _ 16 post
  · apply paid_credits s cfg.regularOpCost 1
    exact hc.mono (by omega)
  rw [show 2 * cfg.regularOpCost + rest = cfg.regularOpCost + (cfg.regularOpCost + rest) by omega]
  apply wp_i32_add cfg (fuel + 1) (cfg.regularOpCost + rest) _ limits stack frame callers _ scratch 16 post
  · apply paid_credits s cfg.regularOpCost 2
    exact hc.mono (by omega)
  apply wp_global_set cfg fuel rest (paid s cfg.regularOpCost 3) limits stack frame callers code 0 index mi (.i32 (scratch + 16)) global post
    hm3 hindex hg3
  · apply paid_credits s cfg.regularOpCost 3
    exact hc.mono (by omega)
  · simpa only [paid] using hnext



/-- Actual zero-status guard of f433; the panic tail is not executed. -/
theorem wp_zeroGuard (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame)
    (callers : List CallFrame) (code : List Instr) (post : Post)
    (hstatus : frame.locals[0]? = some (.i32 0))
    (hc : s.host.gas.Credits (3 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 3) limits
      stack frame callers code)) rest post) :
    WP cfg (fuel + 3) (.next (atCode s limits stack
      (emptyBlockFrame frame stack.size code) callers
      ([.local_get 0, .i32_eqz, .br_if 0] ++ WNear.Binary.ValueReturnBorrow.checkPanic)))
      (3 * cfg.regularOpCost + rest) post := by
  rw [show 3 * cfg.regularOpCost + rest = cfg.regularOpCost + (2 * cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 2) _ s limits stack (emptyBlockFrame frame stack.size code)
    callers _ 0 (.i32 0) post hstatus (hc.mono (by omega))
  rw [show 2 * cfg.regularOpCost + rest = cfg.regularOpCost + (cfg.regularOpCost + rest) by omega]
  apply wp_i32_eqz cfg (fuel + 1) _ (paid s cfg.regularOpCost 1) limits stack
    (emptyBlockFrame frame stack.size code) callers _ 0 post
  · exact paid_credits s cfg.regularOpCost 1 _ (hc.mono (by omega))
  apply wp_br_if_block_nonzero cfg fuel rest (paid s cfg.regularOpCost 2) limits stack frame callers
    code WNear.Binary.ValueReturnBorrow.checkPanic _ post (by decide)
  · exact paid_credits s cfg.regularOpCost 2 _ (hc.mono (by omega))
  · exact hnext

theorem paid_add (s : Store NearState) (op a b : Nat) :
    paid (paid s op a) op b = paid s op (a + b) := by
  induction b with
  | zero => rfl
  | succ b ih => simp only [paid, ih]; rfl

/-- Explicit final state of the successful f433 check. -/
def checkedStore (s : Store NearState) (op index : Nat) (sp : UInt32) : Store NearState :=
  setGlobal (paid (setGlobal (paid s op 5) index (.i32 (sp - 16))) op 7) index (.i32 sp)

/-- The normal check has no memory access and accepts every wrapping i32 SP.
Only the actual zero status is assumed. -/
theorem wp_check (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame)
    (callers : List CallFrame) (code : List Instr) (mi : ModuleInst) (index : Nat)
    (global : GlobalInst) (sp : UInt32) (post : Post)
    (hstatus : frame.locals[0]? = some (.i32 0)) (hsize : 2 ≤ frame.locals.size)
    (hmodule : s.modules[frame.inst]? = some mi) (hindex : mi.globalAddrs[0]? = some index)
    (hglobal : s.globals[index]? = some global) (hsp : global.value = .i32 sp)
    (hc : s.host.gas.Credits (12 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (checkedStore s cfg.regularOpCost index sp) limits stack
      {frame with locals := frame.locals.set! 1 (.i32 (sp - 16))} callers code)) rest post) :
    WP cfg (fuel + 13) (.next (atCode s limits stack frame callers
      (WNear.Binary.ValueReturnBorrow.checkBody ++ code))) (12 * cfg.regularOpCost + rest) post := by
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
      simpa only [UInt32.sub_add_cancel, paid_add, checkedStore, reserved, nextFrame] using hnext
    simpa only [WNear.Binary.ValueReturnBorrow.checkEpilogue] using hrestore hpost
  have hguard := wp_zeroGuard cfg (fuel + 4) (4 * cfg.regularOpCost + rest) reserved limits stack nextFrame callers
    (WNear.Binary.ValueReturnBorrow.checkEpilogue ++ code) post hstatusR
    (hr.mono (by omega)) htail
  rw [show fuel + 4 + 3 = fuel + 7 by omega,
    show 3 * cfg.regularOpCost + (4 * cfg.regularOpCost + rest) = 7 * cfg.regularOpCost + rest by omega] at hguard
  have hblock := wp_block_empty cfg (fuel + 7) (7 * cfg.regularOpCost + rest) reserved limits stack nextFrame callers
    ([.local_get 0, .i32_eqz, .br_if 0] ++ WNear.Binary.ValueReturnBorrow.checkPanic)
    (WNear.Binary.ValueReturnBorrow.checkEpilogue ++ code) post hr
  have hblock' := hblock hguard
  rw [show fuel + 7 + 1 = fuel + 8 by omega] at hblock'
  have hentry := wp_reserve cfg (fuel + 8) (7 * cfg.regularOpCost + rest) s limits stack frame callers
    (.block .empty ([.local_get 0, .i32_eqz, .br_if 0] ++ WNear.Binary.ValueReturnBorrow.checkPanic) ::
      (WNear.Binary.ValueReturnBorrow.checkEpilogue ++ code)) mi index global sp 1 post hmodule hindex hglobal hsp
    (hc.mono (by omega))
  have hentry' := hentry hblock'
  rw [show fuel + 8 + 5 = fuel + 13 by omega,
    show 5 * cfg.regularOpCost + (7 * cfg.regularOpCost + rest) = 12 * cfg.regularOpCost + rest by omega] at hentry'
  simpa only [WNear.Binary.ValueReturnBorrow.checkBody,
    WNear.Binary.ValueReturnBorrow.checkPrologue, List.append_assoc, List.cons_append, List.nil_append] using hentry'

/-- Complete active f430, including its free frame exit. -/
theorem wp_nonnull_return (cfg : WasmConfig) (rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (locals : Array Value) (inst : Nat) (ptr : UInt32)
    (hptr : locals[0]? = some (.i32 ptr)) (hnonzero : ptr ≠ 0)
    (hc : s.host.gas.Credits (3 * cfg.regularOpCost + rest)) :
    WP cfg 5 (.next (atCode s limits #[] (resultFrame locals inst) []
      WNear.Binary.ValueReturnBorrow.nonnullBody)) (3 * cfg.regularOpCost + rest)
      (fun remaining final error => remaining = rest ∧
        final = .done [.i32 ptr] (paid s cfg.regularOpCost 3) ∧ error = none) := by
  have hf := wp_finish_i32 cfg 0 rest (paid s cfg.regularOpCost 3) limits locals inst ptr
    (fun remaining final error => remaining = rest ∧
      final = .done [.i32 ptr] (paid s cfg.regularOpCost 3) ∧ error = none)
    (paid_credits s cfg.regularOpCost 3 rest hc) ⟨rfl, rfl, rfl⟩
  have h := wp_nonnull cfg 1 rest s limits #[] (resultFrame locals inst) [] [] ptr (fun remaining final error => remaining = rest ∧
      final = .done [.i32 ptr] (paid s cfg.regularOpCost 3) ∧ error = none) hptr hnonzero hc
  apply h
  exact hf

/-- Exact global restoration, including the original type and mutability. -/
theorem checkedStore_globals (s : Store NearState) (op index : Nat) (sp : UInt32)
    (global : GlobalInst) (hg : s.globals[index]? = some global) (hsp : global.value = .i32 sp) :
    (checkedStore s op index sp).globals = s.globals := by
  have h := WNear.Proofs.StorePairCaller.setGlobal_restore s index (.i32 (sp - 16)) global hg
  simpa only [checkedStore, paid, chargedStore, setGlobal, hsp] using h

/-- All guest resources are untouched by f433's normal path. -/
theorem checkedStore_resources (s : Store NearState) (op index : Nat) (sp : UInt32)
    (global : GlobalInst) (hg : s.globals[index]? = some global) (hsp : global.value = .i32 sp) :
    {checkedStore s op index sp with host := s.host} = s := by
  have h := checkedStore_globals s op index sp global hg hsp
  cases s
  simp_all only [checkedStore, paid, chargedStore, setGlobal]

theorem checkedStore_gas (s : Store NearState) (op index rest : Nat) (sp : UInt32)
    (hc : s.host.gas.Credits (12 * op + rest)) :
    (checkedStore s op index sp).host.gas.burnt = s.host.gas.burnt + 12 * op ∧
    (checkedStore s op index sp).host.gas.promises = s.host.gas.promises ∧
    (checkedStore s op index sp).host.gas.Credits rest := by
  have h5 := paid_gas s op 5 (7 * op + rest) (hc.mono (by omega))
  have c5 := paid_credits s op 5 (7 * op + rest) (hc.mono (by omega))
  have h7 := paid_gas (setGlobal (paid s op 5) index (.i32 (sp - 16))) op 7 rest c5
  have c7 := paid_credits (setGlobal (paid s op 5) index (.i32 (sp - 16))) op 7 rest c5
  refine ⟨?_, ?_, c7⟩
  · change (paid (setGlobal (paid s op 5) index (.i32 (sp - 16))) op 7).host.gas.burnt = _
    rw [h7.1]
    change (paid s op 5).host.gas.burnt + 7 * op = _
    rw [h5.1]; omega
  · exact h7.2.trans h5.2

/-- The active f433 normal path finishes in fourteen interpreter steps and
spends twelve opcodes; entry activation is nine further units. -/
theorem wp_check_return (cfg : WasmConfig) (rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (locals : Array Value) (inst : Nat) (mi : ModuleInst) (index : Nat)
    (global : GlobalInst) (sp : UInt32)
    (hstatus : locals[0]? = some (.i32 0)) (hsize : 2 ≤ locals.size)
    (hm : s.modules[inst]? = some mi) (hi : mi.globalAddrs[0]? = some index)
    (hg : s.globals[index]? = some global) (hsp : global.value = .i32 sp)
    (hc : s.host.gas.Credits (12 * cfg.regularOpCost + rest)) :
    WP cfg 14 (.next (atCode s limits #[] (WNear.Proofs.StorePair.voidFrame locals inst) []
      WNear.Binary.ValueReturnBorrow.checkBody)) (12 * cfg.regularOpCost + rest)
      (fun remaining final error => remaining = rest ∧
        final = .done [] (checkedStore s cfg.regularOpCost index sp) ∧ error = none) := by
  have c := (checkedStore_gas s cfg.regularOpCost index rest sp hc).2.2
  have hf := WNear.Proofs.StorePair.wp_finish_void cfg 0 rest (checkedStore s cfg.regularOpCost index sp)
    limits (locals.set! 1 (.i32 (sp - 16))) inst
    (fun remaining final error => remaining = rest ∧
      final = .done [] (checkedStore s cfg.regularOpCost index sp) ∧ error = none) c ⟨rfl, rfl, rfl⟩
  have h := wp_check cfg 1 rest s limits #[] (WNear.Proofs.StorePair.voidFrame locals inst) [] []
    mi index global sp (fun remaining final error => remaining = rest ∧
      final = .done [] (checkedStore s cfg.regularOpCost index sp) ∧ error = none) hstatus hsize hm hi hg hsp hc
  apply h
  exact hf

end WNear.Proofs.ValueReturnBorrow
