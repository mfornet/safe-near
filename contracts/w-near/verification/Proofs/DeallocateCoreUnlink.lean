import Proofs.DeallocateCoreState
import Proofs.DeallocateListCallFrame

/-! The actual local_get2/call575 segment of the captured f582 coalescing path. -/
namespace WNear.Proofs.DeallocateCoreUnlink
open Wasm Wasm.Near MeteredLogic
open DeallocateCore
open WNear.Proofs.StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
set_option maxHeartbeats 300000
attribute [local irreducible] WP readI32 writeI32

def unlinkFrom (s : Store NearState) (op : Nat) (p : Layout) :=
  DeallocateListState.after (unlinkEntered (paid s op 1) op) op (unlinkLayout p)

theorem zeroMemory_wf (p : Layout) (hn : Native p) : (zeroMemory p).wf := by
  have marked := writeI32_spec p.memory p.header.toNat (readI32 p.memory p.header.toNat &&& 4294967294) hn.wf hn.headerBound
  have zero := writeI32_spec (markedMemory p) p.pointer.toNat 0 marked.1
    (by rw [show (markedMemory p).byteSize = p.memory.byteSize from marked.2.1]; exact hn.pointerBound)
  exact zero.1

theorem unlinkFrom_memory (s : Store NearState) (op : Nat) (p : Layout)
    (hm : s.mems[p.memoryIndex]? = some (zeroMemory p)) :
    (unlinkFrom s op p).mems[p.memoryIndex]? = some (unlinkedMemory p) := by
  have h := DeallocateListCall.called_memory (paid s op 1) op (unlinkLayout p)
    (by simpa only [paid, chargedStore, unlinkLayout] using hm)
  simpa only [unlinkLayout, unlinkFrom, unlinkedMemory, DeallocateListCall.called, DeallocateListCall.entered, unlinkEntered] using h

theorem unlinkFrom_fields (s : Store NearState) (op : Nat) (p : Layout) :
    (unlinkFrom s op p).funcs = s.funcs ∧ (unlinkFrom s op p).modules = s.modules ∧
    (unlinkFrom s op p).tables = s.tables ∧ (unlinkFrom s op p).globals = s.globals := by
  simpa only [unlinkFrom, DeallocateListCall.called, DeallocateListCall.entered, unlinkEntered, paid, chargedStore] using
    DeallocateListCall.called_fields (paid s op 1) op (unlinkLayout p)

theorem unlinkFrom_code (s : Store NearState) (op inst : Nat) (p : Layout) (hc : Code s inst p) :
    Code (unlinkFrom s op p) inst p := by
  have hf := unlinkFrom_fields s op p
  rcases hc with ⟨hm, hi, i568, f568, i570, f570, i575, f575, i576, f576⟩
  exact ⟨by rw [hf.2.1]; exact hm, hi, i568, by rw [hf.1]; exact f568,
    i570, by rw [hf.1]; exact f570, i575, by rw [hf.1]; exact f575, i576, by rw [hf.1]; exact f576⟩

theorem unlinkFrom_gas (s : Store NearState) (op rest : Nat) (p : Layout)
    (hc : s.host.gas.Credits (73 * op + rest)) :
    (unlinkFrom s op p).host.gas.burnt = s.host.gas.burnt + 73 * op ∧
    (unlinkFrom s op p).host.gas.promises = s.host.gas.promises ∧
    (unlinkFrom s op p).host.gas.Credits rest := by
  have c := paid_credits s op 1 (72 * op + rest) (hc.mono (by omega))
  have h := DeallocateListCall.called_gas (paid s op 1) op rest (unlinkLayout p) c
  have g := StorePairCaller.paid_gas s op 1 (72 * op + rest) (hc.mono (by omega))
  refine ⟨?_, h.2.1.trans g.2, h.2.2⟩
  change (DeallocateListCall.called (paid s op 1) op (unlinkLayout p)).host.gas.burnt = _
  rw [h.1, g.1]; omega

theorem unlinkFrom_credits (s : Store NearState) (op rest : Nat) (p : Layout)
    (hc : s.host.gas.Credits (73 * op + rest)) : (unlinkFrom s op p).host.gas.Credits rest :=
  (unlinkFrom_gas s op rest p hc).2.2

/-- Exactly the original f582 two-instruction call segment. Native link flags
and bounds discharge the concrete helper's accepted branch. -/
theorem wp_unlink (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (p : Layout) (post : Post)
    (hcode : Code s frame.inst p) (hm : s.mems[p.memoryIndex]? = some (zeroMemory p))
    (hl : frame.locals[2]? = some (.i32 p.header)) (hn : Native p)
    (hd : callers.length + 1 < limits.maxCallDepth)
    (hc : s.host.gas.Credits (73 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (unlinkFrom s cfg.regularOpCost p) limits base.toArray frame callers code)) rest post) :
    WP cfg (fuel + 68) (.next (atCode s limits base.toArray frame callers (.local_get 2 :: .call 575 :: code)))
      (73 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  have hm1 : (paid s op 1).modules[frame.inst]? = some p.mi := by simpa only [paid, chargedStore] using hcode.module
  have hf1 : (paid s op 1).funcs[p.address575]? = some (.wasm WNear.Binary.DeallocateList.unlinkSignature frame.inst WNear.Binary.DeallocateList.unlinkFunction) := by
    simpa only [paid, chargedStore] using hcode.function575
  have mem1 : (paid s op 1).mems[p.memoryIndex]? = some (zeroMemory p) := by simpa only [paid, chargedStore] using hm
  have next : WP cfg fuel (.next (atCode (DeallocateListCall.called (paid s op 1) op (unlinkLayout p)) limits base.toArray frame callers code)) rest post := by
    simpa only [unlinkFrom, DeallocateListCall.called, DeallocateListCall.entered, unlinkEntered, op] using hnext
  have call := DeallocateListCall.wp_call cfg fuel rest (paid s op 1) limits base frame callers code (unlinkLayout p) p.address575 post
    hm1 hcode.index575 hf1 hcode.memoryIndex mem1 (zeroMemory_wf p hn) hn.nodeBound hn.firstNonzero hn.firstFlag hn.firstBound hn.secondNonzero hn.secondBound hd
    (paid_credits s op 1 _ (hc.mono (by dsimp [op]; omega))) next
  have result := wp_local_get cfg (fuel + 67) (72 * op + rest) s limits base.toArray frame callers (.call 575 :: code) 2 (.i32 p.header) post hl
    (hc.mono (by dsimp [op]; omega)) (by simpa [unlinkLayout, paid, op] using call)
  have ge : cfg.regularOpCost + (72 * op + rest) = 73 * cfg.regularOpCost + rest := by dsimp [op]; omega
  exact ValueReturnOuterBody.cast_phase cfg _ _ _ _ s limits base.toArray frame callers _ _ post rfl ge rfl result

end WNear.Proofs.DeallocateCoreUnlink
