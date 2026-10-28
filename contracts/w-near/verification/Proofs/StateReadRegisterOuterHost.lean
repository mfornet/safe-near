import Proofs.StateReadRegisterOuterPhases
import Proofs.StateReadRegisterOuterSetupFrame
import Proofs.StateDispatchPrefixHost
import Proofs.StateDispatchReadHost
import Proofs.AllocateVectorOuterHost

/-! Register file and cost table are framed through the real523 length and allocation calls. -/
namespace WNear.Proofs.StateReadRegisterOuter
open Wasm Wasm.Near MeteredLogic MeteredHosts
open StorePairCaller (paid)
set_option maxRecDepth 16384
attribute [local irreducible] StateDispatchLength.finalStore StateDispatchLength.returned StateDispatchLength.arguments StateDispatchLength.checked StateDispatchLength.low StateDispatchLength.high StateDispatchLength.acquired StateDispatchLengthOuter.finalStore StateDispatchLengthOuter.looked looked guarded vectorArguments allocated
private def kept (host : NearState) := (host.registers,host.extCosts)
private theorem kept_mask (s : Store NearState) (host : NearState)
    (h : {host with gas:=s.host.gas,gasProfile:=s.host.gasProfile}=s.host) : kept host=kept s.host := by
  have z := congrArg kept h
  exact z
private theorem kept_paid (s : Store NearState) (op n : Nat) : kept (paid s op n).host=kept s.host := by
  induction n with | zero=>rfl | succ n ih=>exact ih
private theorem kept_charge (s : Store NearState) (n : Nat) : kept (chargedStore s n).host=kept s.host := rfl
private theorem kept_global (s : Store NearState) (i : Nat) (v : Value) : kept (setGlobal s i v).host=kept s.host := rfl
private theorem kept_store32 (s : Store NearState) (i a : Nat) (m : Memory) (v : UInt32) : kept (storeI32 s i a m v).host=kept s.host := rfl
private theorem kept_prefix (s : Store NearState) (op : Nat) (p : StateDispatchPrefix.Layout) :
    kept (StateDispatchPrefix.acquired s op p).host=kept s.host := kept_mask s _ (StateDispatchPrefix.acquired_host s op p)
private theorem kept_length_host (cfg : WasmConfig) (s : Store NearState) (mi : ModuleInst) :
    kept (StateReadRegister.lengthCallAfter cfg s mi).host=kept s.host := by
  have h := congrArg kept (applyCharges_frame (RegisterCalls.beforeCall cfg (paid (StateReadRegister.enteredLength s cfg.regularOpCost) cfg.regularOpCost 1) mi).host
    [.ext "base"] (by simp [BurnsOnly]))
  simpa only [StateReadRegister.lengthCallAfter,StateReadRegister.lengthAfter,RegisterCalls.lengthStore,commitHost_host,
    RegisterCalls.lengthAfter,RegisterRead.paid,Output.paidStore,RegisterCalls.beforeCall,paid,StateReadRegister.enteredLength,chargedStore,chargeHost,kept] using h
private theorem kept_release (s : Store NearState) (op index : Nat) (counter : UInt32) (memory : Memory) :
    kept (ValueReturnOuter.releaseAfter s op index counter memory).host=kept s.host := by
  simp only [ValueReturnOuter.releaseAfter,ValueReturnBorrowCounters.releasedStore,ValueReturnBorrowCounters.calledSwapStore,ValueReturnBorrowCounters.swapEntryStore,ValueReturnBorrowCounters.swapStore,
    ValueReturnOuter.nonnullEntry,kept_paid,kept_charge,kept_store32]
private theorem kept_return (s : Store NearState) (op index : Nat) (sp : UInt32) :
    kept (StateDispatchReturn.callAfter s op index sp).host=kept s.host := by
  rw [StateDispatchReturn.callAfter]
  exact (kept_mask _ _ (StateDispatchReturn.after_host _ _ _ _)).trans (kept_charge _ _ |>.trans (kept_charge _ _))
private theorem kept_length (cfg : WasmConfig) (s : Store NearState) (p : StateDispatchLength.Layout) :
    kept (StateDispatchLength.callAfter cfg s p).host=kept s.host := by
  rw [StateDispatchLength.callAfter,StateDispatchLength.finalStore,StateDispatchLengthFinish.after,StateDispatchLengthFinish.afterReturn,
    kept_paid,kept_global,kept_paid,kept_paid,StateDispatchLengthFinish.returned,kept_return,kept_paid,
    StateDispatchLength.cleaned,StateDispatchLengthCleanup.after,kept_paid,StateDispatchLengthCleanup.released,kept_release,
    StateDispatchLengthCleanup.releaseBefore,kept_paid,StateDispatchLength.returned,kept_length_host,
    StateDispatchLength.arguments,kept_paid,StateDispatchLength.checked,ValueReturnOuter.nonnullAfter,kept_paid,ValueReturnOuter.nonnullEntry,
    kept_charge,kept_charge,kept_paid,StateDispatchLength.low,kept_store32,kept_paid,StateDispatchLength.high,kept_store32,kept_paid,
    StateDispatchLength.acquired,kept_prefix,StateDispatchLength.entered,kept_charge,kept_charge]
private theorem kept_outer_length (cfg : WasmConfig) (s : Store NearState) (p : StateDispatchLengthOuter.Layout) :
    kept (StateDispatchLengthOuter.callAfter cfg s p).host=kept s.host := by
  rw [StateDispatchLengthOuter.callAfter,StateDispatchLengthOuter.finalStore]
  have h := kept_mask _ _ (StateDispatchLengthOuterTail.after_host (StateDispatchLengthOuter.looked cfg (StateDispatchLengthOuter.entered s cfg.regularOpCost) p)
    cfg.regularOpCost p.inner.memoryIndex p.inner.globalIndex (StateDispatchLength.finalMemory p.inner) p.out (StateDispatchLengthOuter.scratch p)
    (StateDispatchLengthOuter.resultValue (StateDispatchLengthOuter.entered s cfg.regularOpCost) p))
  rw [h,StateDispatchLengthOuter.looked,kept_length]
  exact (kept_mask _ _ (StateDispatchLengthOuter.arguments_host _ _ _)).trans (kept_charge _ _ |>.trans (kept_charge _ _))

theorem looked_costs (cfg : WasmConfig) (s : Store NearState) (p : Layout) : (looked cfg s p).host.extCosts=s.host.extCosts := by
  have h : kept (looked cfg s p).host=kept s.host := by
    rw [looked,kept_outer_length]
    exact Prod.ext (lengthArguments_registers s cfg.regularOpCost p) (lengthArguments_costs s cfg.regularOpCost p)
  exact congrArg Prod.snd h

theorem looked_registers (cfg : WasmConfig) (s : Store NearState) (p : Layout) : (looked cfg s p).host.registers=s.host.registers := by
  have h : kept (looked cfg s p).host=kept s.host := by
    rw [looked,kept_outer_length]
    exact Prod.ext (lengthArguments_registers s cfg.regularOpCost p) (lengthArguments_costs s cfg.regularOpCost p)
  exact congrArg Prod.fst h
private theorem kept_looked (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    kept (looked cfg s p).host=kept s.host := Prod.ext (looked_registers cfg s p) (looked_costs cfg s p)
private theorem kept_vector_arguments (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    kept (vectorArguments cfg s p).host=kept s.host := by
  rw [vectorArguments,kept_paid,guarded,kept_paid,kept_looked]
private theorem kept_allocated (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    kept (allocated cfg s p).host=kept s.host := by
  rw [allocated]
  exact (kept_mask _ _ (AllocateVectorOuter.callAfter_functional_host cfg (vectorArguments cfg s p) (actualVector p))).trans (kept_vector_arguments cfg s p)

theorem allocated_costs (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    (allocated cfg s p).host.extCosts=s.host.extCosts := congrArg Prod.snd (kept_allocated cfg s p)
theorem allocated_registers (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    (allocated cfg s p).host.registers=s.host.registers := congrArg Prod.fst (kept_allocated cfg s p)
theorem readArguments_costs (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    (readArguments cfg s p).host.extCosts=s.host.extCosts := by
  have h : kept (readArguments cfg s p).host=kept s.host := by rw [readArguments,kept_paid,kept_allocated]
  exact congrArg Prod.snd h
theorem readArguments_registers (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    (readArguments cfg s p).host.registers=s.host.registers := by
  have h : kept (readArguments cfg s p).host=kept s.host := by rw [readArguments,kept_paid,kept_allocated]
  exact congrArg Prod.fst h

end WNear.Proofs.StateReadRegisterOuter
