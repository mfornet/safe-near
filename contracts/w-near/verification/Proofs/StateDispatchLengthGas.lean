import Proofs.StateDispatchLengthState

/-! Residual gas for the actual f440 helper stages, without execution premises. -/
namespace WNear.Proofs.StateDispatchLengthGas
open Wasm Wasm.Near MeteredLogic MeteredHosts
open StorePairCaller (paid paid_credits)

theorem host_credits (cfg : WasmConfig) (s : Store NearState) (mi : ModuleInst) (rest : Nat)
    (hc : s.host.gas.Credits (13 * cfg.regularOpCost + s.host.extCosts.cost "base" + rest)) :
    (StateReadRegister.lengthCallAfter cfg s mi).host.gas.Credits rest := by
  let op := cfg.regularOpCost
  have c0 := (GasCounter.burn_credits s.host.gas op (10 * op + (2 * op + s.host.extCosts.cost "base" + rest)) (hc.mono (by dsimp [op]; omega))).2.2.2
  have c1 := (GasCounter.burn_credits (chargedStore s op).host.gas (10 * op) (2 * op + s.host.extCosts.cost "base" + rest) c0).2.2.2
  have ca : (StateReadRegister.enteredLength s op).host.gas.Credits
      (2 * cfg.regularOpCost + (StateReadRegister.enteredLength s op).host.extCosts.cost "base" + rest) := by
    simpa only [StateReadRegister.enteredLength,chargedStore,chargeHost,op] using c1
  exact StateReadRegister.lengthAfter_credits cfg (StateReadRegister.enteredLength s op) mi rest ca

theorem cleanup_credits (s : Store NearState) (op index rest : Nat) (counter : UInt32) (memory : Memory)
    (hc : s.host.gas.Credits (45 * op + rest)) :
    (StateDispatchLengthCleanup.after s op index counter memory).host.gas.Credits rest := by
  have c0 : (StateDispatchLengthCleanup.releaseBefore s op).host.gas.Credits (36 * op + (3 * op + rest)) :=
    paid_credits s op 6 _ (hc.mono (by omega))
  have c1 := ValueReturnOuter.releaseAfter_credits (StateDispatchLengthCleanup.releaseBefore s op) op index (3 * op + rest) counter memory c0
  exact paid_credits (StateDispatchLengthCleanup.released s op index counter memory) op 3 rest c1

private theorem after_return_credits (s : Store NearState) (op index rest : Nat) (scratch : UInt32)
    (hc : s.host.gas.Credits (6 * op + rest)) :
    (StateDispatchLengthFinish.afterReturn s op index scratch).host.gas.Credits rest := by
  have c0 := paid_credits s op 1 (5 * op + rest) (hc.mono (by omega))
  have c1 := paid_credits (paid s op 1) op 4 (op + rest) (c0.mono (by omega))
  exact paid_credits (setGlobal (paid (paid s op 1) op 4) index (.i32 (scratch + 16))) op 1 rest
    (by simpa only [setGlobal,Nat.one_mul] using c1)

theorem finish_credits (s : Store NearState) (op index rest : Nat) (scratch : UInt32)
    (hc : s.host.gas.Credits (34 * op + rest)) :
    (StateDispatchLengthFinish.after s op index scratch).host.gas.Credits rest := by
  have c0 := paid_credits s op 2 (26 * op + (6 * op + rest)) (hc.mono (by omega))
  have c1 := StateDispatchReturn.callAfter_credits (paid s op 2) op index (6 * op + rest) scratch c0
  exact after_return_credits (StateDispatchLengthFinish.returned s op index scratch) op index rest scratch c1

end WNear.Proofs.StateDispatchLengthGas
