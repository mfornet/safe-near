import Proofs.StateDispatchReadCleanup
import Proofs.StateDispatchReadFinish
import Proofs.StateReadRegisterCall

/-! Residual credits for actual f240, f435 release, and the accepted zero-status epilogue. -/
namespace WNear.Proofs.StateDispatchReadGas
open Wasm Wasm.Near MeteredLogic MeteredHosts
open StorePairCaller (paid paid_credits)

theorem host_credits (cfg : WasmConfig) (s : Store NearState) (mi : ModuleInst)
    (ptr : UInt64) (bytes : List UInt8) (rest : Nat)
    (hc : s.host.gas.Credits (15*cfg.regularOpCost+RegisterRead.readCost s.host bytes.length+rest)) :
    (StateReadRegister.readCallAfter cfg s mi ptr bytes).host.gas.Credits rest := by
  let op := cfg.regularOpCost
  have cut : op+(11*op+(3*op+RegisterRead.readCost s.host bytes.length+rest)) ≤
      15*cfg.regularOpCost+RegisterRead.readCost s.host bytes.length+rest := by dsimp [op]; omega
  have c0 := GasCounter.burn_credits s.host.gas op _ (hc.mono cut)
  have c1 := GasCounter.burn_credits (chargedStore s op).host.gas (11*op) _ c0.2.2.2
  have cbody : (StateReadRegister.enteredRead s op).host.gas.Credits
      (3*cfg.regularOpCost+RegisterRead.readCost (StateReadRegister.enteredRead s op).host bytes.length+rest) := by
    simpa only [StateReadRegister.enteredRead,RegisterRead.readCost,chargedStore,chargeHost,op] using c1.2.2.2
  exact StateReadRegister.readAfter_credits cfg (StateReadRegister.enteredRead s op) mi ptr bytes rest cbody

theorem cleanup_credits (s : Store NearState) (op index rest : Nat) (counter : UInt32) (memory : Memory)
    (hc : s.host.gas.Credits (42*op+rest)) :
    (StateDispatchReadCleanup.after s op index counter memory).host.gas.Credits rest := by
  have cut : 5*op+(36*op+(op+rest)) ≤ 42*op+rest := by omega
  have c0 : (StateDispatchReadCleanup.releaseBefore s op).host.gas.Credits (36*op+(op+rest)) :=
    paid_credits s op 5 _ (hc.mono cut)
  have c1 := ValueReturnOuter.releaseAfter_credits (StateDispatchReadCleanup.releaseBefore s op) op index (op+rest) counter memory c0
  exact paid_credits (StateDispatchReadCleanup.released s op index counter memory) op 1 rest
    (by simpa only [StateDispatchReadCleanup.released,Nat.one_mul] using c1)

theorem finish_credits (s : Store NearState) (op index rest : Nat) (scratch : UInt32)
    (hc : s.host.gas.Credits (27*op+rest)) :
    (StateDispatchReadFinish.after s op index scratch).host.gas.Credits rest := by
  have cut : op+(22*op+(4*op+rest)) ≤ 27*op+rest := by omega
  have c0 : (paid s op 1).host.gas.Credits (22*op+(4*op+rest)) :=
    paid_credits s op 1 _ (hc.mono (by simpa only [Nat.one_mul] using cut))
  have c1 := ValueReturnOuter.checkAfter_credits (paid s op 1) op index (4*op+rest) scratch c0
  exact paid_credits (StateDispatchReadFinish.checked s op index scratch) op 4 rest c1

end WNear.Proofs.StateDispatchReadGas
