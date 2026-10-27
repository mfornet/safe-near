import Proofs.StateDispatchStorageCleanup
import Proofs.StateDispatchStorageFinish
import Proofs.StateDispatchLengthGas
import Proofs.StateReadStorageFrame

/-! Residual gas for actual storage-forwarder, release, and accepted return. -/
namespace WNear.Proofs.StateDispatchStorageGas
open Wasm Wasm.Near MeteredLogic MeteredHosts
open StorePairCaller (paid paid_credits)

theorem host_credits (cfg : WasmConfig) (s : Store NearState) (mi : ModuleInst) (index : Nat) (memory : Memory)
    (ctx : NearInterface.Context) (raw : NearInterface.RawStorage) (storage : List (List UInt8 × List UInt8))
    (len ptr reg : UInt64) (key value : List UInt8) (rest : Nat)
    (hi : mi.memAddrs[0]? = some index) (hm : s.mems[index]? = some memory)
    (hr : StorageReadCalls.Ready ⟨memory,s.host⟩ ctx raw storage len ptr reg key value)
    (hc : s.host.gas.Credits (17 * cfg.regularOpCost + StorageReadCalls.cost ⟨memory,s.host⟩ ctx.trie len ptr reg key value + rest)) :
    (StateReadStorage.callAfter cfg s mi ctx.trie len ptr reg key value).host.gas.Credits rest :=
  (StateReadStorage.callAfter_gas cfg s mi index memory ctx raw storage len ptr reg key value rest hi hm hr hc).2.2

theorem cleanup_credits (s : Store NearState) (op index rest : Nat) (counter : UInt32) (memory : Memory)
    (hc : s.host.gas.Credits (43 * op + rest)) :
    (StateDispatchStorageCleanup.after s op index counter memory).host.gas.Credits rest := by
  have cut : 6 * op + (36 * op + (op + rest)) ≤ 43 * op + rest := by omega
  have c0 : (StateDispatchStorageCleanup.releaseBefore s op).host.gas.Credits (36 * op + (op + rest)) :=
    paid_credits s op 6 _ (hc.mono cut)
  have c1 := ValueReturnOuter.releaseAfter_credits (StateDispatchStorageCleanup.releaseBefore s op) op index (op + rest) counter memory c0
  exact paid_credits (StateDispatchStorageCleanup.released s op index counter memory) op 1 rest (by simpa only [StateDispatchStorageCleanup.released,Nat.one_mul] using c1)

theorem finish_credits (s : Store NearState) (op index rest : Nat) (scratch : UInt32)
    (hc : s.host.gas.Credits (34 * op + rest)) :
    (StateDispatchStorageFinish.after s op index scratch).host.gas.Credits rest := by
  simpa only [StateDispatchStorageFinish.after,StateDispatchStorageFinish.returned,
    StateDispatchLengthFinish.after,StateDispatchLengthFinish.returned] using
    StateDispatchLengthGas.finish_credits s op index rest scratch hc

end WNear.Proofs.StateDispatchStorageGas
