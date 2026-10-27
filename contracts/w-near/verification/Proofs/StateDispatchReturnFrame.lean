import Proofs.StateDispatchReturnCall
import Proofs.StorePairCallerState

/-! Memory/code/global restoration and exact gas for accepted f432. -/
namespace WNear.Proofs.StateDispatchReturn
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits paid_gas)
set_option maxRecDepth 16384

private theorem paid_globals (s : Store NearState) (op n : Nat) : (paid s op n).globals = s.globals := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

 theorem after_fields (s : Store NearState) (op index : Nat) (sp : UInt32) :
    (after s op index sp).mems = s.mems ∧ (after s op index sp).funcs = s.funcs ∧
    (after s op index sp).modules = s.modules ∧ (after s op index sp).tables = s.tables := by
  simp only [after,suffixAfter,reserved,paid,setGlobal,chargedStore]
  exact ⟨trivial,trivial,trivial,trivial⟩

 theorem after_globals (s : Store NearState) (op index : Nat) (sp : UInt32) (global : GlobalInst)
    (hg : s.globals[index]? = some global) (hv : global.value = .i32 sp) :
    (after s op index sp).globals = s.globals := by
  simp only [after,suffixAfter,reserved,setGlobal,paid_globals,UInt32.sub_add_cancel]
  have hr := StorePairCaller.setGlobal_restore s index (.i32 (sp - 16)) global hg
  simpa only [setGlobal,hv] using hr

 theorem after_host (s : Store NearState) (op index : Nat) (sp : UInt32) :
    {(after s op index sp).host with gas := s.host.gas,gasProfile := s.host.gasProfile} = s.host := by
  simp only [after,suffixAfter,reserved,paid,setGlobal,chargedStore,chargeHost]

private theorem after_gas_eq (s : Store NearState) (op index : Nat) (sp : UInt32) :
    (after s op index sp).host.gas = (paid s op 14).host.gas := rfl

 theorem after_gas (s : Store NearState) (op index rest : Nat) (sp : UInt32)
    (hc : s.host.gas.Credits (14 * op + rest)) :
    (after s op index sp).host.gas.burnt = s.host.gas.burnt + 14 * op ∧
    (after s op index sp).host.gas.promises = s.host.gas.promises ∧
    (after s op index sp).host.gas.Credits rest := by
  rw [after_gas_eq]
  have h := paid_gas s op 14 rest hc
  exact ⟨h.1,h.2,paid_credits s op 14 rest hc⟩

 theorem callAfter_fields (s : Store NearState) (op index : Nat) (sp : UInt32) :
    (callAfter s op index sp).mems = s.mems ∧ (callAfter s op index sp).funcs = s.funcs ∧
    (callAfter s op index sp).modules = s.modules ∧ (callAfter s op index sp).tables = s.tables :=
  after_fields (entered s op) op index sp

 theorem callAfter_globals (s : Store NearState) (op index : Nat) (sp : UInt32) (global : GlobalInst)
    (hg : s.globals[index]? = some global) (hv : global.value = .i32 sp) :
    (callAfter s op index sp).globals = s.globals :=
  after_globals (entered s op) op index sp global hg hv

 theorem callAfter_gas (s : Store NearState) (op index rest : Nat) (sp : UInt32)
    (hc : s.host.gas.Credits (26 * op + rest)) :
    (callAfter s op index sp).host.gas.burnt = s.host.gas.burnt + 26 * op ∧
    (callAfter s op index sp).host.gas.promises = s.host.gas.promises ∧
    (callAfter s op index sp).host.gas.Credits rest := by
  have h0 := GasCounter.burn_credits s.host.gas op (11 * op + (14 * op + rest)) (hc.mono (by omega))
  have h1 := GasCounter.burn_credits (chargedStore s op).host.gas (11 * op) (14 * op + rest) h0.2.2.2
  have h2 := after_gas (entered s op) op index rest sp h1.2.2.2
  refine ⟨?_,h2.2.1.trans (h1.2.2.1.trans h0.2.2.1),h2.2.2⟩
  rw [callAfter,h2.1]
  have b0 : (chargedStore s op).host.gas.burnt = s.host.gas.burnt + op := h0.2.1
  have b1 : (entered s op).host.gas.burnt = (chargedStore s op).host.gas.burnt + 11 * op := h1.2.1
  rw [b1,b0]; omega
end WNear.Proofs.StateDispatchReturn
