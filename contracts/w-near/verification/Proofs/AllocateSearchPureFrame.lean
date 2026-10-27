import Proofs.AllocateSearchPhases

/-! Pure fit/call prefixes change only Wasm gas and its diagnostic profile. -/
namespace WNear.Proofs.AllocateSearch
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
attribute [local irreducible] arithmeticDone callbackDone endSubtracted minimumDone Allocate.callbackAfter

theorem arithmeticDone_resources (s : Store NearState) (op : Nat) :
    {arithmeticDone s op with host:=s.host} = s := by
  simp only [arithmeticDone,callbackDone,endSubtracted,Allocate.callbackAfter,AllocateUnits.unitsAfter,
    AllocateUnits.quantumAfter,AllocateUnits.entered9,paid,chargedStore]

theorem minimumDone_resources (s : Store NearState) (op : Nat) :
    {minimumDone s op with host:=s.host} = s := by
  simp only [minimumDone,AllocateUnits.minimumAfter,AllocateUnits.entered9,paid,chargedStore]
  exact arithmeticDone_resources s op

theorem arithmeticDone_credits (s : Store NearState) (op rest : Nat)
    (hc : s.host.gas.Credits (83*op+rest)) : (arithmeticDone s op).host.gas.Credits rest := by
  have cs := paid_credits s op 13 (35*op+(35*op+rest)) (hc.mono (by omega))
  have cs' : (endSubtracted s op).host.gas.Credits (35*op+(35*op+rest)) := by simpa only [endSubtracted] using cs
  have cq := Allocate.callbackAfter_credits (endSubtracted s op) op (35*op+rest) cs'
  have cq' : (callbackDone s op).host.gas.Credits (35*op+rest) := by simpa only [callbackDone] using cq
  have ca := paid_credits (callbackDone s op) op 35 rest cq'
  simpa only [arithmeticDone] using ca

theorem minimumDone_credits (s : Store NearState) (op rest : Nat)
    (hc : s.host.gas.Credits (101*op+rest)) : (minimumDone s op).host.gas.Credits rest := by
  have ca := arithmeticDone_credits s op (18*op+rest) (hc.mono (by omega))
  have cg := paid_credits (arithmeticDone s op) op 1 (17*op+rest) (ca.mono (by omega))
  have cm := AllocateUnits.minimumAfter_credits (paid (arithmeticDone s op) op 1) op rest cg
  simpa only [minimumDone] using cm

theorem arithmeticDone_code (s : Store NearState) (op : Nat) (p : Layout) (inst : Nat) (h : Code s p inst) :
    Code (arithmeticDone s op) p inst := by
  have r := arithmeticDone_resources s op
  exact h.transport s _ p inst (congrArg (fun t=>t.funcs) r) (congrArg (fun t=>t.modules) r) (congrArg (fun t=>t.tables) r)

theorem minimumDone_code (s : Store NearState) (op : Nat) (p : Layout) (inst : Nat) (h : Code s p inst) :
    Code (minimumDone s op) p inst := by
  have r := minimumDone_resources s op
  exact h.transport s _ p inst (congrArg (fun t=>t.funcs) r) (congrArg (fun t=>t.modules) r) (congrArg (fun t=>t.tables) r)
end WNear.Proofs.AllocateSearch
