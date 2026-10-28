import Proofs.StateReadRegisterFrame

/-! All register-host charges are external costs. Thus action profiling and
all functional host fields except the synchronized context.usedGas are preserved, including on charge failure. -/
namespace WNear.Proofs.StateReadRegister
open Wasm Wasm.Near MeteredLogic MeteredHosts
open StorePairCaller (paid)
set_option maxRecDepth 16384

def functionalHostView (seed host : NearState) := {host with gas:=seed.gas,gasProfile:=seed.gasProfile,context:={host.context with usedGas:=seed.context.usedGas}}
theorem view_charge (seed : NearState) (s : Store NearState) (cost : Nat) :
    functionalHostView seed (chargedStore s cost).host=functionalHostView seed s.host := rfl
theorem view_paid (seed : NearState) (s : Store NearState) (op n : Nat) : functionalHostView seed (paid s op n).host=functionalHostView seed s.host := by
  induction n with |zero=>rfl |succ n ih=>exact ih
/-- Reset precisely the three gas observer fields, retaining actionProfile. -/
theorem view_mask (seed before after : NearState)
    (h : functionalHostView before after=before) :
    functionalHostView seed after=functionalHostView seed before := by
  have eq := congrArg (functionalHostView seed) h
  exact eq

private theorem view_ext (seed ns : NearState) (name : String) (times : Nat) :
    functionalHostView seed (applyCharge ns (.ext name times)).1=functionalHostView seed ns := rfl
theorem view_charges (seed ns : NearState) (charges : List Charge)
    (hext : ∀ c∈charges,∃ name times,c=.ext name times) :
    functionalHostView seed (applyCharges ns charges).1=functionalHostView seed ns := by
  induction charges generalizing ns with
  | nil => rfl
  | cons c cs ih =>
    obtain ⟨name,times,hc⟩ := hext c (List.mem_cons_self)
    subst c
    have tail : ∀ c∈cs,∃ name times,c=.ext name times := fun c hc=>hext c (List.mem_cons_of_mem _ hc)
    cases step : applyCharge ns (.ext name times) with
    | mk after error =>
      have frame : functionalHostView seed after=functionalHostView seed ns := by
        have eq := congrArg (fun x : NearState × Option HostError=>functionalHostView seed x.1) step
        exact eq.symm.trans (view_ext seed ns name times)
      cases error with
      | none =>
        simp only [applyCharges,step]
        exact (ih after tail).trans frame
      | some error =>
        simp only [applyCharges,step]
        exact frame

private theorem view_readStore (seed : NearState) (cfg : WasmConfig) (s : Store NearState) (mi : ModuleInst)
    (ptr : UInt64) (bytes : List UInt8) :
    functionalHostView seed (RegisterCalls.readStore cfg s mi ptr bytes).host=functionalHostView seed s.host := by
  have ext : ∀ c∈RegisterRead.readCharges bytes.length,∃ name times,c=.ext name times := by
    intro c hc
    simp only [RegisterRead.readCharges,List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with h|h|h|h|h <;> subst c <;> exact ⟨_,_,rfl⟩
  have frame := view_charges seed (RegisterCalls.beforeCall cfg s mi).host (RegisterRead.readCharges bytes.length) ext
  simp only [RegisterCalls.readStore,commitHost_host,RegisterCalls.readAfter,RegisterRead.paid,Output.paidStore]
  change functionalHostView seed { (applyCharges (RegisterCalls.beforeCall cfg s mi).host (RegisterRead.readCharges bytes.length)).1 with context := { (applyCharges (RegisterCalls.beforeCall cfg s mi).host (RegisterRead.readCharges bytes.length)).1.context with usedGas := _ } } = functionalHostView seed s.host
  change functionalHostView seed (applyCharges (RegisterCalls.beforeCall cfg s mi).host (RegisterRead.readCharges bytes.length)).1 = functionalHostView seed s.host
  exact frame.trans (view_charge seed s cfg.regularOpCost)
private theorem view_lengthStore (seed : NearState) (cfg : WasmConfig) (s : Store NearState) (mi : ModuleInst) :
    functionalHostView seed (RegisterCalls.lengthStore cfg s mi).host=functionalHostView seed s.host := by
  have ext : ∀ c∈[Charge.ext "base"],∃ name times,c=.ext name times := by
    intro c hc
    have eq : c=Charge.ext "base" := List.mem_singleton.mp hc
    subst c
    exact ⟨_,_,rfl⟩
  have frame := view_charges seed (RegisterCalls.beforeCall cfg s mi).host [.ext "base"] ext
  simp only [RegisterCalls.lengthStore,commitHost_host,RegisterCalls.lengthAfter,RegisterRead.paid,Output.paidStore]
  change functionalHostView seed { (applyCharges (RegisterCalls.beforeCall cfg s mi).host [.ext "base"]).1 with context := { (applyCharges (RegisterCalls.beforeCall cfg s mi).host [.ext "base"]).1.context with usedGas := _ } } = functionalHostView seed s.host
  change functionalHostView seed (applyCharges (RegisterCalls.beforeCall cfg s mi).host [.ext "base"]).1 = functionalHostView seed s.host
  exact frame.trans (view_charge seed s cfg.regularOpCost)

theorem readCallAfter_functional_host (cfg : WasmConfig) (s : Store NearState) (mi : ModuleInst)
    (ptr : UInt64) (bytes : List UInt8) :
    {(readCallAfter cfg s mi ptr bytes).host with gas:=s.host.gas,gasProfile:=s.host.gasProfile,context:={(readCallAfter cfg s mi ptr bytes).host.context with usedGas:=s.host.context.usedGas}}=s.host := by
  change functionalHostView s.host (readCallAfter cfg s mi ptr bytes).host=s.host
  rw [readCallAfter,readAfter,view_readStore,view_paid]
  rfl

theorem lengthCallAfter_functional_host (cfg : WasmConfig) (s : Store NearState) (mi : ModuleInst) :
    {(lengthCallAfter cfg s mi).host with gas:=s.host.gas,gasProfile:=s.host.gasProfile,context:={(lengthCallAfter cfg s mi).host.context with usedGas:=s.host.context.usedGas}}=s.host := by
  change functionalHostView s.host (lengthCallAfter cfg s mi).host=s.host
  rw [lengthCallAfter,lengthAfter,view_lengthStore,view_paid]
  rfl
theorem readCallAfter_actionProfile (cfg : WasmConfig) (s : Store NearState) (mi : ModuleInst)
    (ptr : UInt64) (bytes : List UInt8) :
    (readCallAfter cfg s mi ptr bytes).host.actionProfile=s.host.actionProfile := by
  have eq := congrArg NearState.actionProfile (readCallAfter_functional_host cfg s mi ptr bytes)
  exact eq

theorem lengthCallAfter_actionProfile (cfg : WasmConfig) (s : Store NearState) (mi : ModuleInst) :
    (lengthCallAfter cfg s mi).host.actionProfile=s.host.actionProfile := by
  have eq := congrArg NearState.actionProfile (lengthCallAfter_functional_host cfg s mi)
  exact eq
end WNear.Proofs.StateReadRegister
