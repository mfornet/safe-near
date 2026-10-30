import Spec.Contract
import NearVM.Host
import Bridge.Exported

/-! The input domain admitted by the current function-call boundary. -/
namespace WNear.Binary.InputDomain
open NearInterface Wasm Wasm.Near

/-- The current boundary's well-formedness conditions do not inspect argument bytes. -/
theorem wf_with_args (ctx : Context) (raw : RawStorage) (hwf : ctx.WF raw) (args : List UInt8) :
    ({ ctx with args := args } : Context).WF raw := by
  cases hwf
  constructor <;> assumption

/-- Any well-formed context admits arguments exceeding any given byte bound.
This is a domain fact, not a proof about the execution of those arguments. -/
theorem wf_arguments_unbounded (ctx : Context) (raw : RawStorage) (hwf : ctx.WF raw) (bound : Nat) :
    ∃ ctx' : Context, ctx'.WF raw ∧ ctx'.protocol = ctx.protocol ∧
      ctx'.method = ctx.method ∧ ctx'.prepaidGas = ctx.prepaidGas ∧ bound < ctx'.args.length := by
  refine ⟨{ ctx with args := List.replicate (bound + 1) 32 }, ?_, rfl, rfl, rfl, ?_⟩
  · exact wf_with_args ctx raw hwf _
  · simp

/-- Register 0 rejects an oversized input before the contract can parse it.
This is the host operation only, not the complete deployed-method execution. -/
theorem input_register_limit_trap (st : HostStore NearState) (bound : Nat)
    (hconfig : st.host.config.maxRegisterLen = some bound)
    (hlen : bound < st.host.context.input.length) :
    inputFn.invoke st [.i64 0] = .Trap st "input: register size exceeded" := by
  simp [inputFn, writeRegisterResult, checkedSetRegister?, withinLimit, u64Max, hconfig, Nat.not_le.mpr hlen]
  rfl

/-- The current accepted-call disjunction forbids this panic when the model
succeeds, regardless of available gas. Instantiating the execution premise is
separate from this logical obstruction. -/
theorem not_at_of_input_panic (cfg : WNear.Config) (size : Nat)
    (codeOf : List UInt8 → Near.ContractCode) (raw : RawStorage)
    (st : Option WNear.State) (ctx : Context) (a : WNear.AccountId)
    (hparse : (WNear.wnear cfg).Parses ctx.method ctx.args (.ftBalanceOf a))
    (hstep : ∃ output, (WNear.wnear cfg).step ctx st (.ftBalanceOf a) = .ok output)
    (hobs : (Near.Boundary.nearRuntime.exec (WNear.Binary.wCode size codeOf) raw ctx).outcome =
      .error (.panic "input: register size exceeded")) :
    ¬ WNear.Binary.Exported.At cfg size codeOf raw st ctx := by
  intro hat
  obtain ⟨output, hstep⟩ := hstep
  rcases (hat.2.1 (.ftBalanceOf a) hparse).2 with hmatch | ⟨hresource, _⟩
  · rw [hstep] at hmatch
    have hout := hmatch.1
    rw [hobs] at hout
    cases hout
  · rcases hresource with hgas | hproof
    · rw [hobs] at hgas
      cases hgas
    · rw [hobs] at hproof
      cases hproof

/-- The precise still-open formal witness corresponding to the executable finding. -/
def InputRegisterMismatchWitness (cfg : WNear.Config) (size : Nat)
    (codeOf : List UInt8 → Near.ContractCode) (protocol : RuntimeConfig) : Prop :=
  ∃ (raw : RawStorage) (st : Option WNear.State) (ctx : Context) (a : WNear.AccountId),
    (WNear.wnear cfg).Represents raw st ∧ ctx.WF raw ∧ ctx.protocol = protocol ∧
    ctx.protocol.wasm.limits.maxRegisterSize < ctx.args.length ∧
    (WNear.wnear cfg).Parses ctx.method ctx.args (.ftBalanceOf a) ∧
    (∃ output, (WNear.wnear cfg).step ctx st (.ftBalanceOf a) = .ok output) ∧
    (Near.Boundary.nearRuntime.exec (WNear.Binary.wCode size codeOf) raw ctx).outcome =
      .error (.panic "input: register size exceeded")

/-- An instantiated witness contradicts the unchanged full refinement statement. -/
theorem mismatch_refutes_refinement (cfg : WNear.Config) (size : Nat)
    (codeOf : List UInt8 → Near.ContractCode) (protocol : RuntimeConfig)
    (hwitness : InputRegisterMismatchWitness cfg size codeOf protocol) :
    ¬ Refines Near.Boundary.nearRuntime protocol (WNear.Binary.wCode size codeOf) (WNear.wnear cfg) := by
  obtain ⟨raw, st, ctx, a, hrep, hwf, hprotocol, _hlarge, hparse, hstep, hobs⟩ := hwitness
  intro hrefines
  exact not_at_of_input_panic cfg size codeOf raw st ctx a hparse hstep hobs
    (hrefines raw st ctx hrep hwf hprotocol)

end WNear.Binary.InputDomain
