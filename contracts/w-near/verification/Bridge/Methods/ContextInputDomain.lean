import Spec.Contract
import NearVM.Host
import Bridge.Exported

/-! The input domain admitted by the current function-call boundary. -/
namespace WNear.Binary.InputDomain
open NearInterface Wasm Wasm.Near

/-- Protocol input limits needed to rule out the register-size host failure.
The pinned JSON instantiation is a named open verification obligation. -/
def InputLimitsOrdered (protocol : RuntimeConfig) : Prop :=
  protocol.wasm.limits.maxArgumentsLength ≤ protocol.wasm.limits.maxRegisterSize

/-- Replacing arguments preserves well-formedness when the replacement is receipt-valid. -/
theorem wf_with_args (ctx : Context) (raw : RawStorage) (hwf : ctx.WF raw) (args : List UInt8)
    (hargs : args.length ≤ ctx.protocol.wasm.limits.maxArgumentsLength) :
    ({ ctx with args := args } : Context).WF raw := by
  cases hwf
  constructor <;> assumption

/-- The reviewed incoming receipt domain bounds every admitted argument list. -/
theorem wf_arguments_bounded (ctx : Context) (raw : RawStorage) (hwf : ctx.WF raw) :
    ctx.args.length ≤ ctx.protocol.wasm.limits.maxArgumentsLength :=
  hwf.arguments_length

/-- The runtime action-list validator supplies exactly the new context premise.
This does not derive the other Context.WF fields or prove incoming receipt processing. -/
theorem validated_actions_arguments (ctx : Context) (actions : List Near.Action)
    (method : String) (gas deposit : Nat)
    (hvalid : Near.validateActions ctx.protocol.wasm.limits actions = .ok ())
    (hmem : Near.Action.functionCall method ctx.args gas deposit ∈ actions) :
    ctx.args.length ≤ ctx.protocol.wasm.limits.maxArgumentsLength :=
  Near.validateActions_functionCall_arguments _ _ _ _ _ _ hvalid hmem

/-- The receipt limit suffices for the input register whenever the protocol orders the limits.
The pinned JSON instantiation of this numerical relation remains a separate obligation. -/
theorem wf_input_fits_register (ctx : Context) (raw : RawStorage) (hwf : ctx.WF raw)
    (hlimits : InputLimitsOrdered ctx.protocol) :
    ctx.args.length ≤ ctx.protocol.wasm.limits.maxRegisterSize :=
  Nat.le_trans hwf.arguments_length hlimits

/-- At the actual input host call, receipt-valid input fits register 0.
Gas charging around this host operation is separate. -/
theorem wf_input_register_returns (ctx : Context) (raw : RawStorage) (hwf : ctx.WF raw)
    (hlimits : InputLimitsOrdered ctx.protocol)
    (st : HostStore NearState) (hinput : st.host.context.input = ctx.args)
    (hconfig : st.host.config.maxRegisterLen = some ctx.protocol.wasm.limits.maxRegisterSize) :
    ∃ st', inputFn.invoke st [.i64 0] = .Return [] st' := by
  have hfits := wf_input_fits_register ctx raw hwf hlimits
  simp [inputFn, writeRegisterResult, checkedSetRegister?, withinLimit, u64Max, hconfig, hinput, hfits]

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

/-- Historical mismatch shape. Receipt-valid contexts cannot instantiate this when
the protocol argument limit is at most its register limit. -/
def InputRegisterMismatchWitness (cfg : WNear.Config) (size : Nat)
    (codeOf : List UInt8 → Near.ContractCode) (protocol : RuntimeConfig) : Prop :=
  ∃ (raw : RawStorage) (st : Option WNear.State) (ctx : Context) (a : WNear.AccountId),
    (WNear.wnear cfg).Represents raw st ∧ ctx.WF raw ∧ ctx.protocol = protocol ∧
    ctx.protocol.wasm.limits.maxRegisterSize < ctx.args.length ∧
    (WNear.wnear cfg).Parses ctx.method ctx.args (.ftBalanceOf a) ∧
    (∃ output, (WNear.wnear cfg).step ctx st (.ftBalanceOf a) = .ok output) ∧
    (Near.Boundary.nearRuntime.exec (WNear.Binary.wCode size codeOf) raw ctx).outcome =
      .error (.panic "input: register size exceeded")

/-- The reviewed domain excludes the historical oversized-input witness under the
explicit protocol limit relation; no execution or successful-parse premise is needed. -/
theorem no_mismatch_witness (cfg : WNear.Config) (size : Nat)
    (codeOf : List UInt8 → Near.ContractCode) (protocol : RuntimeConfig)
    (hlimits : InputLimitsOrdered protocol) :
    ¬ InputRegisterMismatchWitness cfg size codeOf protocol := by
  rintro ⟨raw, st, ctx, a, _, hwf, hprotocol, hlarge, _⟩
  have hfits := wf_input_fits_register ctx raw hwf
  rw [hprotocol] at hfits hlarge
  exact Nat.not_lt_of_ge (hfits hlimits) hlarge

/-- A witness would contradict refinement even in the reviewed domain. The
ordered-limit theorem above excludes it for protocols satisfying that relation. -/
theorem mismatch_refutes_refinement (cfg : WNear.Config) (size : Nat)
    (codeOf : List UInt8 → Near.ContractCode) (protocol : RuntimeConfig)
    (hwitness : InputRegisterMismatchWitness cfg size codeOf protocol) :
    ¬ Refines Near.Boundary.nearRuntime protocol (WNear.Binary.wCode size codeOf) (WNear.wnear cfg) := by
  obtain ⟨raw, st, ctx, a, hrep, hwf, hprotocol, _hlarge, hparse, hstep, hobs⟩ := hwitness
  intro hrefines
  exact not_at_of_input_panic cfg size codeOf raw st ctx a hparse hstep hobs
    (hrefines raw st ctx hrep hwf hprotocol)

end WNear.Binary.InputDomain
