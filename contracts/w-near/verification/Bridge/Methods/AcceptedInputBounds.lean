import Bridge.Methods.FtBalanceOfProviderRefines
import Bridge.Methods.ContextInputDomain

/-! Reusable parser growth charges and checked accepted-input domain bounds.
General parser instances and the pinned protocol ceiling remain separate obligations. -/

namespace WNear.Binary.BalanceOf297AbsentCall
open NearInterface NearInterface.ContractModel

theorem accepted_balance_input_nonempty (cfg : WNear.Config) (ctx : Context) (c : WNear.Call)
    (hm : ctx.method = "ft_balance_of") (hp : (WNear.wnear cfg).Parses ctx.method ctx.args c) :
    0 < ctx.args.length := by
  have he : WNear.Call.decode "ft_balance_of" [] = none := by decide +kernel
  change WNear.Call.decode ctx.method ctx.args = some c at hp
  by_contra hn
  have hlen : ctx.args.length = 0 := by omega
  have hempty : ctx.args = [] := by
    cases hbs : ctx.args with
    | nil => rfl
    | cons b bs => simp [hbs] at hlen
  rw [hm, hempty, he] at hp
  cases hp

end WNear.Binary.BalanceOf297AbsentCall

namespace WNear.Binary.InputDomain
open NearInterface Wasm Wasm.Near

/-- The exact protocol argument ceiling used by the deployed parser resource proof. -/
def ArgumentLimitV86 (protocol : RuntimeConfig) : Prop :=
  protocol.wasm.limits.maxArgumentsLength ≤ 4194304

theorem wf_arguments_small (ctx : Context) (raw : WNear.RawStorage) (hwf : ctx.WF raw)
    (hl : ArgumentLimitV86 ctx.protocol) : ctx.args.length ≤ 4194304 := by
  have h := wf_arguments_bounded ctx raw hwf
  exact h.trans hl

theorem accepted_balance_input_bounds (cfg : WNear.Config) (ctx : Context) (raw : WNear.RawStorage) (c : WNear.Call)
    (hwf : ctx.WF raw) (hm : ctx.method = "ft_balance_of")
    (hp : (WNear.wnear cfg).Parses ctx.method ctx.args c) (hl : ArgumentLimitV86 ctx.protocol) :
    0 < ctx.args.length ∧ ctx.args.length < 2 ^ 24 := by
  have hpos := BalanceOf297AbsentCall.accepted_balance_input_nonempty cfg ctx c hm hp
  have hsize := wf_arguments_small ctx raw hwf hl
  exact ⟨hpos, by omega⟩

end WNear.Binary.InputDomain

namespace WNear.Binary.BalanceOf297AbsentCall
open NearInterface NearInterface.ContractModel

theorem absent_plan_of_parser_cost (cfg : WNear.Config) (size : Nat) (raw : WNear.RawStorage)
    (modelSt : Option WNear.State) (ctx : Context) (S : WNear.State) (a : WNear.AccountId)
    (hwf : ctx.WF raw) (hm : ctx.method = "ft_balance_of")
    (hp : (WNear.wnear cfg).Parses ctx.method ctx.args (.ftBalanceOf a))
    (hl : InputDomain.ArgumentLimitV86 ctx.protocol)
    (hcost : ∃ parseGas outF, DeployedParserProvider ctx.protocol ctx.args a parseGas outF ∧
      ProviderModelBudget cfg size raw modelSt ctx S a parseGas outF) :
    AbsentParserPlan cfg size raw modelSt ctx S a ctx.args := by
  obtain ⟨parseGas, outF, hProvider, hBudget⟩ := hcost
  have hb := InputDomain.accepted_balance_input_bounds cfg ctx raw (.ftBalanceOf a) hwf hm hp hl
  exact ⟨parseGas, outF, hb.2, hb.1, hProvider, hBudget⟩

end WNear.Binary.BalanceOf297AbsentCall
