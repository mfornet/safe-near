import NearRuntime.FunctionCallFunding

namespace Near
open Wasm.Near

/-- Successful operations preserve account uniqueness and satisfy the additive
action funding law, for every well-formed input ledger. -/
def ExecM.Funded (operation : ExecM α) (cfg : RuntimeConfig) (price deposit : Nat) : Prop :=
  ∀ before after value, before.state.AccountsUnique →
    operation.run.run before = (.ok value, after) →
    after.state.AccountsUnique ∧ Exec.FundingStep cfg price deposit before after

theorem ExecM.Funded.bind {operation : ExecM α} {next : α → ExecM β}
    {cfg : RuntimeConfig} {price first second : Nat}
    (hfirst : operation.Funded cfg price first) (hnext : ∀ value, (next value).Funded cfg price second) :
    (operation >>= next).Funded cfg price (first + second) := by
  intro before after value hwf hrun
  rw [execM_run_bind] at hrun
  cases he : operation.run.run before with
  | mk result middle =>
    cases result with
    | error error =>
      rw [he] at hrun
      have hbad := congrArg Prod.fst hrun
      cases hbad
    | ok intermediate =>
      have hf := hfirst before middle intermediate hwf he
      have hn := hnext intermediate middle after value hf.1 (by simpa only [he] using hrun)
      exact ⟨hn.1, hf.2.trans hn.2⟩

theorem funded_bind_zero {operation : ExecM α} {next : α → ExecM β} {cfg : RuntimeConfig} {price : Nat}
    (hfirst : operation.Funded cfg price 0) (hnext : ∀ value, (next value).Funded cfg price 0) :
    (operation >>= next).Funded cfg price 0 := hfirst.bind hnext

theorem funded_bind_left_zero {operation : ExecM α} {next : α → ExecM β}
    {cfg : RuntimeConfig} {price deposit : Nat}
    (hfirst : operation.Funded cfg price 0) (hnext : ∀ value, (next value).Funded cfg price deposit) :
    (operation >>= next).Funded cfg price deposit := by simpa only [Nat.zero_add] using hfirst.bind hnext

theorem funded_bind_right_zero {operation : ExecM α} {next : α → ExecM β}
    {cfg : RuntimeConfig} {price deposit : Nat}
    (hfirst : operation.Funded cfg price deposit) (hnext : ∀ value, (next value).Funded cfg price 0) :
    (operation >>= next).Funded cfg price deposit := by simpa only [Nat.add_zero] using hfirst.bind hnext

theorem funded_pure (cfg : RuntimeConfig) (price : Nat) (value : α) :
    (pure value : ExecM α).Funded cfg price 0 := by
  intro before after returned hwf hrun
  have he := congrArg Prod.snd hrun
  change before = after at he
  subst after
  exact ⟨hwf, by simp [Exec.FundingStep]⟩

theorem funded_throw (cfg : RuntimeConfig) (price : Nat) (error : RuntimeError) :
    (throw error : ExecM α).Funded cfg price 0 := by
  intro before after value _ hrun
  have hbad := congrArg Prod.fst hrun
  cases hbad

theorem funded_get (cfg : RuntimeConfig) (price : Nat) : (get : ExecM Exec).Funded cfg price 0 := by
  intro before after value hwf hrun
  have he := congrArg Prod.snd hrun
  change before = after at he
  subst after
  exact ⟨hwf, by simp [Exec.FundingStep]⟩

theorem funded_getState (cfg : RuntimeConfig) (price : Nat) : getState.Funded cfg price 0 := by
  unfold getState
  exact funded_bind_zero (funded_get cfg price) (fun _ => funded_pure cfg price _)

theorem funded_burnGas (cfg : RuntimeConfig) (price fee : Nat) : (burnGas fee).Funded cfg price 0 := by
  intro before after value hwf hrun
  change ((.ok (), { before with gasBurnt := before.gasBurnt + fee, gasUsed := before.gasUsed + fee }) : Except RuntimeError Unit × Exec) =
    (.ok value, after) at hrun
  have he := congrArg Prod.snd hrun
  dsimp only at he
  subst after
  exact ⟨hwf, by simp only [Exec.FundingStep, Exec.totalFunds, Nat.add_mul, Nat.add_zero]; omega⟩

theorem funded_fee (cfg : RuntimeConfig) (price : Nat) (isRefund : Bool) (fee : Nat) :
    (chargeReceiptFee isRefund fee).Funded cfg price 0 := by
  exact funded_burnGas cfg price fee

theorem funded_checkReceiptAction (c : ReceiptCtx) (onlyAction : Bool) (action : Action) :
    (checkReceiptAction c onlyAction action).Funded c.cfg c.action.gasPrice 0 := by
  unfold checkReceiptAction
  repeat (first
    | exact funded_pure _ _ _ | exact funded_throw _ _ _ | exact funded_get _ _ | exact funded_getState _ _
    | (refine funded_bind_zero ?_ (fun _ => ?_)) | split)

theorem funded_checkStorageStake (cfg : RuntimeConfig) (price : Nat) (id : AccountId) :
    (checkStorageStake cfg id).Funded cfg price 0 := by
  unfold checkStorageStake
  repeat (first
    | exact funded_pure _ _ _ | exact funded_throw _ _ _ | exact funded_getState _ _
    | (refine funded_bind_zero ?_ (fun _ => ?_)) | split | (dsimp only; split))

theorem funded_functionCall (c : ReceiptCtx) (method : String) (args : Bytes) (gas deposit : Nat)
    (isLast : Bool) (hreceiver : c.receipt.receiverId ≠ systemAccount) :
    (applyFunctionCall c method args gas deposit isLast).Funded c.cfg c.action.gasPrice deposit := by
  intro before after value hwf hrun
  cases value
  exact ⟨applyFunctionCall_success_accountsUnique c method args gas deposit isLast before after hwf hrun,
    applyFunctionCall_success_funding_step c method args gas deposit isLast before after hwf hreceiver hrun⟩

/-- This currently proved action family supports arbitrary ordered mixtures of
function calls. Other action families require their own concrete funding rules. -/
def FunctionCallFundingAction : Action → Prop
  | .functionCall .. => True
  | _ => False

theorem funded_runReceiptAction_functionCall (c : ReceiptCtx) (onlyAction isLast : Bool)
    (method : String) (args : Bytes) (gas deposit : Nat) (hreceiver : c.receipt.receiverId ≠ systemAccount) :
    (runReceiptAction c onlyAction isLast (.functionCall method args gas deposit)).Funded c.cfg c.action.gasPrice deposit := by
  unfold runReceiptAction
  apply funded_bind_left_zero (funded_fee _ _ _ _)
  intro _
  apply funded_bind_left_zero (funded_checkReceiptAction _ _ _)
  intro _
  exact funded_functionCall c method args gas deposit isLast hreceiver

/-- Native action randomness changes no ledger parameters. A missing exact
context cannot produce a successful step and therefore publishes no funding result. -/
theorem funded_runReceiptActionAt_functionCall (c : ReceiptCtx) (onlyAction isLast : Bool)
    (method : String) (args : Bytes) (gas deposit index : Nat) (hreceiver : c.receipt.receiverId ≠ systemAccount) :
    (runReceiptActionAt c onlyAction isLast (.functionCall method args gas deposit) index).Funded
      c.cfg c.action.gasPrice deposit := by
  cases he : actionRandomSeed c index <;> simp only [runReceiptActionAt, he]
  · intro before after value _ hrun
    have hbad := congrArg Prod.fst hrun
    cases hbad
  · exact funded_runReceiptAction_functionCall _ onlyAction isLast method args gas deposit hreceiver

/-- Failure-index bookkeeping changes no account, gas or receipt funds. -/
theorem funded_failureIndex (cfg : RuntimeConfig) (price : Nat) (index : Option Nat) :
    (modify fun e : Exec => { e with failureIndex := index } : ExecM Unit).Funded cfg price 0 := by
  intro before after value hwf hrun
  have he := congrArg Prod.snd hrun
  change { before with failureIndex := index } = after at he
  subst after
  exact ⟨hwf, by simp [Exec.FundingStep, Exec.totalFunds]⟩

theorem funded_runReceiptActionList (c : ReceiptCtx) (onlyAction : Bool) (actions : List Action) (index : Nat)
    (hreceiver : c.receipt.receiverId ≠ systemAccount)
    (h : ∀ action ∈ actions, FunctionCallFundingAction action) :
    (runReceiptActionList c onlyAction actions index).Funded c.cfg c.action.gasPrice (Fees.totalDeposit actions) := by
  induction actions generalizing index with
  | nil => exact funded_pure _ _ _
  | cons action rest ih =>
    have ha := h action (by simp)
    have hr := ih (index + 1) (by intro a hm; exact h a (by simp [hm]))
    cases action <;> try contradiction
    case functionCall method args gas deposit =>
      simpa only [runReceiptActionList, Fees.totalDeposit, List.map_cons, List.sum_cons, Action.deposit] using
        funded_bind_left_zero (funded_failureIndex _ _ (some index)) (fun _ =>
          (funded_runReceiptActionAt_functionCall c onlyAction rest.isEmpty method args gas deposit index hreceiver).bind (fun _ => hr))

theorem funded_receiptActionBody (c : ReceiptCtx) (hreceiver : c.receipt.receiverId ≠ systemAccount)
    (h : ∀ action ∈ c.action.actions, FunctionCallFundingAction action) :
    (receiptActionBody c).Funded c.cfg c.action.gasPrice (Fees.totalDeposit c.action.actions) := by
  unfold receiptActionBody
  apply funded_bind_left_zero (funded_fee _ _ _ _)
  intro _
  exact funded_bind_right_zero (funded_runReceiptActionList c _ _ 0 hreceiver h)
    (fun _ => funded_bind_zero (funded_failureIndex _ _ none) (fun _ => funded_checkStorageStake _ _ _))

/-- The actual successful action attempt, including all receipt/action fees and
storage-staking checks, obeys the funding law for function-call action lists. -/
theorem runReceiptActions_success_funded (c : ReceiptCtx) (st : ChainState)
    (hwf : st.AccountsUnique) (hreceiver : c.receipt.receiverId ≠ systemAccount)
    (hactions : ∀ action ∈ c.action.actions, FunctionCallFundingAction action)
    (hsuccess : (runReceiptActions c st).2 = none) :
    let raw := (runReceiptActions c st).1
    raw.state.AccountsUnique ∧
      raw.totalFunds c.cfg + raw.gasBurnt * c.action.gasPrice =
        st.totalBalance + Fees.totalDeposit c.action.actions + raw.subsidizedAmount + raw.gasUsed * c.action.gasPrice := by
  cases hr : (receiptActionBody c).run.run { state := st, actorId := c.receipt.predecessorId } with
  | mk result raw =>
    cases result with
    | error error => simp [runReceiptActions, hr] at hsuccess
    | ok value =>
      have hf := funded_receiptActionBody c hreceiver hactions
        { state := st, actorId := c.receipt.predecessorId } raw value hwf hr
      simpa [runReceiptActions, hr, Exec.FundingStep, Exec.totalFunds, receiptsFunds] using hf

end Near
