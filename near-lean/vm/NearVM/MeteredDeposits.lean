import NearVM.HostDeposits

namespace Wasm

def NearState.liquidFunds (ns : NearState) : Nat := ns.context.accountBalance + Near.promisesDeposits ns.promises

end Wasm

namespace Wasm.Near

def fundingState (ns : NearState) : Nat × Nat := (ns.liquidFunds, ns.subsidizedAmount)

def HostResultFunded (before : NearState) : HostResult NearState → Prop
  | .Return _ after => after.host.liquidFunds + before.subsidizedAmount = before.liquidFunds + after.host.subsidizedAmount
  | .Trap .. | .Throw .. => True

def HostPreservesFunding (fn : HostFn NearState) : Prop := ∀ st args, HostResultFunded st.host (fn.invoke st args)

theorem applyCharge_fundingState (ns : NearState) (charge : Charge) :
    fundingState (applyCharge ns charge).1 = fundingState ns := by
  cases charge <;> rfl

theorem applyCharges_fundingState (ns : NearState) (charges : List Charge) :
    fundingState (applyCharges ns charges).1 = fundingState ns := by
  induction charges generalizing ns with
  | nil => rfl
  | cons charge rest ih =>
    cases hc : applyCharge ns charge with
    | mk paid error =>
      have hp := applyCharge_fundingState ns charge
      rw [hc] at hp
      cases error with
      | none => simpa only [applyCharges, hc] using (ih paid).trans hp
      | some error => simpa only [applyCharges, hc] using hp

theorem updateStorageUsage_fundingState (extra : Nat) (name : String) (before after : Store NearState)
    (args : List Value) : fundingState (updateStorageUsage extra name before after args).host = fundingState after.host := by
  unfold updateStorageUsage
  repeat (first | rfl | (dsimp only; split))
  all_goals first | rfl | (split <;> rfl)

@[simp] theorem deductDeposit_promises (name : String) (before after : Store NearState) (args : List Value) :
    (deductDeposit name before after args).1.host.promises = after.host.promises := by
  unfold deductDeposit
  dsimp only
  split
  · rfl
  · exact deductPromiseDeposit_promises _ _ _
  · rfl

theorem deductDeposit_funding (name : String) (before after : Store NearState) (args : List Value)
    (hpaid : (deductDeposit name before after args).2 = none) :
    let paid := (deductDeposit name before after args).1.host
    paid.liquidFunds + after.host.subsidizedAmount + (promiseDeposit? name before args).getD 0 =
      after.host.liquidFunds + paid.subsidizedAmount := by
  have hp := deductDeposit_accounting name before after args hpaid
  dsimp only at hp ⊢
  unfold NearState.liquidFunds
  rw [deductDeposit_promises]
  omega

/-- Post-call metering, successful deposit charging and storage usage preserve
liquid funds plus promise deposits, with minted subsidies explicit. -/
theorem finishMeteredCall_funding (extra : Nat) (name : String) (before : Store NearState)
    (args : List Value) (result : HostResult NearState)
    (hraw : HostResultCreatesDeposits before.host ((promiseDeposit? name before args).getD 0) result) :
    HostResultFunded before.host (finishMeteredCall extra name before args result) := by
  cases result with
  | Trap st message => trivial
  | Throw st tag values => trivial
  | Return values st =>
    change DepositEffect before.host st.host _ at hraw
    have hr : st.host.liquidFunds = before.host.liquidFunds + (promiseDeposit? name before args).getD 0 := by
      simp only [NearState.liquidFunds, hraw.1, hraw.2.2, Nat.add_assoc]
    unfold finishMeteredCall
    dsimp only
    cases hc : applyCharges st.host (chargesAfter name before st args) with
    | mk ns error =>
      have hp := applyCharges_fundingState st.host (chargesAfter name before st args)
      rw [hc] at hp
      have hfund := congrArg Prod.fst hp
      have hsub := congrArg Prod.snd hp
      change ns.liquidFunds = st.host.liquidFunds at hfund
      change ns.subsidizedAmount = st.host.subsidizedAmount at hsub
      cases error with
      | some error => trivial
      | none =>
        cases hd : deductDeposit name before { st with host := ns } args with
        | mk paid error =>
          cases error with
          | some error => trivial
          | none =>
            have hpay := deductDeposit_funding name before { st with host := ns } args (by rw [hd])
            rw [hd] at hpay
            dsimp only at hpay
            have hf := updateStorageUsage_fundingState extra name before paid args
            have hfinal := congrArg Prod.fst hf
            have hsfinal := congrArg Prod.snd hf
            change (updateStorageUsage extra name before paid args).host.liquidFunds = paid.host.liquidFunds at hfinal
            change (updateStorageUsage extra name before paid args).host.subsidizedAmount = paid.host.subsidizedAmount at hsfinal
            change (updateStorageUsage extra name before paid args).host.liquidFunds + before.host.subsidizedAmount =
              before.host.liquidFunds + (updateStorageUsage extra name before paid args).host.subsidizedAmount
            rw [hfinal, hsfinal]
            have hs := hraw.2.1
            omega

/-- The real metered wrapper preserves funded promise obligations on every
successful host return, not just the standalone deposit arithmetic helper. -/
theorem metered_funding (extra : Nat) (name : String) (fn : HostFn NearState)
    (hfn : HostCreatesDeposits name fn) : HostPreservesFunding (metered extra name fn) := by
  intro st args
  unfold metered
  dsimp only
  split
  · trivial
  · split
    · trivial
    · let ns := (applyCharges st.host (chargesBefore name st args)).1
      let st1 : Store NearState := { st with host := { ns with context := { ns.context with usedGas := UInt64.ofNat ns.gas.used } } }
      have hp : fundingState st1.host = fundingState st.host := applyCharges_fundingState _ _
      cases he : (applyCharges st.host (chargesBefore name st args)).2 with
      | some error => trivial
      | none =>
        cases herr : preInvokeError name st1 args with
        | some error => trivial
        | none =>
          have hfinal := finishMeteredCall_funding extra name st1 args _ (hfn st1 args)
          cases hf : finishMeteredCall extra name st1 args (fn.invoke st1 args) with
          | Trap paid message => trivial
          | Throw paid tag values => trivial
          | Return values paid =>
            rw [hf] at hfinal
            change paid.host.liquidFunds + st1.host.subsidizedAmount = st1.host.liquidFunds + paid.host.subsidizedAmount at hfinal
            have hfund := congrArg Prod.fst hp
            have hsub := congrArg Prod.snd hp
            change st1.host.liquidFunds = st.host.liquidFunds at hfund
            change st1.host.subsidizedAmount = st.host.subsidizedAmount at hsub
            change paid.host.liquidFunds + st.host.subsidizedAmount = st.host.liquidFunds + paid.host.subsidizedAmount
            simpa only [hfund, hsub] using hfinal

theorem meteredTransfer_funding (extra : Nat) :
    HostPreservesFunding (metered extra "promise_batch_action_transfer" promiseBatchActionTransferFn) :=
  metered_funding _ _ _ promiseBatchActionTransferFn_deposits

theorem meteredBatchCall_funding (extra : Nat) :
    HostPreservesFunding (metered extra "promise_batch_action_function_call" promiseBatchActionFunctionCallFn) :=
  metered_funding _ _ _ promiseBatchActionFunctionCallFn_deposits

theorem meteredCreate_funding (extra : Nat) : HostPreservesFunding (metered extra "promise_create" promiseCreateFn) :=
  metered_funding _ _ _ promiseCreateFn_deposits

theorem meteredThen_funding (extra : Nat) : HostPreservesFunding (metered extra "promise_then" promiseThenFn) :=
  metered_funding _ _ _ promiseThenFn_deposits

end Wasm.Near
