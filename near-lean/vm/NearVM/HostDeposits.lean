import NearVM.PromiseAccounting

namespace Wasm.Near

/-- Raw host calls append obligations; the metered wrapper charges them. -/
def DepositEffect (before after : NearState) (amount : Nat) : Prop :=
  after.context.accountBalance = before.context.accountBalance ∧
  after.subsidizedAmount = before.subsidizedAmount ∧
  promisesDeposits after.promises = promisesDeposits before.promises + amount

def HostResultCreatesDeposits (before : NearState) (amount : Nat) : HostResult NearState → Prop
  | .Return _ after => DepositEffect before after.host amount
  | .Trap .. | .Throw .. => True

def HostCreatesDeposits (name : String) (fn : HostFn NearState) : Prop :=
  ∀ st args, HostResultCreatesDeposits st.host ((promiseDeposit? name st args).getD 0) (fn.invoke st args)

theorem appendPromise_return_deposits (st : Store NearState) (promise : NearPromise) (values : List Value) :
    HostResultCreatesDeposits st.host (promiseValue depositValue promise) (.Return values (appendPromise st promise)) :=
  ⟨rfl, rfl, appendPromise_deposits st promise⟩

theorem appendPromiseActionResult_deposits (name : String) (st : Store NearState) (index : UInt64)
    (action : PromiseAction) :
    HostResultCreatesDeposits st.host action.deposit (appendPromiseActionResult name st index action) := by
  unfold appendPromiseActionResult
  split
  · exact ⟨rfl, rfl, appendPromiseAction_deposits _ _ _ _ (by assumption)⟩
  · trivial

/-- Successful parsing records the exact u128 amount read from guest memory. -/
theorem readFunctionCallAction_deposit (st : Store NearState)
    (methodLen methodPtr argsLen argsPtr amountPtr gas : UInt64) (action : PromiseAction)
    (h : readFunctionCallAction? st methodLen methodPtr argsLen argsPtr amountPtr gas = some action) :
    action.deposit = (readU128Mem st amountPtr).getD 0 := by
  unfold readFunctionCallAction? at h
  obtain ⟨method, hm, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨args, ha, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨amount, hd, h⟩ := Option.bind_eq_some_iff.mp h
  have he := Option.some.inj h
  subst action
  simp [PromiseAction.deposit, hd]

theorem promiseDeposit_transfer (st : Store NearState) (index ptr : UInt64) :
    promiseDeposit? "promise_batch_action_transfer" st [.i64 index, .i64 ptr] = readU128Mem st ptr := rfl

theorem promiseDeposit_batchCall (st : Store NearState) (index ml mp al ap amount gas : UInt64) :
    promiseDeposit? "promise_batch_action_function_call" st
      [.i64 index, .i64 ml, .i64 mp, .i64 al, .i64 ap, .i64 amount, .i64 gas] = readU128Mem st amount := rfl

theorem promiseDeposit_create (st : Store NearState) (nl np ml mp al ap amount gas : UInt64) :
    promiseDeposit? "promise_create" st [.i64 nl, .i64 np, .i64 ml, .i64 mp, .i64 al, .i64 ap, .i64 amount, .i64 gas] =
      readU128Mem st amount := rfl

theorem promiseDeposit_then (st : Store NearState) (base nl np ml mp al ap amount gas : UInt64) :
    promiseDeposit? "promise_then" st
      [.i64 base, .i64 nl, .i64 np, .i64 ml, .i64 mp, .i64 al, .i64 ap, .i64 amount, .i64 gas] =
      readU128Mem st amount := rfl

theorem promiseBatchActionTransferFn_deposits :
    HostCreatesDeposits "promise_batch_action_transfer" promiseBatchActionTransferFn := by
  intro st args
  unfold promiseBatchActionTransferFn
  dsimp only [disallowInView]
  split
  · trivial
  · split
    · rename_i index amountPtr
      rw [promiseDeposit_transfer]
      split
      · rename_i amount hread
        simpa only [hread, Option.getD_some, PromiseAction.deposit] using
          appendPromiseActionResult_deposits "promise_batch_action_transfer" st index (.transfer amount)
      · trivial
    · trivial

theorem promiseBatchActionFunctionCallFn_deposits :
    HostCreatesDeposits "promise_batch_action_function_call" promiseBatchActionFunctionCallFn := by
  intro st args
  unfold promiseBatchActionFunctionCallFn
  dsimp only [disallowInView]
  split
  · trivial
  · split
    · rename_i index methodLen methodPtr argsLen argsPtr amountPtr gas
      rw [promiseDeposit_batchCall]
      split
      · rename_i action hread
        have hd := readFunctionCallAction_deposit st methodLen methodPtr argsLen argsPtr amountPtr gas action hread
        rw [← hd]
        exact appendPromiseActionResult_deposits _ _ _ _
      · trivial
    · trivial

theorem promiseCreateFn_deposits : HostCreatesDeposits "promise_create" promiseCreateFn := by
  intro st args
  unfold promiseCreateFn
  dsimp only [disallowInView]
  split
  · trivial
  · split
    · rename_i accountLen accountPtr methodLen methodPtr argsLen argsPtr amountPtr gas
      rw [promiseDeposit_create]
      split
      · rename_i account action haccount hread
        have hd := readFunctionCallAction_deposit st methodLen methodPtr argsLen argsPtr amountPtr gas action hread
        unfold checkAccountId
        split
        · simpa [promiseValue, depositValue, hd] using
            appendPromise_return_deposits st (.batch account [action]) [Value.i64 (nextPromiseIdx st)]
        · trivial
      · trivial
    · trivial

theorem promiseThenFn_deposits : HostCreatesDeposits "promise_then" promiseThenFn := by
  intro st args
  unfold promiseThenFn
  dsimp only [disallowInView]
  split
  · trivial
  · split
    · rename_i base accountLen accountPtr methodLen methodPtr argsLen argsPtr amountPtr gas
      rw [promiseDeposit_then]
      split
      · rename_i account action haccount hread
        have hd := readFunctionCallAction_deposit st methodLen methodPtr argsLen argsPtr amountPtr gas action hread
        split
        · unfold checkAccountId
          split
          · simpa [promiseValue, depositValue, hd] using
              appendPromise_return_deposits st (.callback base.toNat account [action]) [Value.i64 (nextPromiseIdx st)]
          · trivial
        · trivial
      · trivial
    · trivial

end Wasm.Near
