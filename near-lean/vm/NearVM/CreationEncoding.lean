import NearVM.PromiseEncoding
import NearVM.ActionMethodValidation
import NearVM.MeteredBatchReservations

namespace Wasm.Near

/-- Receiver decoding is established by the actual creation guard, before
receipt allocation or function-call action validation. -/
theorem creationAccountError_none_utf8 (name : String) (st : HostStore NearState) (args : List Value)
    (len ptr : UInt64) (receiver : List UInt8)
    (hargs : creationAccountArgs name args = some (len, ptr))
    (hread : getMemOrReg st ptr len = some receiver)
    (hguard : creationAccountError name st args = none) :
    (String.fromUTF8? ⟨receiver.toArray⟩).isSome = true := by
  cases he : String.fromUTF8? ⟨receiver.toArray⟩ with
  | none => simp [creationAccountError, hargs, hread, he] at hguard
  | some decoded => rfl

/-- The action decoder preserves the exact method witness accepted by the
metered runtime external. No assumption about the decoded action's gas is used. -/
theorem readFunctionCallAction_encoding (name : String) (st : HostStore NearState) (args : List Value)
    (ml mp al ap amount gas : UInt64) (action : PromiseAction)
    (hpolicy : st.host.config.validateActionMethodUtf8 = true)
    (hguard : actionMethodEncodingError name st args = none)
    (hmethod : actionMethodBytes? name st args = getMemOrReg st mp ml)
    (hread : readFunctionCallAction? st ml mp al ap amount gas = some action) : ActionMethodsUtf8 action := by
  unfold readFunctionCallAction? at hread
  obtain ⟨method, hm, hread⟩ := Option.bind_eq_some_iff.mp hread
  obtain ⟨arguments, _, hread⟩ := Option.bind_eq_some_iff.mp hread
  obtain ⟨deposit, _, hread⟩ := Option.bind_eq_some_iff.mp hread
  have he := Option.some.inj hread
  subst action
  obtain ⟨decoded, hd⟩ := actionMethodEncodingError_none_utf8 name st args method hpolicy (hmethod.trans hm) hguard
  simp [ActionMethodsUtf8, hd]

/-- Appending a newly validated receipt retains every previous encoding witness. -/
theorem appendPromise_encoding (st : HostStore NearState) (promise : NearPromise)
    (h : PromisesEncoding st.host.promises) (hp : PromiseSatisfies ReceiptEncoding promise) :
    PromisesEncoding (appendPromise st promise).host.promises := by
  intro p hm
  rcases List.mem_append.mp hm with hm | hm
  · exact h p hm
  · have he := List.mem_singleton.mp hm
    subst p
    exact hp

/-- Raw creators consume the actual pre-call receiver and post-call method
validation facts. These conditions are supplied by successful metered calls. -/
def HostCreatesEncoding (name : String) (fn : NearHostFn NearState) : Prop :=
  ∀ st args, PromisesEncoding st.host.promises →
    st.host.config.validateActionMethodUtf8 = true →
    creationAccountError name st args = none →
    actionMethodEncodingError name st args = none →
    HostResult.LiveSatisfies (fun ns => PromisesEncoding ns.promises) (fn.invoke st args)

theorem promiseBatchCreateFn_encoding : HostCreatesEncoding "promise_batch_create" promiseBatchCreateFn := by
  intro st args h _ haccount _
  unfold promiseBatchCreateFn
  dsimp only [disallowInView, createBatchPromiseResult, createCallbackPromiseResult, checkAccountId]
  repeat' (first
    | trivial
    | (apply appendPromise_encoding _ _ h
       refine ⟨?_, by simp⟩
       apply creationAccountError_none_utf8 _ _ _ _ _ _ ?_ (by assumption) haccount
       simp [creationAccountArgs, argU64])
    | split)

theorem promiseBatchThenFn_encoding : HostCreatesEncoding "promise_batch_then" promiseBatchThenFn := by
  intro st args h _ haccount _
  unfold promiseBatchThenFn
  dsimp only [disallowInView, createBatchPromiseResult, createCallbackPromiseResult, checkAccountId]
  repeat' (first
    | trivial
    | (apply appendPromise_encoding _ _ h
       refine ⟨?_, by simp⟩
       apply creationAccountError_none_utf8 _ _ _ _ _ _ ?_ (by assumption) haccount
       simp [creationAccountArgs, argU64])
    | split)

theorem promiseAndFn_encoding : HostCreatesEncoding "promise_and" promiseAndFn := by
  intro st args h _ _ _
  unfold promiseAndFn
  dsimp only [disallowInView]
  repeat' (first | trivial | (apply appendPromise_encoding _ _ h; trivial) | split)

theorem promiseCreateFn_encoding : HostCreatesEncoding "promise_create" promiseCreateFn := by
  intro st args h hpolicy haccount hmethod
  unfold promiseCreateFn
  dsimp only [disallowInView, checkAccountId]
  repeat' (first
    | trivial
    | (apply appendPromise_encoding _ _ h
       refine ⟨?_, ?_⟩
       · apply creationAccountError_none_utf8 _ _ _ _ _ _ ?_ (by assumption) haccount
         simp [creationAccountArgs, argU64]
       · simp only [List.mem_singleton, forall_eq]
         apply readFunctionCallAction_encoding _ _ _ _ _ _ _ _ _ _ hpolicy hmethod ?_ (by assumption)
         simp [actionMethodBytes?, usesKeyMethodFields, functionCallInputs?, functionCallInputs, argU64])
    | split)

theorem promiseThenFn_encoding : HostCreatesEncoding "promise_then" promiseThenFn := by
  intro st args h hpolicy haccount hmethod
  unfold promiseThenFn
  dsimp only [disallowInView, checkAccountId]
  repeat' (first
    | trivial
    | (apply appendPromise_encoding _ _ h
       refine ⟨?_, ?_⟩
       · apply creationAccountError_none_utf8 _ _ _ _ _ _ ?_ (by assumption) haccount
         simp [creationAccountArgs, argU64]
       · simp only [List.mem_singleton, forall_eq]
         apply readFunctionCallAction_encoding _ _ _ _ _ _ _ _ _ _ hpolicy hmethod ?_ (by assumption)
         simp [actionMethodBytes?, usesKeyMethodFields, functionCallInputs?, functionCallInputs, argU64])
    | split)


end Wasm.Near
