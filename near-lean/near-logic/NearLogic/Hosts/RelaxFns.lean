import NearLogic.Hosts.FinishRelax
import NearLogic.RelaxStep

/-!
# Host functions under raised gas limits

For every host function wNEAR imports (`gasNames`), the charges before a
call and the argument check do not look at the gas limits
(`chargesBefore_relax`, `preInvokeError_relax`; each name is checked by
evaluation). So such a metered host respects raised limits (`RelaxFn`) as
soon as its call does (`relaxFn_metered`), and, for a host that is not a
storage operation, as soon as its functional part commutes with raising the
limits and keeps them (`relaxFn_plain`).
-/

namespace NearLogic

open Wasm Wasm.Near

/-- The host functions wNEAR imports. -/
def gasNames : List String :=
  ["read_register", "register_len", "current_account_id", "signer_account_id",
   "signer_account_pk", "predecessor_account_id", "input", "block_index", "block_timestamp",
   "epoch_height", "storage_usage", "account_balance", "account_locked_balance",
   "attached_deposit", "prepaid_gas", "used_gas", "random_seed", "sha256", "keccak256",
   "keccak512", "value_return", "panic", "panic_utf8", "log_utf8", "log_utf16", "promise_create",
   "promise_then", "promise_and", "promise_batch_create", "promise_batch_then",
   "promise_batch_action_create_account", "promise_batch_action_deploy_contract",
   "promise_batch_action_function_call", "promise_batch_action_transfer",
   "promise_batch_action_stake", "promise_batch_action_add_key_with_full_access",
   "promise_batch_action_add_key_with_function_call", "promise_batch_action_delete_key",
   "promise_batch_action_delete_account", "promise_results_count", "promise_result",
   "promise_return", "storage_write", "storage_read", "storage_remove", "storage_has_key",
   "validator_stake", "validator_total_stake"]

theorem scanNulBytes_relax (st : HostStore NearState) (p m ptr maxLen : Nat) :
    ∀ fuel i acc, scanNulBytes (relaxSt st p m) ptr maxLen fuel i acc = scanNulBytes st ptr maxLen fuel i acc
  | 0, _, _ => rfl
  | fuel + 1, i, acc => by
    simp only [scanNulBytes]
    rw [scanNulBytes_relax st p m ptr maxLen fuel]
    rfl

theorem scanNulUnits_relax (st : HostStore NearState) (p m ptr maxLen : Nat) :
    ∀ fuel len, scanNulUnits (relaxSt st p m) ptr maxLen fuel len = scanNulUnits st ptr maxLen fuel len
  | 0, _ => rfl
  | fuel + 1, len => by
    simp only [scanNulUnits]
    rw [scanNulUnits_relax st p m ptr maxLen fuel]
    rfl

theorem readU64Array_relax (st : HostStore NearState) (p m : Nat) (ptr : UInt64) :
    ∀ n, readU64Array (relaxSt st p m) ptr n = readU64Array st ptr n
  | 0 => rfl
  | n + 1 => by
    simp only [readU64Array]
    rw [readU64Array_relax st p m ptr n]
    rfl

theorem depsSir_go_relax (st : HostStore NearState) (p m idx : Nat) (r : Option (List UInt8)) :
    ∀ fuel i, depsSir.go (relaxSt st p m) r fuel i = depsSir.go st r fuel i
  | 0, _ => rfl
  | fuel + 1, i => by
    simp only [depsSir.go]
    have hp : (relaxSt st p m).host.promises = st.host.promises := rfl
    rw [hp]
    cases getPromise? st.host.promises i with
    | none => rfl
    | some x =>
      have hg : depsSir.go (relaxSt st p m) r fuel = depsSir.go st r fuel :=
        funext (depsSir_go_relax st p m idx r fuel)
      cases x <;> simp only [hg] <;> rfl

theorem depsSir_relax (st : HostStore NearState) (p m idx : Nat) (r : Option (List UInt8)) :
    depsSir (relaxSt st p m) idx r = depsSir st idx r := by
  unfold depsSir
  rw [depsSir_go_relax st p m idx r]
  rfl

theorem promiseJoinError_relax (st : HostStore NearState) (args : List Value) (p m : Nat) :
    promiseJoinError (relaxSt st p m) args = promiseJoinError st args := by
  unfold promiseJoinError
  split
  · simp only [readU64Array_relax]; rfl
  · rfl

theorem creationAccountError_relax (name : String) (st : HostStore NearState) (args : List Value) (p m : Nat) :
    creationAccountError name (relaxSt st p m) args = creationAccountError name st args := by
  unfold creationAccountError
  simp only [getMemOrReg_relaxSt]
  rfl

theorem creationPrefixError_relax (name : String) (st : HostStore NearState) (args : List Value) (p m : Nat) :
    creationPrefixError name (relaxSt st p m) args = creationPrefixError name st args := by
  unfold creationPrefixError
  rw [creationAccountError_relax]
  rfl

theorem stringHostRead_relax (name : String) (hn : name ≠ "abort") (st : HostStore NearState) (args : List Value) (p m : Nat) :
    stringHostRead? name (relaxSt st p m) args = stringHostRead? name st args := by
  unfold stringHostRead?
  split
  · simp only [logUtf8Read, readUtf8String, scanNulBytes_relax]; rfl
  · simp only [logUtf16Read, readUtf16String, scanNulUnits_relax]; rfl
  · simp only [panicUtf8Read, readUtf8String, scanNulBytes_relax]; rfl
  · exact absurd rfl hn
  · rfl

theorem startsWith_logs : "log_utf8".startsWith "promise_batch_action_" = false ∧
    "log_utf16".startsWith "promise_batch_action_" = false ∧
    "panic_utf8".startsWith "promise_batch_action_" = false := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem chargesBefore_relax {name : String} (hn : name ∈ gasNames) (st : HostStore NearState)
    (args : List Value) (p m : Nat) :
    chargesBefore name (relaxSt st p m) args = chargesBefore name st args := by
  simp only [gasNames, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
    | (simp only [relaxSt, relax, chargesBefore, chargesBeforeUnvalidated, storageMutationPlan?, creationAccountArgs]; rfl)
    | (simp (config := { decide := true }) only [relaxSt, relax, chargesBefore, chargesBeforeUnvalidated, storageMutationPlan?,
        creationAccountArgs, ↓reduceIte, String.reduceBEq, String.reduceBNe, Bool.false_and, Bool.and_false,
        Bool.false_or, Bool.or_false, startsWith_logs.1, startsWith_logs.2.1, startsWith_logs.2.2]; rfl)
    | (simp (config := { decide := true }) only [chargesBefore, chargesBeforeUnvalidated, preInvokeError,
        invocationArgumentError, storageMutationPlan?, creationAccountArgs, ↓reduceIte, String.reduceBEq,
        String.reduceBNe, Bool.false_and, Bool.and_false, Bool.false_or, Bool.or_false, startsWith_logs.1,
        startsWith_logs.2.1, startsWith_logs.2.2, stringHostRead_relax, creationAccountError_relax,
        creationPrefixError_relax, depsSir_relax, promiseJoinError_relax]) <;> rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem preInvokeError_relax {name : String} (hn : name ∈ gasNames) (st : HostStore NearState)
    (args : List Value) (p m : Nat) :
    preInvokeError name (relaxSt st p m) args = preInvokeError name st args := by
  simp only [gasNames, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
    | (simp only [relaxSt, relax, preInvokeError, invocationArgumentError, storageMutationPlan?, creationAccountArgs]; rfl)
    | (simp (config := { decide := true }) only [relaxSt, relax, preInvokeError, invocationArgumentError, storageMutationPlan?,
        creationAccountArgs, ↓reduceIte, String.reduceBEq, String.reduceBNe, Bool.false_and, Bool.and_false,
        Bool.false_or, Bool.or_false, startsWith_logs.1, startsWith_logs.2.1, startsWith_logs.2.2]; rfl)
    | (simp (config := { decide := true }) only [chargesBefore, chargesBeforeUnvalidated, preInvokeError,
        invocationArgumentError, storageMutationPlan?, creationAccountArgs, ↓reduceIte, String.reduceBEq,
        String.reduceBNe, Bool.false_and, Bool.and_false, Bool.false_or, Bool.or_false, startsWith_logs.1,
        startsWith_logs.2.1, startsWith_logs.2.2, stringHostRead_relax, creationAccountError_relax,
        creationPrefixError_relax, depsSir_relax, promiseJoinError_relax]) <;> rfl

/-- A metered host of `gasNames` respects raised limits when its call does. -/
theorem relaxFn_metered (extra : Nat) {name : String} (hn : name ∈ gasNames) (fn : NearHostFn NearState)
    (hinv : InvokeRelax extra name fn) : RelaxFn (metered extra name fn).toHostFn := by
  intro host mem args p m hp hm
  rcases metered_relax extra name fn (fun st args p m => chargesBefore_relax hn st args p m)
    (fun st args p m => preInvokeError_relax hn st args p m) hinv
    { mem := mem.getD (Memory.new 0 none), host } args p m hp hm with ⟨st', e, hinv', he⟩ | hrel
  · left
    refine ⟨.host e.message, { st'.host with lastError := some e }, some st'.mem, e, ?_, rfl, he⟩
    simp only [NearHostFn.toHostFn, hinv', trapWith]
  · right
    simp only [NearHostFn.toHostFn]
    have : ({ mem := mem.getD (Memory.new 0 none), host := relax host p m } : HostStore NearState) =
        relaxSt { mem := mem.getD (Memory.new 0 none), host } p m := rfl
    rw [this, hrel]
    cases (metered extra name fn).invoke { mem := mem.getD (Memory.new 0 none), host } args <;> rfl

/-- A metered host of `gasNames` that is not a storage operation respects
raised limits when its functional part commutes with raising them and keeps
them. -/
theorem relaxFn_plain (extra : Nat) {name : String} (hn : name ∈ gasNames) (fn : NearHostFn NearState)
    (hns : ["storage_read", "storage_has_key", "storage_write", "storage_remove"].contains name = false)
    (hfn : ∀ st args p m, fn.invoke (relaxSt st p m) args = (fn.invoke st args).relax p m)
    (hkeep : ∀ st args vals st2, fn.invoke st args = .Return vals st2 →
      st2.host.gas.prepaid = st.host.gas.prepaid ∧ st2.host.gas.maxBurnt = st.host.gas.maxBurnt) :
    RelaxFn (metered extra name fn).toHostFn :=
  relaxFn_metered extra hn fn (invokeRelax_plain extra name fn hns hfn hkeep)

end NearLogic
