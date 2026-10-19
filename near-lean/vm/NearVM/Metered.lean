import NearVM.Host
import NearVM.Config

/-!
# Gas-metered host functions

The host functions in `NearVM.Host` are functional. This module wraps each
of them with the gas it costs in nearcore (`near_vm_runner::logic::logic.rs`):
a charge computed from the arguments before the call, and a charge computed
from its effect after it (bytes returned through a register, evicted storage
values). It also keeps `storage_usage` in step with storage writes and turns
`panic`/`panic_utf8` into structured `guestPanic` errors carrying the message.

Costs that depend on the state trie (`touching_trie_node`,
`read_cached_trie_node`) are not charged: they need the trie shape, which
the runtime does not model. Replay comparisons of burnt gas on storage-heavy
calls must account for that.
-/

namespace Wasm.Near

/-- One gas charge. -/
inductive Charge
  /-- `times` × the named `ExtCosts` entry, burnt. -/
  | ext (name : String) (times : Nat := 1)
  | burn (gas : Nat)
  /-- `pay_action_base`. -/
  | actionBase (fee : ActionFees → Fee) (sir : Bool)
  /-- `pay_action_per_byte`. -/
  | actionBytes (fee : ActionFees → Fee) (n : Nat) (sir : Bool)
  /-- `pay_gas_for_new_receipt`: one action receipt plus one data receipt per dependency. -/
  | newReceipt (sir : Bool) (depsSir : List Bool)
  /-- `prepay_gas`: gas attached to a function call action. -/
  | prepay (gas : Nat)

def applyCharge (ns : NearState) : Charge → NearState × Option HostError
  | .ext name times =>
    let (g, e) := ns.gas.burn (ns.extCosts.cost name * times)
    ({ ns with gas := g, gasProfile := ns.gasProfile.addExt name (g.burnt - ns.gas.burnt) }, e)
  | .burn n =>
    let (g, e) := ns.gas.burn n
    ({ ns with gas := g, gasProfile := { ns.gasProfile with
      actionBurnt := ns.gasProfile.actionBurnt + (g.burnt - ns.gas.burnt) } }, e)
  | .actionBase fee sir =>
    let f := fee ns.fees
    let (g, e) := ns.gas.payAction (f.send sir) f.execution
    ({ ns with gas := g, gasProfile := { ns.gasProfile with
      actionBurnt := ns.gasProfile.actionBurnt + (g.burnt - ns.gas.burnt) } }, e)
  | .actionBytes fee n sir =>
    let f := fee ns.fees
    let (g, e) := ns.gas.payAction (f.send sir * n) (f.execution * n)
    ({ ns with gas := g, gasProfile := { ns.gasProfile with
      actionBurnt := ns.gasProfile.actionBurnt + (g.burnt - ns.gas.burnt) } }, e)
  | .newReceipt sir depsSir =>
    let a := ns.fees.newActionReceipt
    let d := ns.fees.newDataReceiptBase
    -- Both sending and executing dependency data receipts are burnt here,
    -- rather than reserving their execution fee for the callback runtime.
    let burn := a.send sir + (depsSir.map fun s => d.send s + d.execution).sum
    let use := a.execution
    let (g, e) := ns.gas.payAction burn use
    ({ ns with gas := g, gasProfile := { ns.gasProfile with
      actionBurnt := ns.gasProfile.actionBurnt + (g.burnt - ns.gas.burnt) } }, e)
  | .prepay n =>
    let (g, e) := ns.gas.prepay n
    ({ ns with gas := g }, e)

def applyCharges (ns : NearState) : List Charge → NearState × Option HostError
  | [] => (ns, none)
  | c :: cs =>
    match applyCharge ns c with
    | (ns', none) => applyCharges ns' cs
    | (ns', some e) => (ns', some e)

/-- Trap with a structured error recorded in the host state. -/
def trapWith (st : Store NearState) (e : HostError) : HostResult NearState :=
  .Trap { st with host := { st.host with lastError := some e } } e.message

/-! ## Cost rules -/

def argU64 (args : List Value) (i : Nat) : UInt64 :=
  match args[i]? with
  | some (.i64 n) => n
  | _ => 0

/-- Bytes of a `(len, ptr)` argument following `get_memory_or_register`. -/
def spanLen (st : Store NearState) (len ptr : UInt64) : Nat :=
  if len = u64Max then ((st.host.registers ptr.toNat).map List.length).getD 0 else len.toNat

/-- Reading a `(len, ptr)` argument: memory or register costs. -/
def readSpan (st : Store NearState) (len ptr : UInt64) : List Charge :=
  if len = u64Max then
    [.ext "read_register_base", .ext "read_register_byte" (spanLen st len ptr)]
  else [.ext "read_memory_base", .ext "read_memory_byte" len.toNat]

def readMem (n : Nat) : List Charge := [.ext "read_memory_base", .ext "read_memory_byte" n]
def writeMem (n : Nat) : List Charge := [.ext "write_memory_base", .ext "write_memory_byte" n]
def writeReg (n : Nat) : List Charge := [.ext "write_register_base", .ext "write_register_byte" n]
def utf8 (n : Nat) : List Charge := [.ext "utf8_decoding_base", .ext "utf8_decoding_byte" n]
def utf16 (n : Nat) : List Charge := [.ext "utf16_decoding_base", .ext "utf16_decoding_byte" n]

/-- Receiver of promise `idx`, if it is a receipt. -/
def promiseReceiver? (st : Store NearState) (idx : Nat) : Option (List UInt8) :=
  match getPromise? st.host.promises idx with
  | some (.batch acct _) => some acct
  | some (.callback _ acct _) => some acct
  | _ => none

/-- Same-shard ("sir") test: the receiver is the current account. -/
def sirOf (st : Store NearState) (acct : Option (List UInt8)) : Bool :=
  acct == some st.host.context.currentAccountId

def sirOfSpan (st : Store NearState) (len ptr : UInt64) : Bool :=
  sirOf st (getMemOrReg st ptr len)

/-- Data routing is same-account when the dependency receiver equals the
callback receiver, which need not be the currently executing account. -/
def depsSir (st : Store NearState) (idx : Nat) (receiver : Option (List UInt8)) : List Bool :=
  let rec go (fuel : Nat) (i : Nat) : List Bool :=
    match fuel with
    | 0 => []
    | fuel + 1 =>
      match getPromise? st.host.promises i with
      | some (.and ds) => ds.flatMap (go fuel)
      | some _ => [promiseReceiver? st i == receiver]
      | none => []
  go st.host.promises.length idx

/-- Argument-dependent charge plan before validating promise handles. -/
private def chargesBeforeUnvalidated (name : String) (st : Store NearState) (args : List Value) : List Charge :=
  let a := argU64 args
  let base : Charge := .ext "base"
  match name with
  | "read_register" =>
    let n := ((st.host.registers (a 0).toNat).map List.length).getD 0
    [base, .ext "read_register_base", .ext "read_register_byte" n] ++ writeMem n
  | "register_len" => [base]
  | "write_register" => [base] ++ readMem (a 1).toNat ++ writeReg (a 1).toNat
  | "current_account_id" => [base] ++ writeReg st.host.context.currentAccountId.length
  | "signer_account_id" => [base] ++ writeReg st.host.context.signerAccountId.length
  | "signer_account_pk" => [base] ++ writeReg st.host.context.signerAccountPk.length
  | "predecessor_account_id" => [base] ++ writeReg st.host.context.predecessorAccountId.length
  -- nearcore shares the input Rc buffer with the register, without a byte copy.
  | "input" => [base, .ext "write_register_base"]
  | "random_seed" => [base] ++ writeReg st.host.randomSeed.length
  | "account_balance" | "account_locked_balance" | "attached_deposit" => [base] ++ writeMem 16
  | "validator_stake" =>
    [base, .ext "validator_stake_base"] ++ readSpan st (a 0) (a 1) ++ utf8 (spanLen st (a 0) (a 1)) ++ writeMem 16
  | "validator_total_stake" => [base, .ext "validator_total_stake_base"] ++ writeMem 16
  | "sha256" =>
    let n := spanLen st (a 0) (a 1)
    [base, .ext "sha256_base", .ext "sha256_byte" n] ++ readSpan st (a 0) (a 1) ++ writeReg 32
  | "keccak256" =>
    let n := spanLen st (a 0) (a 1)
    [base, .ext "keccak256_base", .ext "keccak256_byte" n] ++ readSpan st (a 0) (a 1) ++ writeReg 32
  | "keccak512" =>
    let n := spanLen st (a 0) (a 1)
    [base, .ext "keccak512_base", .ext "keccak512_byte" n] ++ readSpan st (a 0) (a 1) ++ writeReg 64
  | "ripemd160" =>
    let n := spanLen st (a 0) (a 1)
    [base, .ext "ripemd160_base", .ext "ripemd160_block" ((n + 8) / 64 + 1)] ++ readSpan st (a 0) (a 1) ++ writeReg 20
  | "ecrecover" =>
    [base, .ext "ecrecover_base"] ++ readSpan st (a 0) (a 1) ++ readSpan st (a 2) (a 3) ++ writeReg 64
  | "ed25519_verify" =>
    let n := spanLen st (a 2) (a 3)
    [base, .ext "ed25519_verify_base", .ext "ed25519_verify_byte" n] ++ readSpan st (a 0) (a 1)
      ++ readSpan st (a 2) (a 3) ++ readSpan st (a 4) (a 5)
  | "log_utf8" =>
    let n := spanLen st (a 0) (a 1)
    [base] ++ readSpan st (a 0) (a 1) ++ utf8 n ++ [.ext "log_base", .ext "log_byte" n]
  | "log_utf16" =>
    let n := spanLen st (a 0) (a 1)
    [base] ++ readSpan st (a 0) (a 1) ++ utf16 n ++ [.ext "log_base", .ext "log_byte" n]
  | "panic" => [base]
  | "panic_utf8" => [base] ++ readSpan st (a 0) (a 1) ++ utf8 (spanLen st (a 0) (a 1))
  | "abort" => [base]
  | "value_return" =>
    let n := spanLen st (a 0) (a 1)
    let byte := st.host.fees.newDataReceiptByte
    let dataGas := (st.host.outputDataReceivers.map fun r =>
      let sir := r == st.host.context.currentAccountId
      byte.send sir * n + byte.execution * n).sum
    [base] ++ readSpan st (a 0) (a 1) ++ [.burn dataGas]
  | "storage_write" =>
    let k := spanLen st (a 0) (a 1)
    let v := spanLen st (a 2) (a 3)
    [base, .ext "storage_write_base"] ++ readSpan st (a 0) (a 1) ++ readSpan st (a 2) (a 3)
      ++ [.ext "storage_write_key_byte" k, .ext "storage_write_value_byte" v]
  | "storage_read" =>
    let k := spanLen st (a 0) (a 1)
    [base, .ext "storage_read_base"] ++ readSpan st (a 0) (a 1) ++ [.ext "storage_read_key_byte" k]
  | "storage_remove" =>
    let k := spanLen st (a 0) (a 1)
    [base, .ext "storage_remove_base"] ++ readSpan st (a 0) (a 1) ++ [.ext "storage_remove_key_byte" k]
  | "storage_has_key" =>
    let k := spanLen st (a 0) (a 1)
    [base, .ext "storage_has_key_base"] ++ readSpan st (a 0) (a 1) ++ [.ext "storage_has_key_byte" k]
  | "promise_create" =>
    let sir := sirOfSpan st (a 0) (a 1)
    let m := spanLen st (a 2) (a 3)
    let args := spanLen st (a 4) (a 5)
    [base] ++ readSpan st (a 0) (a 1) ++ utf8 (spanLen st (a 0) (a 1)) ++ [.newReceipt sir []]
      ++ readSpan st (a 2) (a 3) ++ readSpan st (a 4) (a 5) ++ readMem 16
      ++ [.actionBase (·.functionCallBase) sir, .actionBytes (·.functionCallByte) (m + args) sir,
          .prepay (a 7).toNat]
  | "promise_then" =>
    let sir := sirOfSpan st (a 1) (a 2)
    let m := spanLen st (a 3) (a 4)
    let args := spanLen st (a 5) (a 6)
    [base] ++ readSpan st (a 1) (a 2) ++ utf8 (spanLen st (a 1) (a 2))
      ++ [.newReceipt sir (depsSir st (a 0).toNat (getMemOrReg st (a 2) (a 1)))]
      ++ readSpan st (a 3) (a 4) ++ readSpan st (a 5) (a 6) ++ readMem 16
      ++ [.actionBase (·.functionCallBase) sir, .actionBytes (·.functionCallByte) (m + args) sir,
          .prepay (a 8).toNat]
  | "promise_and" =>
    let n := (a 1).toNat * 8
    [base, .ext "promise_and_base", .ext "promise_and_per_promise" n] ++ readMem n
  | "promise_batch_create" =>
    [base] ++ readSpan st (a 0) (a 1) ++ utf8 (spanLen st (a 0) (a 1))
      ++ [.newReceipt (sirOfSpan st (a 0) (a 1)) []]
  | "promise_batch_then" =>
    [base] ++ readSpan st (a 1) (a 2) ++ utf8 (spanLen st (a 1) (a 2))
      ++ [.newReceipt (sirOfSpan st (a 1) (a 2)) (depsSir st (a 0).toNat (getMemOrReg st (a 2) (a 1)))]
  | "promise_batch_action_create_account" =>
    [base, .actionBase (·.createAccount) (sirOf st (promiseReceiver? st (a 0).toNat))]
  | "promise_batch_action_deploy_contract" =>
    let sir := sirOf st (promiseReceiver? st (a 0).toNat)
    let n := spanLen st (a 1) (a 2)
    [base] ++ readSpan st (a 1) (a 2)
      ++ [.actionBase (·.deployContractBase) sir, .actionBytes (·.deployContractByte) n sir]
  | "promise_batch_action_function_call" =>
    let sir := sirOf st (promiseReceiver? st (a 0).toNat)
    let m := spanLen st (a 1) (a 2)
    let args := spanLen st (a 3) (a 4)
    [base] ++ readSpan st (a 1) (a 2) ++ readSpan st (a 3) (a 4) ++ readMem 16
      ++ [.actionBase (·.functionCallBase) sir, .actionBytes (·.functionCallByte) (m + args) sir,
          .prepay (a 6).toNat]
  | "promise_batch_action_transfer" =>
    [base] ++ readMem 16 ++ [.actionBase (·.transfer) (sirOf st (promiseReceiver? st (a 0).toNat))]
  | "promise_batch_action_stake" =>
    [base] ++ readMem 16 ++ readSpan st (a 2) (a 3)
      ++ [.actionBase (·.stake) (sirOf st (promiseReceiver? st (a 0).toNat))]
  | "promise_batch_action_add_key_with_full_access" =>
    [base] ++ readSpan st (a 1) (a 2)
      ++ [.actionBase (·.addFullAccessKey) (sirOf st (promiseReceiver? st (a 0).toNat))]
  | "promise_batch_action_add_key_with_function_call" =>
    let sir := sirOf st (promiseReceiver? st (a 0).toNat)
    let methods := getMemOrReg st (a 8) (a 7) |>.getD []
    let numMethods := if methods.isEmpty then 0 else (methods.filter (· == 44)).length + 1
    [base] ++ readSpan st (a 1) (a 2) ++ readMem 16 ++ readSpan st (a 5) (a 6)
      ++ utf8 (spanLen st (a 5) (a 6)) ++ readSpan st (a 7) (a 8)
      ++ [.actionBase (·.addFunctionCallKeyBase) sir,
          .actionBytes (·.addFunctionCallKeyByte) (methods.length + numMethods) sir]
  | "promise_batch_action_delete_key" =>
    [base] ++ readSpan st (a 1) (a 2)
      ++ [.actionBase (·.deleteKey) (sirOf st (promiseReceiver? st (a 0).toNat))]
  | "promise_batch_action_delete_account" =>
    [base] ++ readSpan st (a 1) (a 2) ++ utf8 (spanLen st (a 1) (a 2))
      ++ [.actionBase (·.deleteAccount) (sirOf st (promiseReceiver? st (a 0).toNat))]
  | "promise_results_count" => [base]
  | "promise_result" => [base]
  | "promise_return" => [base, .ext "promise_return"]
  | "gas" => [.burn (a 0).toNat]
  | _ => [base]

/-- Charges before a host function runs. Invalid handles retain input-reading
costs, but cannot incur later receipt/action fees or prepaid function-call gas. -/
def chargesBefore (name : String) (st : Store NearState) (args : List Value) : List Charge :=
  let a := argU64 args
  let base : Charge := .ext "base"
  let charges := chargesBeforeUnvalidated name st args
  if (name == "promise_then" || name == "promise_batch_then") &&
      !promiseIndexValid st (a 0).toNat then
    [base] ++ readSpan st (a 1) (a 2) ++ utf8 (spanLen st (a 1) (a 2))
  else if name.startsWith "promise_batch_action_" &&
      (promiseReceiver? st (a 0).toNat).isNone then
    charges.filter fun charge => match charge with
      | .actionBase .. | .actionBytes .. | .prepay .. => false
      | _ => true
  else charges

/-- Length of register `reg` in `st`, if set. -/
def registerLen? (st : Store NearState) (reg : UInt64) : Option Nat :=
  (st.host.registers reg.toNat).map List.length

/-- Charges after a host function ran, from its effect. -/
def chargesAfter (name : String) (before after : Store NearState) (args : List Value) : List Charge :=
  let a := argU64 args
  match name with
  | "storage_write" =>
    match getMemOrReg before (a 1) (a 0) with
    | some key =>
      match before.host.storage key with
      | some old => writeReg old.length
      | none => []
    | none => []
  | "storage_read" =>
    match getMemOrReg before (a 1) (a 0) with
    | some key =>
      match before.host.storage key with
      | some v => [.ext "storage_read_value_byte" v.length] ++ writeReg v.length
      | none => []
    | none => []
  | "storage_remove" =>
    match getMemOrReg before (a 1) (a 0) with
    | some key =>
      match before.host.storage key with
      | some v => writeReg v.length
      | none => []
    | none => []
  | "promise_result" =>
    match getPromiseResult? after.host.promiseResults (a 0).toNat with
    | some (.successful _) => [.ext "write_register_base"]
    | _ => []
  | _ => []

/-- `storage_usage` after a storage host function: new records cost
key + value + `num_extra_bytes_record`, overwrites the value difference. -/
def updateStorageUsage (extraBytes : Nat) (name : String) (before after : Store NearState)
    (args : List Value) : Store NearState :=
  let a := argU64 args
  let adjust (key : List UInt8) : Store NearState :=
    let old := (before.host.storage key).map List.length
    let new := (after.host.storage key).map List.length
    let usage := after.host.context.storageUsage.toNat
    let usage' := match old, new with
      | none, some n => usage + key.length + n + extraBytes
      | some o, some n => usage + n - o
      | some o, none => usage - (key.length + o + extraBytes)
      | none, none => usage
    { after with host := { after.host with context := { after.host.context with storageUsage := UInt64.ofNat usage' } } }
  match name with
  | "storage_write" | "storage_remove" =>
    match getMemOrReg before (a 1) (a 0) with
    | some key => adjust key
    | none => after
  | _ => after

/-- Deposits attached to promise actions leave the account balance when the
action is created (`BalanceExceeded` if it cannot cover them). -/
def deductDeposit (name : String) (before after : Store NearState) (args : List Value) :
    Store NearState × Option HostError :=
  let a := argU64 args
  let amountAt (ptr : UInt64) : Option Nat := readU128Mem before ptr
  let deposit : Option Nat := match name with
    | "promise_create" => amountAt (a 6)
    | "promise_then" => amountAt (a 7)
    | "promise_batch_action_function_call" => amountAt (a 5)
    | "promise_batch_action_transfer" => amountAt (a 1)
    | "promise_batch_action_stake" => amountAt (a 1)
    | _ => some 0
  match deposit with
  | some 0 => (after, none)
  | some d =>
    let bal := after.host.context.accountBalance
    if d ≤ bal then
      ({ after with host := { after.host with context := { after.host.context with accountBalance := bal - d } } }, none)
    else (after, some .balanceExceeded)
  | none => (after, none)

/-- `panic_utf8(len, ptr)` with the message. -/
def panicUtf8Metered : HostFn NearState :=
  { params := [.i64, .i64], results := []
    invoke := fun st args =>
      match args with
      | [.i64 len, .i64 ptr] =>
        match getMemOrReg st ptr len with
        | some bytes =>
          match String.fromUTF8? ⟨bytes.toArray⟩ with
          | some msg => trapWith st (.guestPanic msg)
          | none => trapWith st .badUTF8
        | none => trapWith st .memoryAccessViolation
      | _ => trapWith st .memoryAccessViolation }

def panicMetered : HostFn NearState :=
  { invoke := fun st _ => trapWith st (.guestPanic "explicit guest panic") }

def abortMetered : HostFn NearState :=
  { params := [.i32, .i32, .i32, .i32], results := []
    invoke := fun st _ => trapWith st (.guestPanic "abort") }

/-- The `gas(n)` import used by older metering schemes. -/
def gasFn : HostFn NearState :=
  { params := [.i32], results := []
    invoke := fun st args =>
      match args with
      | [.i32 n] =>
        let (g, e) := st.host.gas.burn n.toNat
        let st' := { st with host := { st.host with gas := g, gasProfile := { st.host.gasProfile with
          wasm := st.host.gasProfile.wasm + (g.burnt - st.host.gas.burnt) } } }
        match e with
        | none => .Return [] st'
        | some err => trapWith st' err
      | _ => trapWith st .memoryAccessViolation }

/-- View restrictions precede argument reads and action/storage fees. -/
def viewRestrictedHost (name : String) : Bool :=
  ["predecessor_account_id", "signer_account_id", "signer_account_pk", "attached_deposit",
   "prepaid_gas", "used_gas", "storage_write", "storage_remove", "promise_create",
   "promise_then", "promise_and", "promise_batch_create", "promise_batch_then",
   "promise_batch_action_create_account", "promise_batch_action_deploy_contract",
   "promise_batch_action_function_call", "promise_batch_action_transfer", "promise_batch_action_stake",
   "promise_batch_action_add_key_with_full_access", "promise_batch_action_add_key_with_function_call",
   "promise_batch_action_delete_key", "promise_batch_action_delete_account",
   "promise_yield_create", "promise_yield_resume", "promise_results_count", "promise_result",
   "promise_return"].contains name

def deprecatedRuntimeHost (name : String) : Bool :=
  ["storage_iter_prefix", "storage_iter_range", "storage_iter_next"].contains name

/-- Post-call metering is separated from host invocation so its frame
properties can be used directly in execution proofs. -/
def finishMeteredCall (extraBytes : Nat) (name : String) (before : Store NearState)
    (args : List Value) : HostResult NearState → HostResult NearState
  | .Return vals st2 =>
    let (ns2, err2) := applyCharges st2.host (chargesAfter name before st2 args)
    let st3 := { st2 with host := ns2 }
    match err2 with
    | some e => trapWith st3 e
    | none =>
      match deductDeposit name before st3 args with
      | (st4, some e) => trapWith st4 e
      | (st4, none) => .Return vals (updateStorageUsage extraBytes name before st4 args)
  | .Trap st2 msg => .Trap st2 msg
  | .Throw st2 tag vals => .Throw st2 tag vals

/-- Wrap a functional host function with its gas and storage-usage rules. -/
def metered (extraBytes : Nat) (name : String) (fn : HostFn NearState) : HostFn NearState :=
  { fn with invoke := fun st args =>
      if deprecatedRuntimeHost name then trapWith st (.deprecated name)
      else if st.host.context.isView && viewRestrictedHost name then
        let charges := [.ext "base"] ++
          (if name == "promise_return" then [.ext "promise_return"] else [])
        let (ns, error) := applyCharges st.host charges
        trapWith { st with host := ns } (error.getD (.prohibitedInView name))
      else
      let (ns, err) := applyCharges st.host (chargesBefore name st args)
      let st1 := { st with host := { ns with context := { ns.context with
        usedGas := UInt64.ofNat ns.gas.used } } }
      match err with
      | some e => trapWith st1 e
      | none =>
        finishMeteredCall extraBytes name st1 args (fn.invoke st1 args) }

/-- These host operations require semantics not supplied by `VMContext`.
Reject them on invocation instead of using the functional host's placeholder
crypto, validator, or yield implementations. Merely importing one is allowed. -/
def unsupportedRuntimeHost (name : String) : Bool :=
  ["sha256", "keccak256", "keccak512", "ripemd160", "ecrecover", "ed25519_verify",
   "validator_stake", "validator_total_stake", "promise_yield_create", "promise_yield_resume",
   "alt_bn128_g1_multiexp", "alt_bn128_g1_sum", "alt_bn128_pairing_check",
   "bls12381_g1_multiexp", "bls12381_g2_multiexp", "bls12381_map_fp_to_g1",
   "bls12381_map_fp2_to_g2", "bls12381_p1_decompress", "bls12381_p2_decompress",
   "bls12381_p1_sum", "bls12381_p2_sum", "bls12381_pairing_check"].contains name

/-- The metered host table: `nearHostFns` with gas, plus the structured
panics and the `gas` import. -/
def meteredHostFns (cfg : RuntimeConfig) : List (ImportDecl × HostFn NearState) :=
  let extra := cfg.fees.numExtraBytesRecord
  let swap (decl : ImportDecl) (fn : HostFn NearState) : HostFn NearState :=
    if unsupportedRuntimeHost decl.name then
      { fn with invoke := fun st _ => trapWith st (.unsupported decl.name) }
    else match decl.name with
    | "panic" => panicMetered
    | "panic_utf8" => panicUtf8Metered
    | "abort" => abortMetered
    | _ => fn
  (nearHostFns.map fun (decl, fn) => (decl, metered extra decl.name (swap decl fn)))
    ++ [({ «module» := "env", name := "gas", params := [.i32], results := [] }, gasFn)]

/-- Resolve imports in declaration order, retaining the first unknown-import
error. Structural recursion exposes the environment invariant to proofs. -/
def resolveMeteredImports (cfg : RuntimeConfig) : List ImportDecl → Except String (HostEnv NearState)
  | [] => .ok { funcs := [] }
  | decl :: rest =>
    match (meteredHostFns cfg).find? (fun p => importMatches p.fst decl) with
    | none => .error s!"{decl.module}.{decl.name}"
    | some (_, fn) =>
      match resolveMeteredImports cfg rest with
      | .error message => .error message
      | .ok env => .ok { funcs := fn :: env.funcs }

/-- Resolve a module's imports against the metered table. `error` names the
first import that is not a known NEAR host function. -/
def resolveMetered (cfg : RuntimeConfig) (m : Module) : Except String (HostEnv NearState) :=
  resolveMeteredImports cfg m.imports

end Wasm.Near
