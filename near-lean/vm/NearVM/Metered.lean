import NearVM.AccountId
import NearVM.Host
import NearVM.Config
import NearVM.PromiseGraph
import NearVM.MethodEncoding

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
    match st.host.registers ptr.toNat with
    | none => []
    | some bytes => [.ext "read_register_base", .ext "read_register_byte" bytes.length]
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

/-- Native transfer reads the u128 before looking up the promise or charging
accumulated action fees. A failed read retains only the argument-reading cost. -/
def transferCharges (st : Store NearState) (index amountPtr : UInt64) : List Charge :=
  let initialCharges := [.ext "base"] ++ readMem 16
  match readU128Mem st amountPtr with
  | none => initialCharges
  | some _ => initialCharges ++ [.actionBase
      (fun fees => transferFees fees st.host.config.ethImplicitAccounts
        ((promiseReceiver? st index.toNat).getD [])) (sirOf st (promiseReceiver? st index.toNat))]

theorem transferCharges_invalidAmount (st : Store NearState) (index amountPtr : UInt64)
    (h : readU128Mem st amountPtr = none) :
    transferCharges st index amountPtr = [.ext "base"] ++ readMem 16 := by
  simp only [transferCharges, h]

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

/-- The supported operations that allocate one raw handle on success. -/
def allocatesPromise (name : String) : Bool :=
  ["promise_create", "promise_then", "promise_and", "promise_batch_create", "promise_batch_then"].contains name

def promiseCapacityError (st : Store NearState) : Option HostError :=
  match st.host.config.maxPromises with
  | none => none
  | some limit =>
    if st.host.promises.length + 1 > limit then
      some (.numberPromisesExceeded (st.host.promises.length + 1) limit)
    else none

def creationAccountArgs (name : String) (args : List Value) : Option (UInt64 × UInt64) :=
  if name == "promise_create" || name == "promise_batch_create" then some (argU64 args 0, argU64 args 1)
  else if name == "promise_then" || name == "promise_batch_then" then some (argU64 args 1, argU64 args 2)
  else none

/-- Receiver parsing precedes receipt creation and the allocation limit. -/
def creationAccountError (name : String) (st : Store NearState) (args : List Value) : Option HostError :=
  match creationAccountArgs name args with
  | none => none
  | some (len, ptr) =>
    match getMemOrReg st ptr len with
    | none => some (if len == u64Max then .invalidRegisterId ptr.toNat else .memoryAccessViolation)
    | some bytes =>
      if (String.fromUTF8? ⟨bytes.toArray⟩).isNone then some .badUTF8
      else if !st.host.config.validAccountId bytes then some .invalidAccountId
      else none

def creationPrefixError (name : String) (st : Store NearState) (args : List Value) : Option HostError :=
  match creationAccountError name st args with
  | some error => some error
  | none =>
    if (name == "promise_then" || name == "promise_batch_then") &&
        !promiseIndexValid st (argU64 args 0).toNat then
      some (.invalidPromiseIndex (argU64 args 0).toNat)
    else none

/-- Retain receipt dispatch charges, stopping before function-action processing. -/
def throughNewReceipt : List Charge → List Charge
  | [] => []
  | charge :: rest => match charge with
    | .newReceipt .. => [charge]
    | _ => charge :: throughNewReceipt rest

structure FunctionCallInputs where
  target : Option Nat := none
  methodLen : UInt64
  methodPtr : UInt64
  argsLen : UInt64
  argsPtr : UInt64
  amountPtr : UInt64
  gas : UInt64

def functionCallInputs (args : List Value) (offset : Nat) (target : Option Nat := none) : FunctionCallInputs :=
  { target, methodLen := argU64 args offset, methodPtr := argU64 args (offset + 1)
    argsLen := argU64 args (offset + 2), argsPtr := argU64 args (offset + 3)
    amountPtr := argU64 args (offset + 4), gas := argU64 args (offset + 5) }

def functionCallInputs? (name : String) (args : List Value) : Option FunctionCallInputs :=
  match name with
  | "promise_create" => some (functionCallInputs args 2)
  | "promise_then" => some (functionCallInputs args 3)
  | "promise_batch_action_function_call" => some (functionCallInputs args 1 (some (argU64 args 0).toNat))
  | _ => none

structure FunctionCallPlan where
  charges : List Charge
  error : Option HostError := none

def spanReadError (len ptr : UInt64) : HostError :=
  if len == u64Max then .invalidRegisterId ptr.toNat else .memoryAccessViolation

def functionCallTargetError (st : Store NearState) (index : Nat) : Option HostError :=
  match getPromise? st.host.promises index with
  | some (.batch ..) | some (.callback ..) => none
  | some (.and _) => some .cannotAppendActionToJointPromise
  | _ => some (.invalidPromiseIndex index)

/-- The reference reads amount, method (rejecting empty), arguments, then the
target handle. Fees and prepaid gas follow only after all inputs are valid. -/
def functionCallPlan (st : Store NearState) (input : FunctionCallInputs) (sir : Bool) : FunctionCallPlan :=
  let amountCharges := [.ext "base"] ++ readMem 16
  match readU128Mem st input.amountPtr with
  | none => { charges := amountCharges, error := some .memoryAccessViolation }
  | some _ =>
    let methodCharges := amountCharges ++ readSpan st input.methodLen input.methodPtr
    match getMemOrReg st input.methodPtr input.methodLen with
    | none => { charges := methodCharges, error := some (spanReadError input.methodLen input.methodPtr) }
    | some method =>
      if method.isEmpty then { charges := methodCharges, error := some .emptyMethodName }
      else
        let argCharges := methodCharges ++ readSpan st input.argsLen input.argsPtr
        match getMemOrReg st input.argsPtr input.argsLen with
        | none => { charges := argCharges, error := some (spanReadError input.argsLen input.argsPtr) }
        | some arguments =>
          let targetError := input.target.bind (functionCallTargetError st)
          match targetError with
          | some error => { charges := argCharges, error := some error }
          | none => { charges := argCharges ++
              [.actionBase (·.functionCallBase) sir,
               .actionBytes (·.functionCallByte) (method.length + arguments.length) sir,
               .prepay input.gas.toNat] }

def functionCallInputError (name : String) (st : Store NearState) (args : List Value) : Option HostError :=
  (functionCallInputs? name args).bind fun input => (functionCallPlan st input false).error

structure FunctionKeyInputs where
  target : Nat
  publicKeyLen : UInt64
  publicKeyPtr : UInt64
  allowancePtr : UInt64
  receiverLen : UInt64
  receiverPtr : UInt64
  methodsLen : UInt64
  methodsPtr : UInt64

def functionKeyInputs (args : List Value) : FunctionKeyInputs :=
  { target := (argU64 args 0).toNat
    publicKeyLen := argU64 args 1, publicKeyPtr := argU64 args 2
    allowancePtr := argU64 args 4, receiverLen := argU64 args 5, receiverPtr := argU64 args 6
    methodsLen := argU64 args 7, methodsPtr := argU64 args 8 }

/-- Native order: key read, allowance, receiver read/UTF-8/syntax, method read/
nonempty segments, target lookup, action fees, then public-key decoding. -/
def functionKeyPlan (st : Store NearState) (input : FunctionKeyInputs) (sir : Bool) : FunctionCallPlan :=
  let keyCharges := [.ext "base"] ++ readSpan st input.publicKeyLen input.publicKeyPtr
  match getMemOrReg st input.publicKeyPtr input.publicKeyLen with
  | none => { charges := keyCharges, error := some (spanReadError input.publicKeyLen input.publicKeyPtr) }
  | some publicKey =>
    let allowanceCharges := keyCharges ++ readMem 16
    match readU128Mem st input.allowancePtr with
    | none => { charges := allowanceCharges, error := some .memoryAccessViolation }
    | some _ =>
      let receiverCharges := allowanceCharges ++ readSpan st input.receiverLen input.receiverPtr
      match getMemOrReg st input.receiverPtr input.receiverLen with
      | none => { charges := receiverCharges, error := some (spanReadError input.receiverLen input.receiverPtr) }
      | some receiver =>
        let parsedCharges := receiverCharges ++ utf8 receiver.length
        if (String.fromUTF8? ⟨receiver.toArray⟩).isNone then { charges := parsedCharges, error := some .badUTF8 }
        else if !st.host.config.validAccountId receiver then { charges := parsedCharges, error := some .invalidAccountId }
        else
          let methodsCharges := parsedCharges ++ readSpan st input.methodsLen input.methodsPtr
          match getMemOrReg st input.methodsPtr input.methodsLen with
          | none => { charges := methodsCharges, error := some (spanReadError input.methodsLen input.methodsPtr) }
          | some methods =>
            if !methodNamesValid methods then { charges := methodsCharges, error := some .emptyMethodName }
            else match functionCallTargetError st input.target with
            | some error => { charges := methodsCharges, error := some error }
            | none =>
              { charges := methodsCharges ++ [.actionBase (·.addFunctionCallKeyBase) sir,
                  .actionBytes (·.addFunctionCallKeyByte) (methodNamesGasBytes methods) sir]
                error := if serializedPublicKeyValid publicKey then none else some .invalidPublicKey }

/-- Argument-dependent charge plan before validating promise handles. -/
def chargesBeforeUnvalidated (name : String) (st : Store NearState) (args : List Value) : List Charge :=
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
  | "storage_read" =>
    let k := spanLen st (a 0) (a 1)
    [base, .ext "storage_read_base"] ++ readSpan st (a 0) (a 1) ++ [.ext "storage_read_key_byte" k]
  | "storage_has_key" =>
    let k := spanLen st (a 0) (a 1)
    [base, .ext "storage_has_key_base"] ++ readSpan st (a 0) (a 1) ++ [.ext "storage_has_key_byte" k]
  | "promise_create" =>
    let sir := sirOfSpan st (a 0) (a 1)
    [base] ++ readSpan st (a 0) (a 1) ++ utf8 (spanLen st (a 0) (a 1)) ++ [.newReceipt sir []]
      ++ (functionCallPlan st (functionCallInputs args 2) sir).charges
  | "promise_then" =>
    let sir := sirOfSpan st (a 1) (a 2)
    [base] ++ readSpan st (a 1) (a 2) ++ utf8 (spanLen st (a 1) (a 2))
      ++ [.newReceipt sir (depsSir st (a 0).toNat (getMemOrReg st (a 2) (a 1)))]
      ++ (functionCallPlan st (functionCallInputs args 3) sir).charges
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
    (functionCallPlan st (functionCallInputs args 1 (some (a 0).toNat)) sir).charges
  | "promise_batch_action_transfer" =>
    transferCharges st (a 0) (a 1)
  | "promise_batch_action_stake" =>
    [base] ++ readMem 16 ++ readSpan st (a 2) (a 3)
      ++ [.actionBase (·.stake) (sirOf st (promiseReceiver? st (a 0).toNat))]
  | "promise_batch_action_add_key_with_full_access" =>
    [base] ++ readSpan st (a 1) (a 2)
      ++ [.actionBase (·.addFullAccessKey) (sirOf st (promiseReceiver? st (a 0).toNat))]
  | "promise_batch_action_add_key_with_function_call" =>
    (functionKeyPlan st (functionKeyInputs args) (sirOf st (promiseReceiver? st (a 0).toNat))).charges
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

/-- The storage adapter is reached only after input reads and length checks.
Its old-value charge precedes the output-register operation, even if that traps. -/
structure StorageMutationPlan where
  charges : List Charge
  error : Option HostError := none

def storageValueCharges (st : Store NearState) (cost : String) (key : List UInt8) : List Charge :=
  if st.host.config.chargeStorageValueAccess then
    match st.host.storage key with
    | some value => [.ext cost value.length]
    | none => []
  else []

def storageMutationPlan? (name : String) (st : Store NearState) (args : List Value) :
    Option StorageMutationPlan := do
  if name != "storage_write" && name != "storage_remove" then none else
  let a := argU64 args
  let charges := [.ext "base", .ext (name ++ "_base")] ++ readSpan st (a 0) (a 1)
  let some key := getMemOrReg st (a 1) (a 0)
    | return { charges, error := some (spanReadError (a 0) (a 1)) }
  if let some limit := st.host.config.maxStorageKeyLen then
    if key.length > limit then return { charges, error := some (.keyLengthExceeded key.length limit) }
  if name == "storage_write" then
    let charges := charges ++ readSpan st (a 2) (a 3)
    let some value := getMemOrReg st (a 3) (a 2)
      | return { charges, error := some (spanReadError (a 2) (a 3)) }
    if let some limit := st.host.config.maxStorageValueLen then
      if value.length > limit then return { charges, error := some (.valueLengthExceeded value.length limit) }
    return { charges := charges ++ [.ext "storage_write_key_byte" key.length,
      .ext "storage_write_value_byte" value.length] ++ storageValueCharges st "storage_write_evicted_byte" key }
  else
    return { charges := charges ++ [.ext "storage_remove_key_byte" key.length] ++
      storageValueCharges st "storage_remove_ret_value_byte" key }

/-- Charges before a host function runs. Invalid handles retain input-reading
costs, but cannot incur later receipt/action fees or prepaid function-call gas. -/
def chargesBefore (name : String) (st : Store NearState) (args : List Value) : List Charge :=
  let a := argU64 args
  let base : Charge := .ext "base"
  let charges := chargesBeforeUnvalidated name st args
  if let some plan := storageMutationPlan? name st args then plan.charges
  else if name == "promise_and" && (a 1).toNat * 8 ≥ 2 ^ 64 then
    [base, .ext "promise_and_base"]
  else if let some (len, ptr) := creationAccountArgs name args then
    let readAccount := [base] ++ readSpan st len ptr
    let parseAccount := readAccount ++ utf8 (spanLen st len ptr)
    match creationAccountError name st args with
    | some .memoryAccessViolation | some (.invalidRegisterId _) => readAccount
    | some _ => parseAccount
    | none =>
      if (creationPrefixError name st args).isSome then parseAccount
      else if (promiseCapacityError st).isSome then throughNewReceipt charges
      else charges
  else if name.startsWith "promise_batch_action_" &&
      (promiseReceiver? st (a 0).toNat).isNone then
    charges.filter fun charge => match charge with
      | .actionBase .. | .actionBytes .. | .prepay .. => false
      | _ => true
  else charges

/-- The public pre-call plan cannot charge transfer fees for an unread amount,
including an invalid target handle. -/
theorem chargesBefore_transfer_invalidAmount (st : Store NearState) (index amountPtr : UInt64)
    (h : readU128Mem st amountPtr = none) :
    chargesBefore "promise_batch_action_transfer" st [.i64 index, .i64 amountPtr] =
      [.ext "base"] ++ readMem 16 := by
  simp [chargesBefore, chargesBeforeUnvalidated, storageMutationPlan?, creationAccountArgs, argU64, transferCharges, h, readMem]

/-- Check each expanded prefix, retaining duplicate receipt dependencies.
This ordering makes an earlier limit violation precede a later invalid handle. -/
def joinedDependenciesError (handles : List PromiseHandle) (limit : Nat) : List Nat → Nat → Option HostError
  | [], _ => none
  | index :: rest, count =>
    match handles[index]? with
    | none => some (.invalidPromiseIndex index)
    | some handle =>
      let count := count + handle.dependencies.length
      if count > limit then some (.numberInputDataDependenciesExceeded count limit)
      else joinedDependenciesError handles limit rest count

/-- Validation after argument-reading charges and before functional invocation.
An invalid internal raw graph is explicit unsupported model state. Ordinary VM
execution preserves graph well-formedness independently of this check. -/
def promiseJoinError (st : Store NearState) (args : List Value) : Option HostError :=
  match args with
  | [.i64 ptr, .i64 count] =>
    if count.toNat * 8 ≥ 2 ^ 64 then some .integerOverflow
    else if ptr.toNat + count.toNat * 8 > memBytes st then some .memoryAccessViolation
    else match readU64Array st ptr count.toNat with
    | none => some .memoryAccessViolation
    | some [] => none
    | some indices =>
      match st.host.config.maxInputDataDependencies with
      | none => none
      | some limit =>
        match convertPromises st.host.promises with
        | none => some (.unsupported "promise_and: malformed raw graph")
        | some graph => joinedDependenciesError graph.handles limit indices 0
  | _ => none

def transferInputError (st : Store NearState) (args : List Value) : Option HostError :=
  match args with
  | [.i64 _, .i64 amountPtr] => if (readU128Mem st amountPtr).isNone then some .memoryAccessViolation else none
  | _ => none

theorem transferInputError_invalidAmount (st : Store NearState) (index amountPtr : UInt64)
    (h : readU128Mem st amountPtr = none) :
    transferInputError st [.i64 index, .i64 amountPtr] = some .memoryAccessViolation := by
  simp only [transferInputError, h, Option.isNone_none, ite_true]

def invocationArgumentError (name : String) (st : Store NearState) (args : List Value) : Option HostError :=
  if let some plan := storageMutationPlan? name st args then plan.error
  else if name == "promise_and" then promiseJoinError st args
  else if name == "promise_batch_action_transfer" then transferInputError st args
  else if name == "promise_batch_action_add_key_with_function_call" then (functionKeyPlan st (functionKeyInputs args) false).error
  else creationPrefixError name st args

def preInvokeError (name : String) (st : Store NearState) (args : List Value) : Option HostError :=
  match invocationArgumentError name st args with
  | some error => some error
  | none =>
    match (if allocatesPromise name then promiseCapacityError st else none) with
    | some error => some error
    | none => functionCallInputError name st args

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

/-- Deduct a promise deposit or grant the protocol's one-yocto subsidy.
Only function-call actions qualify; the counter is diagnostic until receipt commit. -/
def deductPromiseDeposit (name : String) (ns : NearState) (d : Nat) : NearState × Option HostError :=
  let bal := ns.context.accountBalance
  if ns.config.oneYoctoOnPromise && d == 1 && bal == 0 &&
      (name == "promise_create" || name == "promise_then" ||
       name == "promise_batch_action_function_call") then
    ({ ns with subsidizedAmount := ns.subsidizedAmount + d }, none)
  else if d ≤ bal then
    ({ ns with context := { ns.context with accountBalance := bal - d } }, none)
  else (ns, some .balanceExceeded)

/-- Successful deductions conserve liquid funds plus minted deposits. -/
theorem deductPromiseDeposit_accounting (name : String) (ns : NearState) (d : Nat)
    (h : (deductPromiseDeposit name ns d).2 = none) :
    ns.context.accountBalance + (deductPromiseDeposit name ns d).1.subsidizedAmount =
      (deductPromiseDeposit name ns d).1.context.accountBalance + ns.subsidizedAmount + d := by
  by_cases hs : (ns.config.oneYoctoOnPromise && d == 1 && ns.context.accountBalance == 0 &&
      (name == "promise_create" || name == "promise_then" ||
       name == "promise_batch_action_function_call")) = true
  · simp [deductPromiseDeposit, hs, Nat.add_assoc]
  · by_cases hd : d ≤ ns.context.accountBalance
    · simp [deductPromiseDeposit, hs, hd]
      omega
    · simp [deductPromiseDeposit, hs, hd] at h

/-- Deposit carried by each financial host ABI. Non-financial actions, including
stake targets, carry no outgoing deposit. -/
def promiseDeposit? (name : String) (before : Store NearState) (args : List Value) : Option Nat :=
  let a := argU64 args
  let amountAt (ptr : UInt64) : Option Nat := readU128Mem before ptr
  match name with
  | "promise_create" => amountAt (a 6)
  | "promise_then" => amountAt (a 7)
  | "promise_batch_action_function_call" => amountAt (a 5)
  | "promise_batch_action_transfer" => amountAt (a 1)
  | _ => some 0

def deductDeposit (name : String) (before after : Store NearState) (args : List Value) :
    Store NearState × Option HostError :=
  let deposit := promiseDeposit? name before args
  match deposit with
  | some 0 => (after, none)
  | some d =>
    let (ns, err) := deductPromiseDeposit name after.host d
    ({ after with host := ns }, err)
  | none => (after, none)

/-- Stake actions carry a target stake, not an outgoing deposit. Scheduling
one leaves liquid funds untouched; execution uses the receiver's own balance. -/
theorem deductDeposit_stake (before after : Store NearState) (args : List Value) :
    deductDeposit "promise_batch_action_stake" before after args = (after, none) := rfl

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

/-- Method bytes passed to the external receipt builder. The key ABI supplies
CSV bytes: ASCII separators cannot split a UTF-8 multibyte sequence. -/
def actionMethodBytes? (name : String) (before : Store NearState) (args : List Value) : Option (List UInt8) :=
  if name == "promise_batch_action_add_key_with_function_call" then
    getMemOrReg before (argU64 args 8) (argU64 args 7)
  else (functionCallInputs? name args).bind fun input => getMemOrReg before input.methodPtr input.methodLen

/-- Runtime externals decode method names after fees/prepayment and balance
checks. MockedExternal deliberately accepts opaque method bytes instead. -/
def actionMethodEncodingError (name : String) (before : Store NearState) (args : List Value) : Option HostError :=
  if before.host.config.validateActionMethodUtf8 then
    match actionMethodBytes? name before args with
    | some bytes =>
      if name == "promise_batch_action_add_key_with_function_call" then
        if methodNameFieldsUtf8 bytes then none else some .invalidMethodName
      else if (String.fromUTF8? ⟨bytes.toArray⟩).isNone then some .invalidMethodName else none
    | none => none
  else none

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
      | (st4, none) =>
        match actionMethodEncodingError name before args with
        | some error => trapWith st4 error
        | none => .Return vals (updateStorageUsage extraBytes name before st4 args)
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
        trapWith { st with host := ns } (error.getD (.prohibitedInView (if name == "promise_create" then "promise_batch_create"
          else if name == "promise_then" then "promise_batch_then" else name)))
      else
      let (ns, err) := applyCharges st.host (chargesBefore name st args)
      let st1 := { st with host := { ns with context := { ns.context with
        usedGas := UInt64.ofNat ns.gas.used } } }
      match err with
      | some e => trapWith st1 e
      | none =>
        match preInvokeError name st1 args with
        | some error => trapWith st1 error
        | none => finishMeteredCall extraBytes name st1 args (fn.invoke st1 args) }

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
