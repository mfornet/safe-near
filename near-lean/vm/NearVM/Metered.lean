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
`read_cached_trie_node`) are charged only when the context supplies
`storageAccounting` (the trie shape); without it, replay comparisons of burnt
gas on storage-heavy calls must account for the difference.
-/

-- nearcore divergence: `touching_trie_node`/`read_cached_trie_node` are charged only when the
-- context supplies `storageAccounting` (`prepareStorageCallAux`); without it they are skipped.
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
def trapWith (st : HostStore NearState) (e : HostError) : HostResult NearState :=
  .Trap { st with host := { st.host with lastError := some e } } e.message

/-! ## Cost rules -/

def argU64 (args : List Value) (i : Nat) : UInt64 :=
  match args[i]? with
  | some (.i64 n) => n
  | _ => 0

/-- Bytes of a `(len, ptr)` argument following `get_memory_or_register`. -/
def spanLen (st : HostStore NearState) (len ptr : UInt64) : Nat :=
  if len = u64Max then ((st.host.registers ptr.toNat).map List.length).getD 0 else len.toNat

/-- Reading a `(len, ptr)` argument: memory or register costs. -/
def readSpan (st : HostStore NearState) (len ptr : UInt64) : List Charge :=
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
def promiseReceiver? (st : HostStore NearState) (idx : Nat) : Option (List UInt8) :=
  match getPromise? st.host.promises idx with
  | some (.batch acct _) => some acct
  | some (.callback _ acct _) => some acct
  | _ => none

/-- Same-shard ("sir") test: the receiver is the current account. -/
def sirOf (st : HostStore NearState) (acct : Option (List UInt8)) : Bool :=
  acct == some st.host.context.currentAccountId

def sirOfSpan (st : HostStore NearState) (len ptr : UInt64) : Bool :=
  sirOf st (getMemOrReg st ptr len)

/-- Native transfer reads the u128 before looking up the promise or charging
accumulated action fees. A failed read retains only the argument-reading cost. -/
def transferCharges (st : HostStore NearState) (index amountPtr : UInt64) : List Charge :=
  let initialCharges := [.ext "base"] ++ readMem 16
  match readU128Mem st amountPtr with
  | none => initialCharges
  | some _ => initialCharges ++ [.actionBase
      (fun fees => transferFees fees st.host.config.ethImplicitAccounts
        ((promiseReceiver? st index.toNat).getD [])) (sirOf st (promiseReceiver? st index.toNat))]

theorem transferCharges_invalidAmount (st : HostStore NearState) (index amountPtr : UInt64)
    (h : readU128Mem st amountPtr = none) :
    transferCharges st index amountPtr = [.ext "base"] ++ readMem 16 := by
  simp only [transferCharges, h]

/-- Data routing is same-account when the dependency receiver equals the
callback receiver, which need not be the currently executing account. -/
def depsSir (st : HostStore NearState) (idx : Nat) (receiver : Option (List UInt8)) : List Bool :=
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

def promiseCapacityError (st : HostStore NearState) : Option HostError :=
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

/-- `read_and_parse_account_id`: the read, UTF-8 and account id rule errors. -/
def accountIdError (st : HostStore NearState) (len ptr : UInt64) : Option HostError :=
  match getMemOrReg st ptr len with
  | none => some (if len == u64Max then .invalidRegisterId ptr.toNat else .memoryAccessViolation)
  | some bytes =>
    if (String.fromUTF8? ⟨bytes.toArray⟩).isNone then some .badUTF8
    else if !st.host.config.validAccountId bytes then some .invalidAccountId
    else none

/-- Receiver parsing precedes receipt creation and the allocation limit. -/
def creationAccountError (name : String) (st : HostStore NearState) (args : List Value) : Option HostError :=
  match creationAccountArgs name args with
  | none => none
  | some (len, ptr) =>
    match getMemOrReg st ptr len with
    | none => some (if len == u64Max then .invalidRegisterId ptr.toNat else .memoryAccessViolation)
    | some bytes =>
      if (String.fromUTF8? ⟨bytes.toArray⟩).isNone then some .badUTF8
      else if !st.host.config.validAccountId bytes then some .invalidAccountId
      else none

def creationPrefixError (name : String) (st : HostStore NearState) (args : List Value) : Option HostError :=
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

def functionCallTargetError (st : HostStore NearState) (index : Nat) : Option HostError :=
  match getPromise? st.host.promises index with
  | some (.batch ..) | some (.callback ..) => none
  | some (.and _) => some .cannotAppendActionToJointPromise
  | _ => some (.invalidPromiseIndex index)

/-- The reference reads amount, method (rejecting empty), arguments, then the
target handle. Fees and prepaid gas follow only after all inputs are valid. -/
def functionCallPlan (st : HostStore NearState) (input : FunctionCallInputs) (sir : Bool) : FunctionCallPlan :=
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

def functionCallInputError (name : String) (st : HostStore NearState) (args : List Value) : Option HostError :=
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
def functionKeyPlan (st : HostStore NearState) (input : FunctionKeyInputs) (sir : Bool) : FunctionCallPlan :=
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

/-- The `use_global_contract` hosts' arguments: by account id or code hash. -/
def globalContractInputs? (name : String) : Option Bool :=
  if name == "promise_batch_action_use_global_contract" then some false
  else if name == "promise_batch_action_use_global_contract_by_account_id" then some true
  else none

/-- nearcore's `promise_batch_action_use_global_contract_impl`: read the
identifier (an account id is UTF-8 decoded, charged, and validated; a code hash
must have 32 bytes), look up the target, then charge the action fees on the
identifier's length. -/
def globalContractPlan (st : HostStore NearState) (byAccount : Bool) (target : Nat) (len ptr : UInt64)
    (sir : Bool) : FunctionCallPlan :=
  let readCharges := [.ext "base"] ++ readSpan st len ptr
  match getMemOrReg st ptr len with
  | none => { charges := readCharges, error := some (spanReadError len ptr) }
  | some bytes =>
    let idCharges := if byAccount then readCharges ++ utf8 bytes.length else readCharges
    let idError : Option HostError :=
      if byAccount then
        if (String.fromUTF8? ⟨bytes.toArray⟩).isNone then some .badUTF8
        else if !st.host.config.validAccountId bytes then some .invalidAccountId
        else none
      else if bytes.length != 32 then some .contractCodeHashMalformed else none
    match idError with
    | some error => { charges := idCharges, error := some error }
    | none =>
      match functionCallTargetError st target with
      | some error => { charges := idCharges, error := some error }
      | none =>
        let id : GlobalContractId := if byAccount then .accountId bytes else .codeHash bytes
        { charges := idCharges ++ [.actionBase (·.useGlobalContractBase) sir,
            .actionBytes (·.useGlobalContractByte) id.length sir] }

/-- A log host's charges, in nearcore's order, and the error that stops it
(`logic.rs`): the count check, the decoding base, the remaining-length check,
the read, the decoding bytes, `log_base` and `log_byte` on the decoded length,
then the running-total check. A `u64::MAX` length reads a register here, where
nearcore reads a NUL-terminated string. -/
structure LogPlan where
  charges : List Charge
  error : Option HostError := none

def logPlan (name : String) (st : HostStore NearState) (args : List Value) : LogPlan := Id.run do
  let a := argU64 args
  let base : Charge := .ext "base"
  let total := (st.host.logs.map List.length).sum
  let fits (n : Nat) := withinLimit st.host.config.maxLogLen n
  let limit := st.host.config.maxLogLen.getD 0
  if let some count := st.host.config.maxNumberLogs then
    if st.host.logs.length ≥ count then
      return { charges := [base], error := some (.numberOfLogsExceeded count) }
  let (len, ptr) := (a 0, a 1)
  if name == "log_utf8" then
    let charges := [base, .ext "utf8_decoding_base"]
    if len != u64Max && !fits (total + len.toNat) then
      return { charges, error := some (.totalLogLengthExceeded (total + len.toNat) limit) }
    let charges := charges ++ readSpan st len ptr
    let some msg := getMemOrReg st ptr len | return { charges, error := some (spanReadError len ptr) }
    let charges := charges ++ [.ext "utf8_decoding_byte" msg.length]
    if (String.fromUTF8? ⟨msg.toArray⟩).isNone then return { charges, error := some .badUTF8 }
    let charges := charges ++ [.ext "log_base", .ext "log_byte" msg.length]
    -- nearcore adds the length to the total before reporting it.
    if !fits (total + msg.length) then
      return { charges, error := some (.totalLogLengthExceeded (total + 2 * msg.length) limit) }
    return { charges }
  else
    let charges := [base, .ext "utf16_decoding_base"] ++ readSpan st len ptr
    let some raw := getMemOrReg st ptr len | return { charges, error := some (spanReadError len ptr) }
    if raw.length % 2 != 0 then return { charges, error := some .badUTF16 }
    if !fits (total + raw.length) then
      return { charges, error := some (.totalLogLengthExceeded (total + raw.length) limit) }
    let charges := charges ++ [.ext "utf16_decoding_byte" raw.length]
    let some msg := decodeUtf16 raw | return { charges, error := some .badUTF16 }
    let charges := charges ++ [.ext "log_base", .ext "log_byte" msg.length]
    if !fits (total + msg.length) then
      return { charges, error := some (.totalLogLengthExceeded (total + 2 * msg.length) limit) }
    return { charges }

/-- `ecrecover` and `ed25519_verify` in nearcore's order (`logic.rs`): each
pays its own base (not `base`), reads and checks its inputs one by one, and
stops at the first invalid one; `ed25519_verify` returns false, unread, after
a signature whose last byte has a top bit set. The register write follows a
recovered key. -/
def cryptoPlan? (name : String) (st : HostStore NearState) (args : List Value) : Option LogPlan := do
  let a := argU64 args
  if name == "ecrecover" then
    some <| Id.run do
      let charges := [.ext "ecrecover_base"] ++ readSpan st (a 2) (a 3)
      let some sig := getMemOrReg st (a 3) (a 2) | return { charges, error := some (spanReadError (a 2) (a 3)) }
      if sig.length != 64 then
        return { charges, error := some (.ecRecoverError
          s!"The length of the signature: {sig.length}, exceeds the limit of 64 bytes") }
      if (a 4).toNat ≥ 4 then
        return { charges, error := some (.ecRecoverError
          s!"V recovery byte 0 through 3 are valid but was provided {(a 4).toNat}") }
      let charges := charges ++ readSpan st (a 0) (a 1)
      let some hash := getMemOrReg st (a 1) (a 0) | return { charges, error := some (spanReadError (a 0) (a 1)) }
      if hash.length != 32 then
        return { charges, error := some (.ecRecoverError
          s!"The length of the hash: {hash.length}, exceeds the limit of 32 bytes") }
      if (a 5).toNat > 1 then
        return { charges, error := some (.ecRecoverError
          s!"Malleability flag needs to be 0 or 1, but is instead {(a 5).toNat}") }
      match st.host.crypto.ecrecover.bind fun recover => recover hash sig (a 4).toNat ((a 5).toNat == 1) with
      | some key => return { charges := charges ++ writeReg key.length }
      | none => return { charges }
  else if name == "ed25519_verify" then
    some <| Id.run do
      let charges := [.ext "ed25519_verify_base"] ++ readSpan st (a 0) (a 1)
      let some sig := getMemOrReg st (a 1) (a 0) | return { charges, error := some (spanReadError (a 0) (a 1)) }
      if sig.length != 64 then
        return { charges, error := some (.ed25519VerifyInvalidInput "invalid signature length") }
      if (sig.getLast?.getD 0) &&& 0xE0 != 0 then return { charges }
      let charges := charges ++ readSpan st (a 2) (a 3)
      let some message := getMemOrReg st (a 3) (a 2) | return { charges, error := some (spanReadError (a 2) (a 3)) }
      let charges := charges ++ [.ext "ed25519_verify_byte" message.length] ++ readSpan st (a 4) (a 5)
      let some key := getMemOrReg st (a 5) (a 4) | return { charges, error := some (spanReadError (a 4) (a 5)) }
      if key.length != 32 then
        return { charges, error := some (.ed25519VerifyInvalidInput "invalid public key length") }
      return { charges }
  else none

/-- Argument-dependent charge plan before validating promise handles. -/
def chargesBeforeUnvalidated (name : String) (st : HostStore NearState) (args : List Value) : List Charge :=
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
  -- nearcore reads and parses the account id before `validator_stake_base`.
  | "validator_stake" =>
    let read := [base] ++ readSpan st (a 0) (a 1)
    match getMemOrReg st (a 1) (a 0) with
    | none => read
    | some bytes =>
      if (accountIdError st (a 0) (a 1)).isSome then read ++ utf8 bytes.length
      else read ++ utf8 bytes.length ++ [.ext "validator_stake_base"] ++ writeMem 16
  | "validator_total_stake" => [base, .ext "validator_total_stake_base"] ++ writeMem 16
  -- Hashes pay their own base (not `base`), read the input, then pay per byte
  -- (per block for RIPEMD-160) and write the digest register (`logic.rs`).
  | "sha256" | "keccak256" | "keccak512" | "ripemd160" =>
    let (perInput, digest) : (Nat → Charge) × Nat := match name with
      | "sha256" => (fun n => .ext "sha256_byte" n, 32)
      | "keccak256" => (fun n => .ext "keccak256_byte" n, 32)
      | "keccak512" => (fun n => .ext "keccak512_byte" n, 64)
      | _ => (fun n => .ext "ripemd160_block" ((n + 8) / 64 + 1), 20)
    [.ext (name ++ "_base")] ++ readSpan st (a 0) (a 1) ++
      (match getMemOrReg st (a 1) (a 0) with
       | some value => [perInput value.length] ++ writeReg digest
       | none => [])
  | "ecrecover" | "ed25519_verify" => ((cryptoPlan? name st args).map (·.charges)).getD []
  | "log_utf8" | "log_utf16" => (logPlan name st args).charges
  | "panic" => [base]
  | "panic_utf8" => [base] ++ readSpan st (a 0) (a 1) ++ utf8 (spanLen st (a 0) (a 1))
  | "abort" => [base]
  | "value_return" =>
    let n := spanLen st (a 0) (a 1)
    let byte := st.host.fees.newDataReceiptByte
    let dataGas := (st.host.outputDataReceivers.map fun r =>
      let sir := r == st.host.context.currentAccountId
      byte.send sir * n + byte.execution * n).sum
    -- nearcore reads the value and checks its length before burning the data
    -- receipt bytes.
    [base] ++ readSpan st (a 0) (a 1) ++
      (match getMemOrReg st (a 1) (a 0) with
       | some value => if withinLimit st.host.config.maxReturnLen value.length then [.burn dataGas] else []
       | none => [])
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
  | "promise_batch_action_use_global_contract" =>
    (globalContractPlan st false (a 0).toNat (a 1) (a 2) (sirOf st (promiseReceiver? st (a 0).toNat))).charges
  | "promise_batch_action_use_global_contract_by_account_id" =>
    (globalContractPlan st true (a 0).toNat (a 1) (a 2) (sirOf st (promiseReceiver? st (a 0).toNat))).charges
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

def storageValueCharges (st : HostStore NearState) (cost : String) (key : List UInt8) : List Charge :=
  if st.host.config.chargeStorageValueAccess && st.host.storageAccounting.isNone then
    match st.host.storage key with
    | some value => [.ext cost value.length]
    | none => []
  else []

def storageMutationPlan? (name : String) (st : HostStore NearState) (args : List Value) :
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
def chargesBefore (name : String) (st : HostStore NearState) (args : List Value) : List Charge :=
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
theorem chargesBefore_transfer_invalidAmount (st : HostStore NearState) (index amountPtr : UInt64)
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
def promiseJoinError (st : HostStore NearState) (args : List Value) : Option HostError :=
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

def transferInputError (st : HostStore NearState) (args : List Value) : Option HostError :=
  match args with
  | [.i64 _, .i64 amountPtr] => if (readU128Mem st amountPtr).isNone then some .memoryAccessViolation else none
  | _ => none

theorem transferInputError_invalidAmount (st : HostStore NearState) (index amountPtr : UInt64)
    (h : readU128Mem st amountPtr = none) :
    transferInputError st [.i64 index, .i64 amountPtr] = some .memoryAccessViolation := by
  simp only [transferInputError, h, Option.isNone_none, ite_true]

/-- Hosts whose first argument pair is a value read before anything else is
charged, so an unreadable value is nearcore's typed read error. -/
def spanInputHost (name : String) : Bool :=
  ["value_return", "sha256", "keccak256", "keccak512", "ripemd160"].contains name

def invocationArgumentError (name : String) (st : HostStore NearState) (args : List Value) : Option HostError :=
  if let some plan := storageMutationPlan? name st args then plan.error
  else if name == "promise_and" then promiseJoinError st args
  else if name == "promise_batch_action_transfer" then transferInputError st args
  else if name == "promise_batch_action_add_key_with_function_call" then (functionKeyPlan st (functionKeyInputs args) false).error
  else if let some byAccount := globalContractInputs? name then
    (globalContractPlan st byAccount (argU64 args 0).toNat (argU64 args 1) (argU64 args 2) false).error
  else if name == "log_utf8" || name == "log_utf16" then (logPlan name st args).error
  else if name == "validator_stake" then accountIdError st (argU64 args 0) (argU64 args 1)
  else if let some plan := cryptoPlan? name st args then plan.error
  else if spanInputHost name then
    if (getMemOrReg st (argU64 args 1) (argU64 args 0)).isNone then
      some (spanReadError (argU64 args 0) (argU64 args 1))
    else none
  else creationPrefixError name st args

def preInvokeError (name : String) (st : HostStore NearState) (args : List Value) : Option HostError :=
  match invocationArgumentError name st args with
  | some error => some error
  | none =>
    match (if allocatesPromise name then promiseCapacityError st else none) with
    | some error => some error
    | none => functionCallInputError name st args

/-- The native inline-value boundary is 4000 bytes. Value-byte charges and
large-read overhead precede dereference, including for in-memory values. -/
def storageReadValueCharges (length : Nat) : List Charge :=
  [.ext "storage_read_value_byte" length] ++
    (if length > 4000 then [.ext "storage_large_read_overhead_base",
      .ext "storage_large_read_overhead_byte" length] else [])

/-- Charges after a host function ran, from its effect. -/
def chargesAfter (name : String) (before after : HostStore NearState) (args : List Value) : List Charge :=
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
      | some v => (if before.host.storageAccounting.isNone then storageReadValueCharges v.length else [])
          ++ writeReg v.length
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
def updateStorageUsage (extraBytes : Nat) (name : String) (before after : HostStore NearState)
    (args : List Value) : HostStore NearState :=
  let a := argU64 args
  let adjust (key : List UInt8) : HostStore NearState :=
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
def promiseDeposit? (name : String) (before : HostStore NearState) (args : List Value) : Option Nat :=
  let a := argU64 args
  let amountAt (ptr : UInt64) : Option Nat := readU128Mem before ptr
  match name with
  | "promise_create" => amountAt (a 6)
  | "promise_then" => amountAt (a 7)
  | "promise_batch_action_function_call" => amountAt (a 5)
  | "promise_batch_action_transfer" => amountAt (a 1)
  | _ => some 0

def deductDeposit (name : String) (before after : HostStore NearState) (args : List Value) :
    HostStore NearState × Option HostError :=
  let deposit := promiseDeposit? name before args
  match deposit with
  | some 0 => (after, none)
  | some d =>
    let (ns, err) := deductPromiseDeposit name after.host d
    ({ after with host := ns }, err)
  | none => (after, none)

/-- Stake actions carry a target stake, not an outgoing deposit. Scheduling
one leaves liquid funds untouched; execution uses the receiver's own balance. -/
theorem deductDeposit_stake (before after : HostStore NearState) (args : List Value) :
    deductDeposit "promise_batch_action_stake" before after args = (after, none) := rfl

/-- `panic_utf8(len, ptr)` with the message. -/
def panicUtf8Metered : NearHostFn NearState :=
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

def panicMetered : NearHostFn NearState :=
  { invoke := fun st _ => trapWith st (.guestPanic "explicit guest panic") }

def abortMetered : NearHostFn NearState :=
  { params := [.i32, .i32, .i32, .i32], results := []
    invoke := fun st _ => trapWith st (.guestPanic "abort") }

/-- The `gas(n)` import used by older metering schemes. -/
def gasFn : NearHostFn NearState :=
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
   "promise_return", "promise_batch_action_deploy_global_contract",
   "promise_batch_action_deploy_global_contract_by_account_id",
   "promise_batch_action_use_global_contract",
   "promise_batch_action_use_global_contract_by_account_id"].contains name

def deprecatedRuntimeHost (name : String) : Bool :=
  ["storage_iter_prefix", "storage_iter_range", "storage_iter_next"].contains name

/-- Method bytes passed to the external receipt builder. The key ABI supplies
CSV bytes: ASCII separators cannot split a UTF-8 multibyte sequence. -/
def actionMethodBytes? (name : String) (before : HostStore NearState) (args : List Value) : Option (List UInt8) :=
  if name == "promise_batch_action_add_key_with_function_call" then
    getMemOrReg before (argU64 args 8) (argU64 args 7)
  else (functionCallInputs? name args).bind fun input => getMemOrReg before input.methodPtr input.methodLen

/-- Runtime externals decode method names after fees/prepayment and balance
checks. MockedExternal deliberately accepts opaque method bytes instead. -/
def actionMethodEncodingError (name : String) (before : HostStore NearState) (args : List Value) : Option HostError :=
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
def finishMeteredCall (extraBytes : Nat) (name : String) (before : HostStore NearState)
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

/-- RuntimeExt's external storage phase. The base trie is immutable within the
chunk; prospective updates bypass it. Cache warming survives every gas failure.
Reads bill lookup nodes before value bytes, then dereference with a free gas
counter. Mutations bill old-value bytes before dereference, then disk/cache totals.
Remove stages its update before that final charge; write stages it afterwards. -/
private def prepareStorageCallAux (name : String) (before : HostStore NearState) (args : List Value) :
    HostStore NearState × Option FunctionCallError := Id.run do
  unless ["storage_read", "storage_has_key", "storage_write", "storage_remove"].contains name do
    return (before, none)
  let some initial := before.host.storageAccounting | return (before, none)
  let a := argU64 args
  let some key := getMemOrReg before (a 1) (a 0)
    | return (before, some (.hostError (spanReadError (a 0) (a 1))))
  if let some limit := before.host.config.maxStorageKeyLen then
    if key.length > limit then
      return (before, some (.hostError (.keyLengthExceeded key.length limit)))
  let rawKey := _root_.Near.TrieOverlay.contractKey before.host.context.currentAccountId key
  let mutation := name == "storage_write" || name == "storage_remove"
  let result := _root_.Near.TrieOverlay.getReference initial rawKey
    (mutation || before.host.storageReadsFromTrie)
  let .ok (looked, pointer) := result
    | return (before, some (.executionIssue (.storageAccounting
        (match result with | .error message => message | .ok _ => "lookup failed"))))
  let mut trie := looked
  let mut st := { before with host := { before.host with storageAccounting := some trie } }
  let bill (st : HostStore NearState) (charges : List Charge) :=
    let (host, error) := applyCharges st.host charges
    ({ st with host }, error.map FunctionCallError.hostError)
  let totals (after : _root_.Near.TrieOverlay.State) :=
    [.ext "touching_trie_node" (after.accounting.disk - initial.accounting.disk),
     .ext "read_cached_trie_node" (after.accounting.mem - initial.accounting.mem)]
  if pointer.isSome != (before.host.storage key).isSome then
    return (st, some (.executionIssue (.storageAccounting "trie/contract storage presence mismatch")))
  unless mutation do
    let (paid, error) := bill st (totals trie)
    st := paid
    if error.isSome then return (st, error)
  if name != "storage_has_key" then
    if let some pointer := pointer then
      let length := pointer.reference.2.length
      let charges := if name == "storage_read" then storageReadValueCharges length
        else [.ext (if name == "storage_write" then "storage_write_evicted_byte"
          else "storage_remove_ret_value_byte") length]
      let (paid, error) := bill st charges
      st := paid
      if error.isSome then return (st, error)
      match _root_.Near.TrieOverlay.dereference trie pointer with
      | .error message => return (st, some (.executionIssue (.storageAccounting message)))
      | .ok (fetched, value) =>
        trie := fetched
        st := { st with host := { st.host with storageAccounting := some trie } }
        if before.host.storage key != some value then
          return (st, some (.executionIssue (.storageAccounting "trie/contract storage value mismatch")))
  if name == "storage_remove" then
    trie := trie.remove rawKey
    st := { st with host := { st.host with storageAccounting := some trie } }
  if mutation then
    let (paid, error) := bill st (totals trie)
    st := paid
    if error.isSome then return (st, error)
  if name == "storage_write" then
    let some value := getMemOrReg before (a 3) (a 2)
      | return (st, some (.hostError (spanReadError (a 2) (a 3))))
    trie := trie.set rawKey value
    st := { st with host := { st.host with storageAccounting := some trie } }
  return (st, none)

/-- Burnt gas is at least `b` and within fixed limits: what a charge preserves.
Unlike `Bounded`, it says nothing of promise gas, so it survives the storage
phase's splice of burnt gas into the caller's counter. -/
def GasCounter.Floor (b prepaid maxBurnt : Nat) (g : GasCounter) : Prop :=
  b ≤ g.burnt ∧ g.burnt ≤ maxBurnt ∧ g.burnt ≤ prepaid ∧ g.prepaid = prepaid ∧ g.maxBurnt = maxBurnt

theorem GasCounter.deduct_floor {b prepaid maxBurnt : Nat} {g : GasCounter} (burn use : Nat)
    (h : g.Floor b prepaid maxBurnt) : (g.deduct burn use).1.Floor b prepaid maxBurnt := by
  obtain ⟨hb, hm, hp, hpp, hmb⟩ := h
  unfold deduct
  dsimp only
  split
  · rename_i hok
    simp only [Floor]
    rw [hpp, hmb] at hok
    omega
  · simp only [Floor]
    rw [hpp, hmb]
    refine ⟨?_, ?_, ?_, rfl, rfl⟩
    · exact Nat.le_min.mpr ⟨by omega, Nat.le_min.mpr ⟨by omega, by omega⟩⟩
    · exact Nat.le_trans (Nat.min_le_right _ _) (Nat.min_le_right _ _)
    · exact Nat.le_trans (Nat.min_le_right _ _) (Nat.min_le_left _ _)

theorem applyCharge_floor {b prepaid maxBurnt : Nat} (ns : NearState) (charge : Charge)
    (h : ns.gas.Floor b prepaid maxBurnt) : (applyCharge ns charge).1.gas.Floor b prepaid maxBurnt := by
  cases charge <;> exact GasCounter.deduct_floor _ _ h

theorem applyCharges_floor {b prepaid maxBurnt : Nat} (ns : NearState) (charges : List Charge)
    (h : ns.gas.Floor b prepaid maxBurnt) : (applyCharges ns charges).1.gas.Floor b prepaid maxBurnt := by
  induction charges generalizing ns with
  | nil => exact h
  | cons charge charges ih =>
    have hp := applyCharge_floor ns charge h
    unfold applyCharges
    cases hc : applyCharge ns charge with
    | mk paid error =>
      rw [hc] at hp
      cases error with
      | none => exact ih paid hp
      | some error => exact hp

theorem gas_ite {P : GasCounter → Prop} {c : Prop} [Decidable c]
    {a b : HostStore NearState × Option FunctionCallError}
    (ha : c → P a.1.host.gas) (hb : ¬c → P b.1.host.gas) : P (if c then a else b).1.host.gas := by
  by_cases h : c
  · simp only [h, ↓reduceIte]; exact ha h
  · simp only [h, ↓reduceIte]; exact hb h

-- Needs about 500k heartbeats (2026-10-24); the bound leaves twice that.
set_option maxHeartbeats 1000000 in
/-- The storage phase changes gas only by billing charges, so any property of
the counter that billing preserves holds after it. -/
theorem prepareStorageCallAux_gas (P : GasCounter → Prop) (name : String)
    (before : HostStore NearState) (args : List Value) (hP : P before.host.gas)
    (hbill : ∀ (ns : NearState) (charges : List Charge), P ns.gas → P (applyCharges ns charges).1.gas) :
    P (prepareStorageCallAux name before args).1.host.gas := by
  unfold prepareStorageCallAux
  simp only [Id.run, pure]
  by_cases hname : ["storage_read", "storage_has_key", "storage_write", "storage_remove"].contains name = true
  · simp only [hname, ↓reduceIte]
    cases hacc : before.host.storageAccounting with
    | none => exact hP
    | some initial =>
      dsimp only
      rcases hk : getMemOrReg before (argU64 args 1) (argU64 args 0) with _ | key
      · exact hP
      · dsimp only
        rcases hr : Near.TrieOverlay.getReference initial
            (Near.TrieOverlay.contractKey before.host.context.currentAccountId key)
            (name == "storage_write" || name == "storage_remove" || before.host.storageReadsFromTrie)
          with msg | ⟨looked, pointer⟩
        · dsimp only
          rcases before.host.config.maxStorageKeyLen with _ | limit
          all_goals dsimp only
          all_goals repeat' (first | exact hP | (refine gas_ite ?_ ?_ <;> intro _))
        · dsimp only
          rcases before.host.config.maxStorageKeyLen with _ | limit
          all_goals dsimp only
          all_goals rcases pointer with _ | ptr
          all_goals (try dsimp only)
          all_goals repeat' (first | exact hP | (refine gas_ite ?_ ?_ <;> intro _) | apply hbill)
          all_goals (try (rcases getMemOrReg before (argU64 args 3) (argU64 args 2) with _ | value))
          all_goals (try dsimp only)
          all_goals repeat' (first | exact hP | apply hbill)
          all_goals rcases Near.TrieOverlay.dereference looked ptr with msg | ⟨fetched, stored⟩
          all_goals (try dsimp only)
          all_goals repeat' (first | exact hP | (refine gas_ite ?_ ?_ <;> intro _) | apply hbill)
  · simp only [hname, Bool.false_eq_true, ↓reduceIte]; exact hP

/-- Expose only the fields the external storage phase may change. On success
its local burns cannot alter prepaid promise obligations or call gas limits. -/
def prepareStorageCall (name : String) (before : HostStore NearState) (args : List Value) :
    HostStore NearState × Option FunctionCallError :=
  let (after, error) := prepareStorageCallAux name before args
  ({ before with host := { before.host with
      storageAccounting := after.host.storageAccounting
      gas := { before.host.gas with
        burnt := after.host.gas.burnt
        promises := if error.isNone then before.host.gas.promises else after.host.gas.promises }
      gasProfile := after.host.gasProfile } }, error)

/-- The storage phase only raises burnt gas, within the call's limits. -/
theorem prepareStorageCall_floor {b prepaid maxBurnt : Nat} (name : String) (st : HostStore NearState)
    (args : List Value) (h : st.host.gas.Floor b prepaid maxBurnt) :
    (prepareStorageCall name st args).1.host.gas.Floor b prepaid maxBurnt := by
  have ha := prepareStorageCallAux_gas (GasCounter.Floor b prepaid maxBurnt) name st args h
    (fun ns charges hns => applyCharges_floor ns charges hns)
  obtain ⟨hb, hm, hp, _, _⟩ := ha
  exact ⟨hb, hm, hp, h.2.2.2.1, h.2.2.2.2⟩

@[simp] theorem prepareStorageCall_promises (name : String) (st : HostStore NearState) (args : List Value) :
    (prepareStorageCall name st args).1.host.promises = st.host.promises := rfl

theorem prepareStorageCall_success_promisesGas (name : String) (st : HostStore NearState) (args : List Value)
    (h : (prepareStorageCall name st args).2 = none) :
    (prepareStorageCall name st args).1.host.gas.promises = st.host.gas.promises := by
  change (if (prepareStorageCall name st args).2.isNone then st.host.gas.promises else _) = _
  rw [h]
  rfl

/-- Nonstorage hosts pass straight through the external phase. -/
@[simp] theorem prepareStorageCall_other (name : String) (st : HostStore NearState) (args : List Value)
    (h : ["storage_read", "storage_has_key", "storage_write", "storage_remove"].contains name = false) :
    prepareStorageCall name st args = (st, none) := by
  have ha : prepareStorageCallAux name st args = (st, none) := by
    simp only [prepareStorageCallAux, h, Bool.false_eq_true, ↓reduceIte]
    rfl
  simp only [prepareStorageCall, ha]
  rfl

/-- Invoke the functional host only after the external storage phase succeeds. -/
def invokeStorageCall (extra : Nat) (name : String) (fn : NearHostFn NearState)
    (before : HostStore NearState) (args : List Value) : HostResult NearState :=
  let (after, error) := prepareStorageCall name before args
  match error with
  | some (.hostError error) => trapWith after error
  | some (.executionIssue issue) =>
    .Trap { after with host := { after.host with lastExecutionIssue := some issue } } issue.message
  | some error => .Trap after error.message
  | none => finishMeteredCall extra name after args (fn.invoke after args)

/-- Wrap a functional host function with its gas and storage-usage rules. -/
def metered (extraBytes : Nat) (name : String) (fn : NearHostFn NearState) : NearHostFn NearState :=
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
        | none => invokeStorageCall extraBytes name fn st1 args }

-- nearcore divergence: curve, yield and global-deploy host
-- functions are rejected as execution issues instead of being executed.
/-- These host operations require semantics not supplied by `VMContext`.
Reject them on invocation instead of using the functional host's placeholder
crypto, validator, or yield implementations. Merely importing one is allowed. -/
def unsupportedRuntimeHost (name : String) : Bool :=
  ["promise_yield_create", "promise_yield_resume",
   "alt_bn128_g1_multiexp", "alt_bn128_g1_sum", "alt_bn128_pairing_check",
   "bls12381_g1_multiexp", "bls12381_g2_multiexp", "bls12381_map_fp_to_g1",
   "bls12381_map_fp2_to_g2", "bls12381_p1_decompress", "bls12381_p2_decompress",
   "bls12381_p1_sum", "bls12381_p2_sum", "bls12381_pairing_check",
   "promise_batch_action_deploy_global_contract",
   "promise_batch_action_deploy_global_contract_by_account_id"].contains name

/-- The name a host is metered under. nearcore's weighted function call is the
plain one plus a weight: same charges, checks and errors. -/
def meteringName (name : String) : String :=
  if name == "promise_batch_action_function_call_weight" then "promise_batch_action_function_call"
  else name

/-- The metered host table: `nearHostFns` with gas, plus the structured
panics and the `gas` import. -/
def meteredHostFns (cfg : RuntimeConfig) : List (ImportDecl × NearHostFn NearState) :=
  let extra := cfg.fees.numExtraBytesRecord
  let swap (decl : ImportDecl) (fn : NearHostFn NearState) : NearHostFn NearState :=
    if unsupportedRuntimeHost decl.name then
      { fn with invoke := fun st _ => trapWith st (.unsupported decl.name) }
    else match decl.name with
    | "panic" => panicMetered
    | "panic_utf8" => panicUtf8Metered
    | "abort" => abortMetered
    | _ => fn
  (nearHostFns.map fun (decl, fn) => (decl, metered extra (meteringName decl.name) (swap decl fn)))
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
  resolveMeteredImports cfg m.importDecls

end Wasm.Near
