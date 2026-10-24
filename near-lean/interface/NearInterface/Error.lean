/-!
# Function-call errors

The error taxonomy of `near_vm_runner` (`FunctionCallError` and
`HostError`), restricted to what the Lean runtime can produce. Names and
messages follow nearcore so replay diffs and the Rust shim can map them
directly.
-/

namespace Wasm.Near

/-- A limitation of the executable model, never an on-chain contract failure. -/
inductive ExecutionIssue
  | fuelExhausted
  | unsupportedHost (name : String)
  | unsupportedAction (name : String)
  | interpreterError (message : String)
  | storageAccounting (message : String)
  deriving Repr, BEq, Inhabited

def ExecutionIssue.message : ExecutionIssue → String
  | .fuelExhausted => "Interpreter fuel exhausted; execution is incomplete"
  | .unsupportedHost name => s!"Unsupported host semantics: {name}"
  | .unsupportedAction name => s!"Unsupported action semantics: {name}"
  | .interpreterError message => s!"Interpreter error: {message}"
  | .storageAccounting message => s!"Storage accounting error: {message}"

/-- `near_vm_runner::logic::HostError`. -/
inductive HostError
  | badUTF8
  | badUTF16
  | gasExceeded
  | gasLimitExceeded
  | balanceExceeded
  | emptyMethodName
  | invalidMethodName
  | guestPanic (panicMsg : String)
  | integerOverflow
  | invalidPromiseIndex (promiseIdx : Nat)
  | cannotAppendActionToJointPromise
  | cannotReturnJointPromise
  | invalidPromiseResultIndex (resultIdx : Nat)
  | invalidRegisterId (registerId : Nat)
  | iteratorWasInvalidated (iteratorIndex : Nat)
  | memoryAccessViolation
  | invalidReceiptIndex (receiptIndex : Nat)
  | invalidIteratorIndex (iteratorIndex : Nat)
  | invalidAccountId
  | invalidPublicKey
  | tooManyPromises (numberOfPromises limit : Nat)
  | tooManyInputDataDependencies (dependencies limit : Nat)
  | returnedValueLengthExceeded (length limit : Nat)
  | contractSizeExceeded (size limit : Nat)
  | keyLengthExceeded (length limit : Nat)
  | valueLengthExceeded (length limit : Nat)
  | totalLogLengthExceeded (length limit : Nat)
  | numberOfLogsExceeded (limit : Nat)
  | numberPromisesExceeded (numberOfPromises limit : Nat)
  | numberInputDataDependenciesExceeded (dependencies limit : Nat)
  | prohibitedInView (methodName : String)
  | deprecated (methodName : String)
  | unsupported (methodName : String)
  | contractCodeHashMalformed
  deriving Repr, BEq, Inhabited

def HostError.message : HostError → String
  | .badUTF8 => "String encoding is bad UTF-8 sequence."
  | .badUTF16 => "String encoding is bad UTF-16 sequence."
  | .gasExceeded => "Exceeded the prepaid gas."
  | .gasLimitExceeded => "Exceeded the maximum amount of gas allowed to burn per contract."
  | .balanceExceeded => "Exceeded the account balance."
  | .emptyMethodName => "Tried to call an empty method name."
  | .invalidMethodName => "VM Logic returned an invalid method name"
  | .guestPanic msg => s!"Smart contract panicked: {msg}"
  | .integerOverflow => "Integer overflow."
  | .invalidPromiseIndex i => s!"{i} does not correspond to existing promises"
  | .cannotAppendActionToJointPromise => "Actions can only be appended to non-joint promise."
  | .cannotReturnJointPromise => "Returning joint promise is currently prohibited."
  | .invalidPromiseResultIndex i => s!"Accessed invalid promise result index: {i}"
  | .invalidRegisterId i => s!"Accessed invalid register id: {i}"
  | .iteratorWasInvalidated i => s!"Iterator {i} was invalidated after its creation by performing a mutable operation on trie"
  | .memoryAccessViolation => "Accessed memory outside the bounds."
  | .invalidReceiptIndex i => s!"VM Logic returned an invalid receipt index: {i}"
  | .invalidIteratorIndex i => s!"Iterator index {i} does not exist"
  | .invalidPublicKey => "VM Logic provided an invalid public key"
  | .invalidAccountId => "VM Logic returned an invalid account id"
  | .tooManyPromises n l => s!"Number of promises within a FunctionCall {n} exceeds the limit {l}"
  | .tooManyInputDataDependencies n l => s!"Number of input data dependencies {n} exceeds the limit {l}"
  | .returnedValueLengthExceeded n l => s!"The length of a returned value {n} exceeds the limit {l}"
  | .contractSizeExceeded n l => s!"The size of a contract code in DeployContract action {n} exceeds the limit {l}"
  | .keyLengthExceeded n l => s!"The length of a storage key {n} exceeds the limit {l}"
  | .valueLengthExceeded n l => s!"The length of a storage value {n} exceeds the limit {l}"
  | .totalLogLengthExceeded n l => s!"The length of a log message {n} exceeds the limit {l}"
  | .numberOfLogsExceeded l => s!"The number of logs will exceed the limit {l}"
  | .numberPromisesExceeded n l => s!"The number of promises within a FunctionCall {n} exceeds the limit {l}"
  | .numberInputDataDependenciesExceeded n l => s!"The number of input data dependencies {n} exceeds the limit {l}"
  | .prohibitedInView m => s!"{m} is not allowed in view calls"
  | .deprecated m => s!"Attempted to call deprecated host function {m}"
  | .unsupported m => s!"Attempted to call unsupported host function {m}"
  | .contractCodeHashMalformed => "contract code hash is malformed"

/-- Why a Wasm execution trapped (`near_vm_runner::logic::errors::WasmTrap`). -/
inductive WasmTrap
  | unreachable
  | incorrectCallIndirectSignature
  | memoryOutOfBounds
  | callIndirectOOB
  | illegalArithmetic
  | misalignedAtomicAccess
  | indirectCallToNull
  | stackOverflow
  | genericTrap
  deriving Repr, BEq, Inhabited

def WasmTrap.message : WasmTrap → String
  | .unreachable => "An `unreachable` opcode was executed."
  | .incorrectCallIndirectSignature => "Call indirect incorrect signature trap."
  | .memoryOutOfBounds => "Memory out of bounds trap."
  | .callIndirectOOB => "Call indirect out of bounds trap."
  | .illegalArithmetic => "An arithmetic exception, e.g. divided by zero."
  | .misalignedAtomicAccess => "Misaligned atomic access trap."
  | .indirectCallToNull => "Indirect call to null."
  | .stackOverflow => "Stack overflow."
  | .genericTrap => "Generic trap."

/-- `near_vm_runner::logic::errors::MethodResolveError`. -/
inductive MethodResolveError
  | methodEmptyName
  | methodNotFound
  | methodInvalidSignature
  deriving Repr, BEq, Inhabited

/-- `near_vm_runner::logic::errors::FunctionCallError`. -/
inductive FunctionCallError
  | compilationError (msg : String)
  | linkError (msg : String)
  | methodResolveError (e : MethodResolveError)
  | wasmTrap (t : WasmTrap)
  | hostError (e : HostError)
  /-- The interpreter itself failed (ran out of fuel or hit an internal error).
  Never produced by nearcore; a replay mismatch if it ever shows up. -/
  | internal (msg : String)
  /-- Execution stopped without establishing a protocol outcome. -/
  | executionIssue (issue : ExecutionIssue)
  deriving Repr, BEq, Inhabited

def FunctionCallError.message : FunctionCallError → String
  | .compilationError m => s!"CompilationError({m})"
  | .linkError m => s!"LinkError({m})"
  | .methodResolveError .methodEmptyName => "MethodEmptyName"
  | .methodResolveError .methodNotFound => "MethodNotFound"
  | .methodResolveError .methodInvalidSignature => "MethodInvalidSignature"
  | .wasmTrap t => s!"WebAssembly trap: {t.message}"
  | .hostError e => e.message
  | .internal m => s!"Internal({m})"
  | .executionIssue issue => issue.message

/-- Model limitations must be propagated separately from protocol failures.
Legacy internal errors and unsupported host traps are included so neither
can be mistaken for a contract panic. -/
def FunctionCallError.issue? : FunctionCallError → Option ExecutionIssue
  | .executionIssue issue => some issue
  | .internal message => some (.interpreterError message)
  | .hostError (.unsupported name) => some (.unsupportedHost name)
  | _ => none

/-- Errors that nearcore treats as "out of gas" for the purpose of the
refinement hypothesis. -/
def FunctionCallError.isOutOfGas : FunctionCallError → Bool
  | .hostError .gasExceeded | .hostError .gasLimitExceeded => true
  | _ => false

end Wasm.Near
