import NearVM.Interp
import NearVM.Error
import NearVM.Gas
import NearVM.TrieOverlay
import NearInterface.Raw

/-!
# NEAR host state (`α := NearState`)

The interpreter threads an opaque `host : α` slot through `HostStore α`; host
imports are the only code that inspects it. This module instantiates that
slot for the **NEAR Protocol** smart-contract host environment.

`NearState` is the part of the NEAR runtime a single contract call can
observe and mutate:

* `storage`   — the contract's storage trie, modelled as a *pure function*
  `key → Option value` (mirroring `Mem.bytes : Nat → UInt8`). This is the
  "projection of NEAR state" specs reason about before/after a call; the
  function model supports `∀ key` (frame) reasoning directly, and NEAR's
  storage-iterator host functions are deprecated so contracts can't
  enumerate keys anyway — only ghost specs do, via quantifiers.
* `registers` — the NEAR register ABI scratch buffers (`id → bytes`). Host
  functions that "return" variable-length data write it to a register; the
  contract then copies it into linear memory via `read_register`.
* `context`   — immutable call context (account ids, input bytes, deposit,
  and whether the call is a view call).
* `returnData` / `logs` — outputs produced via `value_return` / logging.
* `promiseResults` / `promises` — callback inputs and promise handles for
  proof-visible cross-contract APIs.
* `config`    — optional size limits that make unsupported oversize behavior
  trap instead of silently entering proofs.

Promise creation/action modelling is deliberately incremental: callback
result access and returned-promise selection are concrete; emitted receipt
actions are added in `Env.lean` as the host API grows.

The host-function semantics live in `NearVM/Host.lean`; this file is
just the state shape plus the pure helpers those functions are built from.
-/

namespace Wasm

/-- `2^64 - 1`, the NEAR register/length sentinel. Used by host functions
that read an argument through `getMemOrReg`: a length field equal to this
value means "the pointer is a register id, take the bytes already in that
register" rather than "read this many bytes of linear memory". When used
as an output `register_id`, the same value means "discard the output". -/
def u64Max : UInt64 := 0xFFFFFFFFFFFFFFFF

/-- Immutable per-call NEAR context. Account ids and `input` are raw byte
strings (NEAR account ids are UTF-8; contract input is opaque bytes,
conventionally JSON or Borsh). `attachedDeposit` is a yoctoNEAR `u128`,
written to memory as 16 little-endian bytes by `attached_deposit`. -/
structure NearContext where
  currentAccountId     : List UInt8 := []
  predecessorAccountId : List UInt8 := []
  signerAccountId      : List UInt8 := []
  signerAccountPk      : List UInt8 := []
  /-- Raw call input (method arguments). Read into a register by `input`. -/
  input                : List UInt8 := []
  /-- Whether this execution is a view call. Some host APIs trap in view mode. -/
  isView               : Bool := false
  blockIndex           : UInt64 := 0
  blockTimestamp       : UInt64 := 0
  epochHeight          : UInt64 := 0
  storageUsage         : UInt64 := 0
  accountBalance       : Nat := 0
  accountLockedBalance : Nat := 0
  /-- Attached deposit in yoctoNEAR (`u128`). -/
  attachedDeposit      : Nat := 0
  prepaidGas           : UInt64 := 0
  usedGas              : UInt64 := 0
  validatorStake       : List UInt8 → Nat := fun _ => 0
  validatorTotalStake  : Nat := 0
deriving Inhabited

/-- Optional NEAR host limits. `none` means the reference model leaves that
limit unconstrained, which keeps existing concrete examples small and easy to
compute while allowing fidelity checks to opt in to nearcore-style traps. -/
structure NearConfig where
  /-- RuntimeExt charges old-value bytes; MockedExternal does not. Trie-node costs are separate. -/
  chargeStorageValueAccess : Bool := false
  /-- Runtime external action methods are UTF-8; VM mocks may keep opaque bytes. -/
  validateActionMethodUtf8 : Bool := true
  oneYoctoOnPromise : Bool := false
  ethImplicitAccounts : Bool := false
  maxRegisterLen     : Option Nat := none
  maxReturnLen       : Option Nat := none
  maxLogLen          : Option Nat := none
  maxNumberLogs      : Option Nat := none
  maxStorageKeyLen   : Option Nat := none
  maxStorageValueLen : Option Nat := none
  maxInputDataDependencies : Option Nat := none
  maxPromises : Option Nat := none
  validAccountId     : List UInt8 → Bool := fun _ => true
  validPublicKey     : List UInt8 → Bool := fun _ => true
deriving Inhabited

/-- Promise handle allocated during the current execution. A batch promise
emits actions toward an account; a callback batch depends on an earlier
promise; a joint promise waits for several promises and cannot accept
actions. -/
inductive NearPromise where
  | batch (accountId : List UInt8) (actions : List PromiseAction)
  | callback (base : Nat) (accountId : List UInt8) (actions : List PromiseAction)
  | and (dependencies : List Nat)
  | yielded (methodName args : List UInt8) (gas weight : UInt64) (dataId : List UInt8)
deriving Inhabited, BEq

/-- Snapshot iterator over finite storage keys. The primary storage model
remains a function; this is the finite witness needed by deprecated NEAR
iterator host functions. -/
structure StorageIterator where
  entries : List (List UInt8 × List UInt8) := []
  pos     : Nat := 0
deriving Inhabited, BEq

/-- The NEAR host state threaded as `HostStore.host`. -/
structure NearState where
  /-- Storage trie projection: `key ↦ value`, `none` when absent. -/
  storage    : List UInt8 → Option (List UInt8) := fun _ => none
  /-- Optional full chunk trie and shared accounting cache. Contract storage remains
  the functional projection; disagreement is an explicit model execution issue. -/
  storageAccounting : Option _root_.Near.TrieOverlay.State := none
  /-- Reads/has-key use flat storage by default; writes/removes always traverse the trie. -/
  storageReadsFromTrie : Bool := false
  /-- Finite key support for deprecated storage iterator APIs. -/
  storageKeys : List (List UInt8) := []
  iterators  : Nat → Option StorageIterator := fun _ => none
  nextIteratorId : Nat := 0
  /-- Register ABI scratch buffers: `id ↦ bytes`, `none` when unset. -/
  registers  : Nat → Option (List UInt8) := fun _ => none
  context    : NearContext := {}
  /-- Attempted one-yocto grants; retained as diagnostics on VM failure. -/
  subsidizedAmount : Nat := 0
  /-- Value set by `value_return` (the call's result), if any. -/
  returnData : Option (List UInt8) := none
  /-- Log lines emitted during the call, newest last. -/
  logs       : List (List UInt8) := []
  /-- Promise results available to callback executions. -/
  promiseResults : List PromiseResult := []
  /-- Promises created during this execution. -/
  promises   : List NearPromise := []
  /-- Weighted function-call actions, in call order: (promise index, action
  index, weight), recorded only for a positive weight. After a successful call
  the unused prepaid gas is split among them (nearcore's `distribute_gas`). -/
  gasWeights : List (Nat × Nat × Nat) := []
  /-- Promise selected as this call's return value by `promise_return`. -/
  returnedPromise : Option Nat := none
  /-- Successful `promise_yield_resume` payloads, newest last. -/
  yieldResumes : List (List UInt8 × List UInt8) := []
  config     : NearConfig := {}
  /-- The cryptographic oracles supplied with the call (`HostCrypto`). -/
  crypto     : HostCrypto := {}
  randomSeed : List UInt8 := []
  /-- Gas counter of this execution; charged by the metered host functions
  (`NearVM.Metered`) and by the step loop (`NearVM.Run`). -/
  gas        : Near.GasCounter := {}
  gasProfile : Near.GasProfile := {}
  /-- Host-function gas costs (`ExtCosts`) of the protocol version in force. -/
  extCosts   : Near.ExtCosts := {}
  /-- Action fees charged when promises are created. -/
  fees       : Near.ActionFees := {}
  /-- Accounts that receive this call's return value as data receipts
  (`output_data_receivers`); each costs data-receipt bytes on `value_return`. -/
  outputDataReceivers : List (List UInt8) := []
  /-- The structured error behind the last host trap, read by the runner. -/
  lastError  : Option Near.HostError := none
  lastExecutionIssue : Option Near.ExecutionIssue := none
  yieldCreateToken : List UInt8 → List UInt8 → UInt64 → UInt64 → List UInt8 :=
    fun _ _ _ _ => []
  altBn128G1Multiexp : List UInt8 → List UInt8 := fun _ => []
  altBn128G1Sum : List UInt8 → List UInt8 := fun _ => []
  altBn128PairingCheck : List UInt8 → UInt64 := fun _ => 0
  bls12381G1Multiexp : List UInt8 → UInt64 × List UInt8 := fun _ => (1, [])
  bls12381G2Multiexp : List UInt8 → UInt64 × List UInt8 := fun _ => (1, [])
  bls12381MapFpToG1 : List UInt8 → UInt64 × List UInt8 := fun _ => (1, [])
  bls12381MapFp2ToG2 : List UInt8 → UInt64 × List UInt8 := fun _ => (1, [])
  bls12381P1Decompress : List UInt8 → UInt64 × List UInt8 := fun _ => (1, [])
  bls12381P2Decompress : List UInt8 → UInt64 × List UInt8 := fun _ => (1, [])
  bls12381P1Sum : List UInt8 → UInt64 × List UInt8 := fun _ => (1, [])
  bls12381P2Sum : List UInt8 → UInt64 × List UInt8 := fun _ => (1, [])
  bls12381PairingCheck : List UInt8 → UInt64 := fun _ => 0
deriving Inhabited

namespace NearState

/-- Set register `id` to `data` (creating or overwriting). -/
def setRegister (ns : NearState) (id : Nat) (data : List UInt8) : NearState :=
  { ns with registers := fun i => if i = id then some data else ns.registers i }

/-- Insert/overwrite `key ↦ val` in storage. -/
def setStorage (ns : NearState) (key val : List UInt8) : NearState :=
  { ns with
    storage := fun k => if k = key then some val else ns.storage k
    storageKeys := if ns.storageKeys.contains key then ns.storageKeys else ns.storageKeys ++ [key] }

/-- Remove `key` from storage. -/
def removeStorage (ns : NearState) (key : List UInt8) : NearState :=
  { ns with
    storage := fun k => if k = key then none else ns.storage k
    storageKeys := ns.storageKeys.filter (fun k => k != key) }

def invalidateIterators (ns : NearState) : NearState :=
  { ns with iterators := fun _ => none }

def setIterator (ns : NearState) (id : Nat) (it : StorageIterator) : NearState :=
  { ns with
    iterators := fun i => if i = id then some it else ns.iterators i
    nextIteratorId := max ns.nextIteratorId (id + 1) }

/-- Return selectors share one logical slot: the last successful selection wins. -/
def selectReturnValue (ns : NearState) (bytes : List UInt8) : NearState :=
  { ns with returnData := some bytes, returnedPromise := none }

def selectReturnPromise (ns : NearState) (index : Nat) : NearState :=
  { ns with returnedPromise := some index, returnData := none }

theorem selectReturnValue_clears_promise (ns : NearState) (bytes : List UInt8) :
    (ns.selectReturnValue bytes).returnedPromise = none := rfl

theorem selectReturnPromise_clears_value (ns : NearState) (index : Nat) :
    (ns.selectReturnPromise index).returnData = none := rfl

theorem selectReturnValue_after_promise (ns : NearState) (index : Nat) (bytes : List UInt8) :
    (ns.selectReturnPromise index).selectReturnValue bytes = ns.selectReturnValue bytes := rfl

theorem selectReturnPromise_after_value (ns : NearState) (bytes : List UInt8) (index : Nat) :
    (ns.selectReturnValue bytes).selectReturnPromise index = ns.selectReturnPromise index := rfl

end NearState

/-- The NEAR `get_memory_or_register` input convention. For an input
`(ptr, len)` pair: when `len = u64Max`, `ptr` is a *register id* and the
bytes are taken from that register (`none` if the register is unset, which
the caller turns into a trap); otherwise it reads `len` bytes of linear
memory starting at `ptr`, returning `none` when the range exceeds guest
memory. Used uniformly by `storage_*` (keys/values) and `value_return`. -/
def getMemOrReg (st : HostStore NearState) (ptr len : UInt64) : Option (List UInt8) :=
  if len = u64Max then st.host.registers ptr.toNat
  else if ptr.toNat + len.toNat > st.mem.size * 65536 then none
  else some (st.mem.readList ptr.toNat len.toNat)

end Wasm
