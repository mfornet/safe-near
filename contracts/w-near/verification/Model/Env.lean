import Model.Types

/-!
# Call environment and runtime configuration

Everything a single method execution reads from the host, plus the runtime
parameters the contract's behaviour depends on. The contract's own NEAR
balance and in-flight receipts are *not* here: they belong to the chain-level
model built on top of this one.
-/

namespace WNear

/-- Runtime parameters the contract observes. -/
@[blueprint "def:config"
  (statement := /-- The runtime parameters the contract observes: the extra bytes charged per storage record (40 on mainnet). The measured storage usage of one account entry is $(1 + 4 + 64) + 16 + \mathit{extra}$ bytes. -/)]
structure Config where
  /-- Bytes the runtime charges per storage record on top of key and value
  (`storage_num_extra_bytes_record`, 40 on mainnet). -/
  extraBytesPerRecord : Nat

/-- Storage charged for one `accounts` entry whose account id has `len` bytes:
key `b"a" ++ borsh(String)` (1 + 4 + len), value `borsh(u128)` (16), record overhead. -/
def Config.accountEntryBytes (cfg : Config) (len : Nat) : Nat :=
  (1 + 4 + len) + 16 + cfg.extraBytesPerRecord

/-- What `FungibleToken::new` measures: the entry of a 64-byte account id
(125 bytes on mainnet, i.e. a 0.00125 NEAR registration fee). -/
def Config.measuredAccountStorageUsage (cfg : Config) : Nat :=
  cfg.accountEntryBytes maxAccountIdBytes

/-- The result of the single promise a callback depends on, after the contract
parsed it. `successful none` is a successful call whose return value did not
parse as a JSON `U128`. -/
inductive PromiseResult
  | notReady
  | failed
  | successful (unused : Option Nat)
  deriving DecidableEq, Repr

/-- Host context of one method execution. -/
@[blueprint "def:env"
  (statement := /-- The host context of one execution: current account, predecessor, attached deposit, prepaid gas and, in callbacks, the result of the awaited promise (failed, or successful with the return value parsed as a JSON \texttt{U128} when it parses). -/)]
structure Env where
  /-- `env::current_account_id()` (`wrap.near`). -/
  currentAccount : AccountId
  /-- `env::predecessor_account_id()`. -/
  predecessor : AccountId
  /-- `env::attached_deposit()`, yoctoNEAR. -/
  attachedDeposit : Nat
  /-- `env::prepaid_gas()`. -/
  prepaidGas : Nat
  /-- `env::promise_result(0)`; `none` outside callbacks. -/
  promiseResult : Option PromiseResult

end WNear
