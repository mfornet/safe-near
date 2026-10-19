import NearRuntime.State

/-!
# Fees

`runtime/src/config.rs`: the gas a transaction or receipt burns when sent,
the gas its execution will burn, and the gas it carries for function calls.
All of it comes from the `RuntimeConfig` loaded from nearcore's own tables.
-/

namespace Near

open Wasm.Near

/-- Bytes of a public key plus an access key, as stored for storage accounting. -/
def accessKeyStorageBytes (pk : PublicKey) (k : AccessKey) : Nat :=
  pk.length + 8 + (match k.permission with
    | .fullAccess => 1
    | .functionCall _ receiver methods => 1 + 17 + 4 + receiver.length + 4 + (methods.map (·.utf8ByteSize + 4)).sum)

/-- 64 lowercase hex characters: an implicit (NEAR) account. -/
def isImplicitAccount (id : AccountId) : Bool :=
  id.length == 64 && id.toList.all fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')

private def hexNibble (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else none

private def decodeHex : List Char → Option Bytes
  | [] => some []
  | hi :: lo :: rest => do
    let h ← hexNibble hi
    let l ← hexNibble lo
    let tail ← decodeHex rest
    pure (UInt8.ofNat (16 * h + l) :: tail)
  | _ => none

/-- The Ed25519 key encoded by a NEAR implicit account: curve tag 0 followed
by the 32 decoded bytes, rather than the 64 ASCII hexadecimal characters. -/
def implicitPublicKey? (id : AccountId) : Option PublicKey :=
  if isImplicitAccount id then (decodeHex id.toList).map (0 :: ·) else none

/-- New keys start in the block's nonce range (`access_keys.rs` in the pinned
reference). Block zero is a synthetic fixture; real execution starts above it. -/
def initialNonce (blockHeight : Nat) : Nat := (blockHeight - 1) * 1_000_000

namespace Fees

/-- Send fee of one action (`total_send_fees` summand). -/
def send (f : ActionFees) (sir : Bool) (receiver : AccountId) : Action → Nat
  | .createAccount => f.createAccount.send sir
  | .deployContract code => f.deployContractBase.send sir + f.deployContractByte.send sir * code.size
  | .functionCall m args _ _ =>
    f.functionCallBase.send sir + f.functionCallByte.send sir * (m.utf8ByteSize + args.length)
  | .transfer _ =>
    f.transfer.send sir + (if isImplicitAccount receiver then
      f.createAccount.send sir + f.addFullAccessKey.send sir else 0)
  | .stake _ _ => f.stake.send sir
  | .addKey _ k =>
    match k.permission with
    | .fullAccess => f.addFullAccessKey.send sir
    | .functionCall _ _ methods =>
      f.addFunctionCallKeyBase.send sir
        + f.addFunctionCallKeyByte.send sir * (methods.map fun m => m.utf8ByteSize + 1).sum
  | .deleteKey _ => f.deleteKey.send sir
  | .deleteAccount _ => f.deleteAccount.send sir

/-- Execution fee of one action (`exec_fee`). -/
def exec (f : ActionFees) (receiver : AccountId) : Action → Nat
  | .createAccount => f.createAccount.execution
  | .deployContract code => f.deployContractBase.execution + f.deployContractByte.execution * code.size
  | .functionCall m args _ _ =>
    f.functionCallBase.execution + f.functionCallByte.execution * (m.utf8ByteSize + args.length)
  | .transfer _ =>
    f.transfer.execution + (if isImplicitAccount receiver then
      f.createAccount.execution + f.addFullAccessKey.execution else 0)
  | .stake _ _ => f.stake.execution
  | .addKey _ k =>
    match k.permission with
    | .fullAccess => f.addFullAccessKey.execution
    | .functionCall _ _ methods =>
      f.addFunctionCallKeyBase.execution
        + f.addFunctionCallKeyByte.execution * (methods.map fun m => m.utf8ByteSize + 1).sum
  | .deleteKey _ => f.deleteKey.execution
  | .deleteAccount _ => f.deleteAccount.execution

def totalSend (f : ActionFees) (sir : Bool) (receiver : AccountId) (actions : List Action) : Nat :=
  (actions.map (send f sir receiver)).sum

def totalExec (f : ActionFees) (receiver : AccountId) (actions : List Action) : Nat :=
  (actions.map (exec f receiver)).sum

def totalPrepaid (actions : List Action) : Nat := (actions.map Action.attachedGas).sum

def totalDeposit (actions : List Action) : Nat := (actions.map Action.deposit).sum

/-- The cost of a transaction (`tx_cost`): gas burnt now, gas prepaid for
the receipt, and the total yoctoNEAR charged to the signer. -/
structure TxCost where
  gasBurnt : Nat
  gasRemaining : Nat
  receiptGasPrice : Nat
  total : Nat

def txCost (cfg : RuntimeConfig) (gasPrice : Nat) (signer receiver : AccountId)
    (actions : List Action) : TxCost :=
  let f := cfg.fees.actionFees
  let sir := signer == receiver
  let gasBurnt := f.newActionReceipt.send sir + totalSend f sir receiver actions
  let gasRemaining := f.newActionReceipt.execution + totalExec f receiver actions + totalPrepaid actions
  let receiptGasPrice := max gasPrice cfg.minGasPurchasePrice
  { gasBurnt, gasRemaining, receiptGasPrice,
    total := gasBurnt * gasPrice + gasRemaining * receiptGasPrice + totalDeposit actions }

end Fees

end Near
