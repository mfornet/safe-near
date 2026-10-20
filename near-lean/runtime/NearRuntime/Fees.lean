import Mathlib.Tactic.Linarith
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
    | .functionCall allowance receiver methods =>
      1 + (match allowance with | none => 1 | some _ => 17) + 4 + receiver.utf8ByteSize + 4
        + (methods.map (·.utf8ByteSize + 4)).sum)

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
def send (f : ActionFees) (ethEnabled : Bool) (sir : Bool) (receiver : AccountId) : Action → Nat
  | .createAccount => f.createAccount.send sir
  | .deployContract code => f.deployContractBase.send sir + f.deployContractByte.send sir * code.size
  | .functionCall m args _ _ =>
    f.functionCallBase.send sir + f.functionCallByte.send sir * (m.utf8ByteSize + args.length)
  | .transfer _ =>
    (transferFees f ethEnabled receiver.toUTF8.toList).send sir
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
def exec (f : ActionFees) (ethEnabled : Bool) (receiver : AccountId) : Action → Nat
  | .createAccount => f.createAccount.execution
  | .deployContract code => f.deployContractBase.execution + f.deployContractByte.execution * code.size
  | .functionCall m args _ _ =>
    f.functionCallBase.execution + f.functionCallByte.execution * (m.utf8ByteSize + args.length)
  | .transfer _ =>
    (transferFees f ethEnabled receiver.toUTF8.toList).execution
  | .stake _ _ => f.stake.execution
  | .addKey _ k =>
    match k.permission with
    | .fullAccess => f.addFullAccessKey.execution
    | .functionCall _ _ methods =>
      f.addFunctionCallKeyBase.execution
        + f.addFunctionCallKeyByte.execution * (methods.map fun m => m.utf8ByteSize + 1).sum
  | .deleteKey _ => f.deleteKey.execution
  | .deleteAccount _ => f.deleteAccount.execution

def totalSend (f : ActionFees) (ethEnabled : Bool) (sir : Bool) (receiver : AccountId) (actions : List Action) : Nat :=
  (actions.map (send f ethEnabled sir receiver)).sum

def totalExec (f : ActionFees) (ethEnabled : Bool) (receiver : AccountId) (actions : List Action) : Nat :=
  (actions.map (exec f ethEnabled receiver)).sum

def totalPrepaid (actions : List Action) : Nat := (actions.map Action.attachedGas).sum

def totalDeposit (actions : List Action) : Nat := (actions.map Action.deposit).sum

/-- Gas budget carried by an ordinary action receipt. -/
def receiptGasBudget (cfg : RuntimeConfig) (receiver : AccountId) (actions : List Action) : Nat :=
  cfg.fees.actionFees.newActionReceipt.execution + totalExec cfg.fees.actionFees cfg.wasm.ethImplicitAccounts receiver actions + totalPrepaid actions

/-- Funds carried by a receipt: deposits plus gas purchased for future execution.
System refunds carry only their transfer balance; data receipts carry no funds. -/
def receiptFunds (cfg : RuntimeConfig) (r : Receipt) : Nat :=
  match r.receipt with
  | .action a => totalDeposit a.actions +
      (if r.isRefund then 0 else receiptGasBudget cfg r.receiverId a.actions * a.gasPrice)
  | .data _ => 0

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
  let gasBurnt := f.newActionReceipt.send sir + totalSend f cfg.wasm.ethImplicitAccounts sir receiver actions
  let gasRemaining := receiptGasBudget cfg receiver actions
  let receiptGasPrice := max gasPrice cfg.minGasPurchasePrice
  { gasBurnt, gasRemaining, receiptGasPrice,
    total := gasBurnt * gasPrice + gasRemaining * receiptGasPrice + totalDeposit actions }

/-- Token settlement from pinned nearcore's `refund_unspent_gas_and_deposits`.
Gas purchase price is carried by the receipt; burn price comes from this block. -/
structure GasSettlement where
  burnPrice : Nat
  refund : Nat
  tokensBurnt : Nat
  priceDeficit : Nat
  priceSurplus : Nat
  refundPenalty : Nat
  creationCharge : Nat
  deriving Repr, BEq

def settleGas (cfg : RuntimeConfig) (purchasePrice currentPrice prepaid used burnt : Nat)
    (createdAccount : Bool) : GasSettlement :=
  let burnPrice := if cfg.accountCostIncrease then min purchasePrice currentPrice else currentPrice
  let grossRefund := prepaid - used
  let (num, den) := cfg.fees.gasRefundPenalty
  let penaltyGas := min grossRefund (max (grossRefund * num / den) cfg.fees.minGasRefundPenalty)
  let penaltyPrice := if cfg.accountCostIncrease then burnPrice else purchasePrice
  let refundPenalty := penaltyGas * penaltyPrice
  let priceDeficit := (burnPrice - purchasePrice) * burnt
  let priceSurplus := (purchasePrice - burnPrice) * burnt
  let creationCharge := if cfg.accountCostIncrease && createdAccount then
      min priceSurplus (cfg.accountCreationCharge - cfg.fees.actionFees.createAccount.execution * burnPrice)
    else 0
  let refund := grossRefund * purchasePrice - refundPenalty +
    (if cfg.accountCostIncrease then priceSurplus - creationCharge else 0)
  let tokensBurnt := burnt * burnPrice - priceDeficit +
    (if cfg.accountCostIncrease then 0 else priceSurplus) + refundPenalty + creationCharge
  { burnPrice, refund, tokensBurnt, priceDeficit, priceSurplus, refundPenalty, creationCharge }

/-- A receipt's purchased gas partitions into its refund, burnt tokens and
reserved gas sent onward. Charges and penalties move funds within that partition. -/
theorem gas_settlement_partition (purchase burn prepaid used burnt penalty charge : Nat)
    (hprice : burn ≤ purchase) (hused : used ≤ prepaid) (hburnt : burnt ≤ used)
    (hpenalty : penalty ≤ (prepaid - used) * purchase)
    (hcharge : charge ≤ (purchase - burn) * burnt) :
    ((prepaid - used) * purchase - penalty + ((purchase - burn) * burnt - charge)) +
      (burnt * burn + penalty + charge) + (used - burnt) * purchase = prepaid * purchase := by
  have hr := Nat.sub_add_cancel hused
  have hu := Nat.sub_add_cancel hburnt
  have hp := Nat.sub_add_cancel hprice
  have hgas : (prepaid - used) * purchase + (used - burnt) * purchase + burnt * purchase = prepaid * purchase := by
    nlinarith
  have hsurplus : (purchase - burn) * burnt + burnt * burn = burnt * purchase := by
    nlinarith
  omega

/-- Kernel-checked gas-token conservation for the v85+ settlement algorithm. -/
theorem settleGas_conservation (cfg : RuntimeConfig) (purchase current prepaid used burnt : Nat)
    (created : Bool) (hnew : cfg.accountCostIncrease = true)
    (hused : used ≤ prepaid) (hburnt : burnt ≤ used) :
    (settleGas cfg purchase current prepaid used burnt created).refund +
      (settleGas cfg purchase current prepaid used burnt created).tokensBurnt +
      (used - burnt) * purchase = prepaid * purchase := by
  let burn := min purchase current
  let gross := prepaid - used
  let penaltyGas := min gross (max (gross * cfg.fees.gasRefundPenalty.1 / cfg.fees.gasRefundPenalty.2)
    cfg.fees.minGasRefundPenalty)
  let penalty := penaltyGas * burn
  let charge := if created then
      min ((purchase - burn) * burnt) (cfg.accountCreationCharge - cfg.fees.actionFees.createAccount.execution * burn)
    else 0
  have hb : burn ≤ purchase := Nat.min_le_left _ _
  have hp : penalty ≤ (prepaid - used) * purchase :=
    Nat.mul_le_mul (Nat.min_le_left _ _) hb
  have hc : charge ≤ (purchase - burn) * burnt := by
    dsimp only [charge]
    split
    · exact Nat.min_le_left _ _
    · exact Nat.zero_le _
  have identity := gas_settlement_partition purchase burn prepaid used burnt penalty charge hb hused hburnt hp hc
  simpa [settleGas, hnew, burn, gross, penaltyGas, penalty, charge,
    Nat.sub_eq_zero_of_le hb] using identity

end Fees

end Near
