import Model.Args
import Model.Storage
import NearInterface.Model

/-!
# wNEAR at the function-call boundary

What `NearInterface.ContractModel` needs beyond the method semantics of
`Model/Methods.lean`, all in the raw space of the protocol:

* `contractStep`: `step` read through `Env.ofContext`, followed by the two
  resource checks the runtime makes on a successful call: promise deposits the
  liquid balance cannot pay (`balanceExceeded`) and the receipt's storage-stake
  check on the post-state (`lackBalanceForState`);
* the exact bytes of return values (`encodeRet`) and of the receipts the
  promises become (`encodeReceipts`), as serde_json and near-sdk 3.1.0 write
  them;
* `gasBound`, an upper bound on the gas a call uses, for every trie.
-/

namespace WNear

open NearInterface (Context RawStorage storageUsageOf stakeDeficit)
open NearInterface.Json (quote)
open Wasm.Near (ReturnData ReceiptSpec)

def AccountId.bytes (a : AccountId) : List UInt8 := a.val.toUTF8.toList

/-! ## Return values -/

/-- A `U128` as near-sdk serialises it: a JSON string. -/
def jsonU128 (n : Nat) : String := quote (toString n)

def StorageBalance.json (b : StorageBalance) : String :=
  "{\"total\":" ++ jsonU128 b.total ++ ",\"available\":" ++ jsonU128 b.available ++ "}"

def jsonOption (json : α → String) : Option α → String
  | some a => json a
  | none => "null"

/-- serde_json's serialisation of a return value. -/
def Ret.json : Ret → String
  | .unit | .promise _ => ""
  | .u128 n => jsonU128 n
  | .bool b => toString b
  | .storageBalance b => b.json
  | .optStorageBalance b => jsonOption StorageBalance.json b
  | .storageBalanceBounds b =>
    "{\"min\":" ++ jsonU128 b.min ++ ",\"max\":" ++ jsonOption jsonU128 b.max ++ "}"
  | .metadata m =>
    "{\"spec\":" ++ quote m.spec ++ ",\"name\":" ++ quote m.name ++ ",\"symbol\":" ++ quote m.symbol
      ++ ",\"icon\":" ++ jsonOption quote m.icon ++ ",\"reference\":" ++ jsonOption quote m.reference
      ++ ",\"reference_hash\":null,\"decimals\":" ++ toString m.decimals ++ "}"

/-- The return data of a call: nothing for `()`, the receipt whose result the
call delegates to, or the JSON bytes. -/
def encodeRet : Ret → ReturnData
  | .unit => .none
  | .promise index => .receiptIndex index
  | r => .value r.json.toUTF8.toList

/-! ## Receipts -/

def OutgoingCall.method : OutgoingCall → String
  | .ftOnTransfer .. => "ft_on_transfer"
  | .ftResolveTransfer .. => "ft_resolve_transfer"

/-- The arguments near-sdk 3.1.0's `ext_contract` serialises: the parameters
as a struct, in declaration order. -/
def OutgoingCall.args : OutgoingCall → String
  | .ftOnTransfer sender amount msg =>
    "{\"sender_id\":" ++ quote sender.val ++ ",\"amount\":" ++ jsonU128 amount
      ++ ",\"msg\":" ++ quote msg ++ "}"
  | .ftResolveTransfer sender receiver amount =>
    "{\"sender_id\":" ++ quote sender.val ++ ",\"receiver_id\":" ++ quote receiver.val
      ++ ",\"amount\":" ++ jsonU128 amount ++ "}"

/-- The receipts of one promise, numbered from `start` in creation order. In
`p.then q`, the first receipt of `q` waits on the last receipt of `p`. -/
def Promise.receipts : Promise → Nat → List ReceiptSpec
  | .transfer receiver amount, _ =>
    [{ receiverId := receiver.bytes, actions := [.transfer amount] }]
  | .call receiver method deposit gas, _ =>
    [{ receiverId := receiver.bytes,
       actions := [.functionCall method.method.toUTF8.toList method.args.toUTF8.toList deposit
         (UInt64.ofNat gas)] }]
  | .then first callback, start =>
    let firsts := first.receipts start
    let callbacks := callback.receipts (start + firsts.length)
    firsts ++ callbacks.modifyHead fun r =>
      { r with dependencies := r.dependencies ++ [start + firsts.length - 1] }

/-- The receipts a call's promises become, in creation order. -/
def encodeReceipts (promises : List Promise) : List ReceiptSpec :=
  (promises.foldl (fun (acc : List ReceiptSpec) p => acc ++ p.receipts acc.length) [])

/-! ## One call at the boundary -/

/-- The contract storage of an optional state. -/
def storageOf : Option State → RawStorage
  | none => ∅
  | some s => encode s

/-- A failed call: the failure and the logs emitted before it. -/
abbrev Result := NearInterface.StepResult Panic State Ret Promise

/-- `step` on the context, then the runtime's resource checks on a success:
the promises' deposits against the liquid balance (the deposit included), and
the storage stake of the account's new usage. -/
def contractStep (ctx : Context) (st : Option State) (c : Call) : Result :=
  match step (Config.ofRuntime ctx.protocol) st (Env.ofContext ctx) c with
  | .error p => .error { failure := .panic p, logs := p.logs }
  | .ok o =>
    let available := ctx.balance + ctx.attached
    if available < o.nearOut then .error { failure := .balanceExceeded, logs := o.logs }
    else
      let usage := ctx.storageUsage - storageUsageOf ctx.protocol (storageOf st) +
        storageUsageOf ctx.protocol (encode o.state)
      let deficit := stakeDeficit ctx.protocol usage (available - o.nearOut) ctx.locked
      if 0 < deficit then .error { failure := .lackBalanceForState deficit, logs := o.logs }
      else .ok { state := o.state, ret := o.ret, logs := o.logs, promises := o.promises }

/-- The failure each panic site produces. Reading a missing promise result is
a host error, reported with nearcore's message. -/
def Panic.failure (p : Panic) : NearInterface.Failure :=
  match p with
  | .noPromiseResult => .other p.message
  | p => .panic p.message

/-! ## Gas

`gasBound` bounds `usedGas`: gas burnt plus the gas reserved for the receipts
a call creates. Measured on `contract.wasm` without trie accounting, every
method burns at most 0.85 Tgas on short arguments, and each argument byte
costs at most 157 Mgas (`ft_transfer_call` with a long `msg`). Storage
accesses are charged per trie node on the key's path: the bound pays every
node of the longest possible path cold for each distinct key a call touches
(the `STATE` record and at most two accounts), and cached for every access.
That the bound holds is an obligation of `Refines`, checked by the adapter
tests on adversarial tries. -/

/-- Wasm execution and host calls other than storage, with short arguments. -/
def computeGas : Nat := 4 * 10 ^ 12
/-- Per byte of the arguments of a method that reads them. -/
def argumentByteGas : Nat := 400 * 10 ^ 6
/-- Execution fees a transfer receipt reserves (measured: 223 Ggas). -/
def transferReceiptGas : Nat := 5 * 10 ^ 11
/-- Execution fees a function-call receipt reserves, short arguments
(measured: at most 0.9 Tgas). Argument bytes are paid by `argumentByteGas`. -/
def callReceiptGas : Nat := 2 * 10 ^ 12
/-- Longest contract key: an `accounts` entry, `b"a"` and a borsh string. -/
def maxStorageKeyBytes : Nat := 1 + 4 + maxAccountIdBytes
/-- Distinct storage keys any call touches: `STATE` and at most two accounts. -/
def storageKeysTouched : Nat := 3
/-- Storage host calls any call makes. -/
def storageAccesses : Nat := 8

/-- Nodes on the longest trie path to a key of this contract: one per nibble of
`contractKey current key`, plus the root. -/
def trieNodes (ctx : Context) : Nat :=
  2 * (2 + ctx.current.bytes.length + maxStorageKeyBytes) + 1

def trieGas (ctx : Context) : Nat :=
  let costs := ctx.protocol.wasm.extCosts
  storageKeysTouched * trieNodes ctx * costs.cost "touching_trie_node" +
    storageAccesses * trieNodes ctx * costs.cost "read_cached_trie_node"

/-- Methods with parameters read and parse their input. -/
def Call.readsArguments : Call → Bool
  | .new | .nearDeposit | .ftTotalSupply | .ftMetadata | .storageBalanceBounds
  | .storageMinimumBalance => false
  | _ => true

/-- Gas the call attaches to the receipts it creates. -/
def Call.attachedGas (ctx : Context) : Call → Nat
  | .ftTransferCall .. => ctx.prepaidGas - gasForFtTransferCall + gasForResolveTransfer
  | _ => 0

/-- Execution fees of the receipts the call may create. -/
def Call.receiptGas : Call → Nat
  | .nearWithdraw _ | .storageDeposit .. | .storageUnregister _ => transferReceiptGas
  | .ftTransferCall .. => 2 * callReceiptGas
  | _ => 0

def gasBound (ctx : Context) (c : Call) : Nat :=
  c.attachedGas ctx + c.receiptGas + computeGas +
    (if c.readsArguments then argumentByteGas * ctx.args.length else 0) + trieGas ctx

end WNear
