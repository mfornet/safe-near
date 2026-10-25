import NearNode.Rpc.Query

/-!
# Transactions: `tx`, `EXPERIMENTAL_tx_status`, `send_tx`, `broadcast_tx_async`, `broadcast_tx_commit`

`chain/jsonrpc/src/lib.rs` (`send_tx`, `tx_status_fetch`, `send_tx_internal`), `ViewClientActor::get_tx_status`
and `Chain::get_final_transaction_result` at the pinned nearcore. A transaction sent here goes to the
node's loop (the pool is only touched there) and the request then polls the node's record of executed
transactions every 200 ms for at most 10 s, as `RpcPollingConfig` does.
-/

namespace Near.Node.Rpc

open Lean Near.Node Near.Node.Borsh Near.Node.Chain Near.Node.Network Near.Node.Validator
  Near.Node.Apply

/-! ### `InvalidTxError` -/

private def keyOfBytes (b : List UInt8) : Json :=
  match Codec.decodeAll (α := PublicKey) ⟨b.toArray⟩ with
  | .ok k => jkey k
  | .error _ => Json.null

/-- `InvalidTxError` as `serde_json` writes it. The runtime model's errors are mapped to the variant
they correspond to; the reasons the model has no variant for fall back to `ActionsValidation`. -/
def invalidTxJson : TxReject → Json
  | .expired => Json.str "Expired"
  | .invalidChain => Json.str "InvalidChain"
  | .invalidSignature => Json.str "InvalidSignature"
  | .invalidVersion => Json.str "InvalidTransactionVersion"
  | .sizeExceeded s l =>
    tagged "TransactionSizeExceeded" (Json.mkObj [("size", jn s), ("limit", jn l)])
  | .actions w => tagged "ActionsValidation" (Json.str w)
  | .congested w => tagged "ShardCongested" (Json.str w)
  | .unsupported w => tagged "ActionsValidation" (Json.str w)
  | .state w => tagged "StorageError" (Json.str w)
  | .runtime e =>
    match e with
    | .invalidSigner id => tagged "SignerDoesNotExist" (Json.mkObj [("signer_id", id)])
    | .accessKeyNotFound id pk =>
      tagged "InvalidAccessKeyError"
        (tagged "AccessKeyNotFound"
          (Json.mkObj [("account_id", id), ("public_key", keyOfBytes pk)]))
    | .invalidNonce t a =>
      tagged "InvalidNonce" (Json.mkObj [("tx_nonce", jn t), ("ak_nonce", jn a)])
    | .nonceTooLarge t u =>
      tagged "NonceTooLarge" (Json.mkObj [("tx_nonce", jn t), ("upper_bound", jn u)])
    | .notEnoughBalance id b c =>
      tagged "NotEnoughBalance"
        (Json.mkObj
          [("signer_id", id), ("balance", Json.str (toString b)), ("cost", Json.str (toString c))])
    | .lackBalanceForState id a =>
      tagged "LackBalanceForState"
        (Json.mkObj [("signer_id", id), ("amount", Json.str (toString a))])
    | .notEnoughAllowance id pk al c =>
      tagged "InvalidAccessKeyError"
        (tagged "NotEnoughAllowance"
          (Json.mkObj
            [("account_id", id), ("public_key", keyOfBytes pk),
              ("allowance", Json.str (toString al)), ("cost", Json.str (toString c))]))
    | .receiverMismatch t k =>
      tagged "InvalidAccessKeyError"
        (tagged "ReceiverMismatch" (Json.mkObj [("tx_receiver", t), ("ak_receiver", k)]))
    | .methodNameMismatch m =>
      tagged "InvalidAccessKeyError" (tagged "MethodNameMismatch" (Json.mkObj [("method_name", m)]))
    | .invalidAccessKey "RequiresFullAccess" =>
      tagged "InvalidAccessKeyError" (Json.str "RequiresFullAccess")
    | .invalidAccessKey "DepositWithFunctionCall" =>
      tagged "InvalidAccessKeyError" (Json.str "DepositWithFunctionCall")
    | .transactionSizeExceeded s l =>
      tagged "TransactionSizeExceeded" (Json.mkObj [("size", jn s), ("limit", jn l)])
    | .invalidTransactionVersion => Json.str "InvalidTransactionVersion"
    | other => tagged "ActionsValidation" (Json.str other.message)

def invalidTxError (r : TxReject) : RpcError :=
  RpcError.handler "INVALID_TRANSACTION" (some (Json.mkObj []))
    (tagged "TxExecutionError" (tagged "InvalidTxError" (invalidTxJson r)))

def timeoutError : RpcError :=
  RpcError.handler "TIMEOUT_ERROR" none (Json.str "Timeout") 408

def unknownTransaction (h : CryptoHash) : RpcError :=
  RpcError.handler "UNKNOWN_TRANSACTION"
    (some (Json.mkObj [("requested_transaction_hash", jhash h)]))
    (Json.str s!"Transaction {base58Encode h.bytes} doesn't exist")

/-! ### The status of a transaction -/

inductive WaitUntil where
  | none
  | included
  | executedOptimistic
  | includedFinal
  | executed
  | final
  deriving BEq

def WaitUntil.name : WaitUntil → String
  | .none => "NONE"
  | .included => "INCLUDED"
  | .executedOptimistic => "EXECUTED_OPTIMISTIC"
  | .includedFinal => "INCLUDED_FINAL"
  | .executed => "EXECUTED"
  | .final => "FINAL"

def parseWaitUntil : Json → Except String WaitUntil
  | .str "NONE" => pure .none
  | .str "INCLUDED" => pure .included
  | .str "EXECUTED_OPTIMISTIC" => pure .executedOptimistic
  | .str "INCLUDED_FINAL" => pure .includedFinal
  | .str "EXECUTED" => pure .executed
  | .str "FINAL" => pure .final
  | .str s =>
    throw
      s!"unknown variant `{s}`, expected one of `NONE`, `INCLUDED`, `EXECUTED_OPTIMISTIC`, `INCLUDED_FINAL`, `EXECUTED`, `FINAL`"
  | _ => throw "invalid type, expected a string"

/-- `tx_execution_status_meets_expectations`. -/
def WaitUntil.meets (expected actual : WaitUntil) : Bool :=
  match expected with
  | .none => true
  | .included => actual != .none
  | .executedOptimistic => actual == .executedOptimistic || actual == .executed || actual == .final
  | .includedFinal => actual == .includedFinal || actual == .executed || actual == .final
  | .executed => actual == .executed || actual == .final
  | .final => actual == .final

/-- An outcome with the block that holds it. -/
abbrev Found :=
  OutcomeRec

/-- `get_recursive_transaction_results`: the outcome of `id`, then those of the receipts it created, depth first. -/
partial def recursiveOutcomes (s : VState) (id : CryptoHash) (acc : Array Found)
    (fuel : Nat := 100000) : Array Found :=
  match s.outcomes[id.bytes]? with
  | none => acc
  | some o =>
    let acc := acc.push o
    o.outcome.outcome.receiptIds.foldl (fun acc r => recursiveOutcomes s r acc fuel) acc

def outcomeWithIdView (o : OutcomeRec) : Json :=
  Json.mkObj
    [("proof", merklePathView o.proof), ("block_hash", jhash o.block), ("id", jhash o.outcome.id),
      ("outcome", outcomeView o.outcome.outcome)]

/-- `get_execution_status`. -/
def finalStatus (txHash : CryptoHash) (outcomes : Array Found) : Json :=
  if outcomes.isEmpty then Json.str "NotStarted"
  else
    Id.run do
      let mut looking := txHash
      for o in outcomes do
        if o.outcome.id == looking then
          match o.outcome.outcome.status with
          | .unknown =>
            return Json.str (if outcomes.size == 1 then "NotStarted" else "Started")
          | .failure _ =>
            return tagged "Failure" Json.null
          | .successValue v =>
            return tagged "SuccessValue" (jbytes v)
          | .successReceiptId r =>
            looking := r
      return Json.str "Started"

/-- Whether a block is final and on the chain of the tip (`check_blocks_final_and_canonical`). -/
def finalAndCanonical (s : VState) (hash : CryptoHash) : Bool :=
  match s.st.block hash, s.st.block s.tip with
  | .ok b, .ok tip =>
    match s.st.block tip.view.lastFinalBlock with
    | .ok fin => b.view.height ≤ fin.view.height && s.canon[b.view.height]? == some hash.bytes
    | .error _ => false
  | _, _ => false

/-- `get_tx_execution_status`: the lowest status the node can prove. -/
def executionStatus (s : VState) (txOutcome : Found) (receipts : Array Found) : WaitUntil :=
  if txOutcome.outcome.outcome.status matches .unknown then .none
  else
    Id.run do
      let awaiting : List CryptoHash :=
        txOutcome.outcome.outcome.receiptIds.toList ++
          (receipts.toList.flatMap fun o => o.outcome.outcome.receiptIds.toList)
      let executed : List CryptoHash :=
        (receipts.toList.filter fun o => !(o.outcome.outcome.status matches .unknown)).map
          (·.outcome.id)
      -- a refund receipt that is the last one of an outcome is not waited for
      let mut nonRefund := awaiting
      for o in receipts do
        if let some last := o.outcome.outcome.receiptIds.back? then
          if executed.contains last then
            continue
          match s.receiptsById[last.bytes]? with
          | some (.v0 r) =>
            if r.predecessorId.val == "system" then
              nonRefund := nonRefund.filter (· != last)
          | none =>
            pure ()
      let executedIgnoringRefunds := nonRefund.all executed.contains
      let executedIncludingRefunds := awaiting.all executed.contains
      if !(finalAndCanonical s txOutcome.block) then
        return if executedIgnoringRefunds then .executedOptimistic else .included
      if !executedIgnoringRefunds then
        return .includedFinal
      if !executedIncludingRefunds then
        return .executed
      let blocks := (receipts.toList.map (·.block)).eraseDups
      return if blocks.all (finalAndCanonical s) then .final else .executed

/-- The status of a transaction, or `none` when the node knows of no such transaction. -/
def txStatus (s : VState) (hash : CryptoHash) (withReceipts : Bool) : Option (Json × WaitUntil) :=
  match s.txIndex[hash.bytes]?, s.outcomes[hash.bytes]? with
  | some (blockHash, chunkHash), some txOutcome =>
    let all := recursiveOutcomes s hash #[]
    let receipts := all.extract 1 all.size
    let tx? : Option SignedTransaction :=
      ((s.chunks[chunkHash.hash.bytes]?).bind (·.body)).bind fun b =>
        b.transactions.find? (·.hash == hash)
    match tx? with
    | none => none
    | some tx =>
      let status := executionStatus s txOutcome receipts
      let local_ := tx.transaction.signerId == tx.transaction.receiverId
      let first? := txOutcome.outcome.outcome.receiptIds[0]?
      let receiptViews : List (String × Json) :=
        if withReceipts then
          [("receipts",
              Json.arr
                ((receipts.filterMap fun o =>
                  if some o.outcome.id == first? && local_ then none
                  else (s.receiptsById[o.outcome.id.bytes]?).map receiptView)))]
        else []
      let body :=
        Json.mkObj
          ([("status", finalStatus hash all), ("transaction", signedTransactionView tx),
              ("transaction_outcome", outcomeWithIdView txOutcome),
              ("receipts_outcome", jarr outcomeWithIdView receipts)] ++
            receiptViews ++
            [("final_execution_status", Json.str status.name)])
      let _ := blockHash
      some (body, status)
  | _, _ => none

/-! ### Requests -/

/-- Decodes the `signed_tx_base64` of a request: base64, then Borsh. -/
def parseSignedTx (j : Json) : Except String SignedTransaction :=
  match j with
  | .str s =>
    match base64Decode s with
    | .error why => throw s!"the value could not decoded from base64 due to: {why}"
    | .ok bytes =>
      match Codec.decodeAll (α := SignedTransaction) bytes with
      | .ok t => pure t
      | .error .eof =>
        throw "the value could not decoded from borsh due to: Unexpected length of input"
      | .error (.tag "Transaction" v) =>
        throw
          s!"the value could not decoded from borsh due to: invalid transaction version tag: {v}"
      | .error e => throw s!"the value could not decoded from borsh due to: {repr e}"
  | _ => throw "invalid type: expected a string of base64"

/-- Polls `check` every 200 ms for 10 s. -/
partial def poll {α : Type} (check : IO (Option α)) (timeoutMs : Nat := 10000) : IO (Option α) := do
  let started ← IO.monoMsNow
  let rec loop : IO (Option α) := do
    if let some r← check then
      return some r
    if (← IO.monoMsNow) - started ≥ timeoutMs then
      return none
    IO.sleep 200
    loop
  loop

/-- Submits a transaction to the node's loop. -/
def submit (c : Ctx) (t : SignedTransaction) : IO TxVerdict := do
  let p ← IO.Promise.new
  c.env.txQueue.modify (·.push (t, p))
  let r ←
    poll
        (do
          if ← p.isResolved then
            return some (← IO.wait p.result!)
          else
            return none)
        30000
  return r.getD .noResponse

/-- Why a transaction would be refused now, if it would (`ProcessTxRequest` with `check_only`). -/
def checkOnly (c : Ctx) (s : VState) (t : SignedTransaction) : Option TxReject :=
  match lift' (s.st.epochIdFromPrevBlock s.tip) with
  | .error _ => none
  | .ok epoch =>
    match
      (s.st.epoch epoch).toOption.bind fun e =>
        e.layout.accountIdToShardId t.transaction.signerId with
    | none => none
    | some shard =>
      match c.env.txContext s s.tip shard with
      | .error _ => none
      | .ok ctx =>
        match ctx.checkForPool t with
        | .error r => some r
        | .ok () => none
where lift' {α : Type} (r : Result α) : Except String α :=
    r.mapError fun e => s!"{e.kind} {e.detail}"

def txStatusRequest (c : Ctx) (params : Json) (withReceipts : Bool) : IO R := do
  let parsed : Except String (CryptoHash × AccountId × WaitUntil × Option SignedTransaction) := do
    let wait ←
      match field? params "wait_until" with
      | some w =>
        parseWaitUntil w
      | none =>
        pure .executedOptimistic
    match params with
    | .arr #[h, a] =>
      do
        pure (← parseHash h, ← parseAccount a, WaitUntil.executedOptimistic, none)
    | .arr #[x] =>
      do
        let t ← parseSignedTx x
        pure (t.hash, t.transaction.signerId, .executedOptimistic, some t)
    | .obj _ =>
      if let some x := field? params "signed_tx_base64" then
        let t ← parseSignedTx x
        pure (t.hash, t.transaction.signerId, wait, some t)
      else
        let some h :=
          field? params
            "tx_hash" | throw "data did not match any variant of untagged enum TransactionInfo"
        let some a :=
          field? params
            "sender_account_id" | throw "data did not match any variant of untagged enum TransactionInfo"
        pure (← parseHash h, ← parseAccount a, wait, none)
    | _ =>
      throw "invalid type, expected a transaction reference"
  match liftParse parsed with
  | .error e =>
    return .error e
  | .ok (hash, _, wait, tx?) =>
    if wait == .none && tx?.isNone && (txStatus (← c.env.get) hash withReceipts).isNone then
      return .error (unknownTransaction hash)
    let r ←
      poll
          (do
            let s ← c.env.get
            match txStatus s hash withReceipts with
            | some (body, status) =>
              if wait.meets status then
                return some (Sum.inl body)
              else
                return none
            | none =>
              -- a transaction sent with the request that is invalid is told so (`send_tx_internal` with `check_only`)
              match tx? with
              | some t =>
                match checkOnly c s t with
                | some reason =>
                  return some (Sum.inr reason)
                | none =>
                  return none
              | none =>
                return none)
    match r with
    | some (.inl body) =>
      return .ok body
    | some (.inr reason) =>
      return .error (invalidTxError reason)
    | none =>
      return .error timeoutError

def sendTx (c : Ctx) (t : SignedTransaction) (wait : WaitUntil) : IO R := do
  if wait == .none then
    discard <| submit c t
    return .ok (Json.mkObj [("final_execution_status", "NONE")])
  match ← submit c t with
  | .invalid reason =>
    -- a resubmitted transaction is not an error (`send_tx_internal`)
    let s ← c.env.get
    match reason, s.txIndex[t.hash.bytes]? with
    | .runtime (.invalidNonce ..), some _ =>
      pure ()
    | _, _ =>
      return .error (invalidTxError reason)
    pure ()
  | .noResponse =>
    return .error timeoutError
  | _ =>
    pure ()
  let r ←
    poll
        (do
          let s ← c.env.get
          match txStatus s t.hash false with
          | some (body, status) =>
            if wait.meets status then
              return some body
            else
              return none
          | none =>
            return none)
  match r with
  | some body =>
    return .ok body
  | none =>
    return .error timeoutError

def sendTxRequest (c : Ctx) (params : Json) (commit : Bool) : IO R := do
  let parsed : Except String (SignedTransaction × WaitUntil) := do
    match params with
    | .arr #[x] =>
      do
        pure (← parseSignedTx x, WaitUntil.executedOptimistic)
    | .obj _ =>
      let some x := field? params "signed_tx_base64" | throw "missing field `signed_tx_base64`"
      let wait ←
        match field? params "wait_until" with
        | some w =>
          parseWaitUntil w
        | none =>
          pure .executedOptimistic
      pure (← parseSignedTx x, if commit then .executedOptimistic else wait)
    | _ =>
      throw "invalid type, expected a transaction"
  match liftParse parsed with
  | .error e =>
    return .error e
  | .ok (t, wait) =>
    sendTx c t wait

def broadcastAsync (c : Ctx) (params : Json) : IO R := do
  let parsed : Except String SignedTransaction :=
    match params with
    | .arr #[x] => parseSignedTx x
    | .obj _ =>
      match field? params "signed_tx_base64" with
      | some x => parseSignedTx x
      | none => throw "missing field `signed_tx_base64`"
    | _ => throw "invalid type, expected a transaction"
  let marker := "the value could not decoded from borsh due to: "
  match parsed with
  | .error m =>
    if m.startsWith marker then
      return .error (RpcError.parse s!"Failed to decode transaction: {m.drop marker.length}")
    else
      return .error (RpcError.parse s!"Failed parsing args: {m}")
  | .ok t =>
    -- the transaction is handed to the node's loop; the answer does not wait for it
    let p ← IO.Promise.new
    c.env.txQueue.modify (·.push (t, p))
    return .ok (jhash t.hash)

end Near.Node.Rpc
