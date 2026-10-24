import NearChain.Step
import Wasm

/-! Replay the shared full-receipt scenarios through the public chain step.
The delivery selector is a test input; it is not a shard-network implementation. -/
open Lean Wasm Wasm.Near Near

instance : FromJson UInt8 where
  fromJson? value := do
    let n : Nat ← fromJson? value
    if n < 256 then pure (UInt8.ofNat n) else .error "byte exceeds u8"
instance : ToJson UInt8 where
  toJson value := toJson value.toNat

structure ContractInput where
  account : String
  codePath : String
  watPath : String
  deriving FromJson
structure AccountInput where
  id : String
  balance : String
  deriving FromJson
structure ActionInput where
  kind : String
  method : String := ""
  args : List UInt8 := []
  gas : Nat := 0
  deposit : String := "0"
  beneficiary : String := ""
  codePath : String := ""
  deriving FromJson
structure ReceiptInput where
  receiver : String
  predecessor : String
  actions : List ActionInput
  deriving FromJson
structure StepInput where
  label : String
  deliver : Json
  inject : List ReceiptInput
  gasLimit : Option Nat := none
  deriving FromJson
structure KeyInput where
  account : String
  key : List UInt8
  deriving FromJson
structure Request where
  protocolVersion : Nat
  configDir : String
  contracts : List ContractInput
  accounts : List AccountInput
  inspectKeys : List KeyInput
  steps : List StepInput
  deriving FromJson

def actionJson : Action → Json
  | .functionCall method args gas deposit => Json.mkObj [
      ("kind", toJson "functionCall"), ("method", toJson method), ("args", toJson args),
      ("gas", toJson gas), ("deposit", toJson (toString deposit))]
  | .transfer deposit => Json.mkObj [("kind", toJson "transfer"), ("deposit", toJson (toString deposit))]
  | .deleteAccount beneficiary => Json.mkObj [("kind", toJson "deleteAccount"), ("beneficiary", toJson beneficiary)]
  | .deployContract code => Json.mkObj [("kind", toJson "deployContract"), ("size", toJson code.size)]
  | _ => Json.mkObj [("unsupported", toJson true)]

def receiptJson (r : Receipt) : Json :=
  let body := match r.receipt with
    | .action a => Json.mkObj [
        ("kind", toJson "action"), ("signer", toJson a.signerId), ("signerPublicKey", toJson a.signerPublicKey),
        ("gasPrice", toJson (toString a.gasPrice)), ("refundTo", Json.null),
        ("inputs", toJson a.inputDataIds),
        ("outputs", toJson (a.outputDataReceivers.map fun d => Json.mkObj [
          ("data_id", toJson d.dataId), ("receiver_id", toJson d.receiverId)])),
        ("actions", toJson (a.actions.map actionJson))]
    | .data d => Json.mkObj [("kind", toJson "data"), ("dataId", toJson d.dataId), ("data", toJson d.data)]
    | .globalDistribution _ => Json.mkObj [("kind", toJson "globalDistribution")]
  Json.mkObj [("id", toJson r.receiptId), ("predecessor", toJson r.predecessorId),
    ("receiver", toJson r.receiverId), ("body", body)]

def statusJson : ExecutionStatus → Json
  | .successValue bytes => Json.mkObj [("kind", toJson "value"), ("value", toJson bytes)]
  | .successReceiptId id => Json.mkObj [("kind", toJson "receipt"), ("receiptId", toJson id)]
  | .failure error => Json.mkObj [("kind", toJson "failure"), ("error", toJson (reprStr error))]

def outcomeJson (pair : ReceiptId × ExecutionOutcome) : Json :=
  let (id, o) := pair
  Json.mkObj [("id", toJson id), ("executor", toJson o.executorId), ("status", statusJson o.status),
    ("logs", toJson o.logs), ("gasBurnt", toJson o.gasBurnt), ("tokensBurnt", toJson (toString o.tokensBurnt)),
    ("receipts", toJson o.receiptIds)]

def parseAmount (s : String) : IO Nat := do
  let some n := s.toNat? | throw (IO.userError "invalid decimal amount")
  unless n < 2 ^ 128 do throw (IO.userError "amount exceeds u128")
  return n

def main : IO Unit := do
  let input ← (← IO.getStdin).getLine
  let request : Request ← match Json.parse input >>= fromJson? with
    | .ok r => pure r
    | .error error => throw (IO.userError error)
  unless request.protocolVersion == 86 do throw (IO.userError "receipt replay pins protocol 86")
  let cfg ← RuntimeConfig.load request.configDir request.protocolVersion
  let mut registry : List (String × List UInt8 × ContractCode) := []
  for c in request.contracts do
    let raw ← IO.FS.readBinFile c.codePath
    let module ← match Binary.decode raw with
      | .ok m => pure m
      | .error error => throw (IO.userError error.message)
    let bytes := raw.data.toList
    registry := registry ++ [(c.account, bytes, { module, size := bytes.length, hash := c.codePath })]
  let decoder : CodeTable := fun bytes =>
    ((registry.find? (fun entry => entry.2.1 == bytes)).map (·.2.2)).getD default
  let mut state : ChainState := { nextId := 1_000_000 }
  for a in request.accounts do
    let amount ← parseAmount a.balance
    let code := (registry.find? (fun entry => entry.1 == a.id)).map (·.2.2)
    state := state.setAccount a.id { amount, code, storageUsage := 182 + (code.map (·.size)).getD 0 }
  let mut snapshot : Snapshot := { state }
  let mut trace : List Json := []
  for (block, index) in request.steps.zipIdx do
    let mut injected : List Receipt := []
    for (r, ri) in block.inject.zipIdx do
      let mut actions : List Action := []
      for a in r.actions do
        let action ← match a.kind with
          | "functionCall" => do
            unless a.gas < 2 ^ 64 do throw (IO.userError "gas exceeds u64")
            pure (.functionCall a.method a.args a.gas (← parseAmount a.deposit))
          | "transfer" => do pure (.transfer (← parseAmount a.deposit))
          | "deleteAccount" => pure (.deleteAccount a.beneficiary)
          | "deployContract" => do
            let bytes := (← IO.FS.readBinFile a.codePath).data.toList
            unless registry.any (fun c => c.2.1 == bytes) do throw (IO.userError "unregistered deployment")
            pure (.deployContract (decoder bytes))
          | _ => throw (IO.userError "unknown action kind")
        actions := actions ++ [action]
      injected := injected ++ [{
        receiptId := 100 + index * 1000 + ri
        predecessorId := r.predecessor
        receiverId := r.receiver
        receipt := .action {
          signerId := r.predecessor
          signerPublicKey := List.replicate 33 0
          gasPrice := 100_000_000
          actions } }]
    let pending := snapshot.pending ++ injected
    let deliver := fun id =>
      injected.any (fun r => r.receiptId == id) ||
        match block.deliver with
        | .str "all" => true
        | .str "none" => false
        | .arr ids => pending.any (fun r => r.receiptId == id && ids.any (· == .str r.receiverId))
        | .obj _ => pending.any (fun r => r.receiptId == id &&
            ((block.deliver.getObjValAs? (Array String) "receivers").toOption.getD #[]).contains r.receiverId &&
            match (block.deliver.getObjValAs? String "kind").toOption with
            | some "data" => match r.receipt with | .data _ => true | _ => false
            | some "action" => match r.receipt with | .action _ => true | _ => false
            | _ => false)
        | _ => false
    let incoming := pending.filter (fun r => deliver r.receiptId)
    let positions := (pending.zipIdx.filter (fun (r, _) => deliver r.receiptId)).map Prod.snd
    let (next, result) ← match step cfg decoder { snapshot with pending }
      { ap := { blockHeight := index + 1, blockTimestamp := (index + 1) * 1_000_000_000,
                gasPrice := 100_000_000, gasLimit := block.gasLimit }, txs := [], receipts := .indices positions } with
      | .ok value => pure value
      | .error error => throw (IO.userError s!"schedule error: {reprStr error}")
    if let some (_, issue) := result.issue then throw (IO.userError s!"model issue: {reprStr issue}")
    snapshot := next
    let accounts := Json.mkObj (request.accounts.map fun a =>
      (a.id, match snapshot.state.account? a.id with
        | none => Json.null
        | some account => Json.mkObj [("balance", toJson (toString account.amount)), ("storageUsage", toJson account.storageUsage)]))
    let storage := request.inspectKeys.map fun k =>
      let value := ((snapshot.state.contractStorage k.account).find? (fun kv => kv.1 == k.key)).map (·.2)
      Json.mkObj [("account", toJson k.account), ("key", toJson k.key), ("value", toJson value)]
    trace := trace ++ [Json.mkObj [("label", toJson block.label), ("incoming", toJson (incoming.map receiptJson)),
      ("outgoing", toJson (result.outgoing.map receiptJson)), ("outcomes", toJson (result.outcomes.map outcomeJson)),
      ("accounts", accounts), ("storage", toJson storage), ("pending", toJson (snapshot.pending.map receiptJson)),
      ("delayed", toJson snapshot.state.delayed.length)]]
  IO.println (Json.mkObj [("trace", toJson trace), ("protocolVersion", toJson request.protocolVersion),
    ("backend", toJson "Lean Near.step / Near.apply / NearVM.run")]).compress
