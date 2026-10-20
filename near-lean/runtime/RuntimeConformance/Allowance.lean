import NearRuntime.Refund
import NearRuntime.Fees

open Lean Near

structure AllowanceRequest where
  operation : String
  keyKind : String
  allowance : String
  keyNonce : Nat
  receiverId : String
  methods : List String
  targetMatches : Bool
  refunds : List String
  deriving FromJson

def keyJson (pk : PublicKey) : Option AccessKey → Json
  | none => Json.null
  | some key => match key.permission with
    | .fullAccess => Json.mkObj [("nonce", toJson key.nonce), ("kind", toJson "full"), ("storageBytes", toJson (accessKeyStorageBytes pk key))]
    | .functionCall allowance receiver methods => Json.mkObj [
      ("nonce", toJson key.nonce), ("kind", toJson "functionCall"),
      ("allowance", toJson (allowance.map toString)), ("receiverId", toJson receiver), ("methods", toJson methods), ("storageBytes", toJson (accessKeyStorageBytes pk key))]

def receiptMetadata (receipt : Receipt) : Json :=
  match receipt.receipt with
  | .data _ => Json.null
  | .action action => Json.mkObj [
    ("predecessorId", toJson receipt.predecessorId), ("receiverId", toJson receipt.receiverId),
    ("signerId", toJson action.signerId), ("signerPublicKey", toJson (action.signerPublicKey.map UInt8.toNat)),
    ("gasPrice", toJson (toString action.gasPrice)),
    ("amount", match action.actions with | [.transfer amount] => toJson (toString amount) | _ => Json.null)]

def checkedBalance (value : String) : IO Nat := do
  let some value := value.toNat? | throw (IO.userError "invalid balance")
  unless value < 2 ^ 128 do throw (IO.userError "balance exceeds u128")
  pure value

def main : IO Unit := do
  let line ← (← IO.getStdin).getLine
  let request : AllowanceRequest ← match Json.parse line >>= fromJson? with
    | .ok r => pure r
    | .error e => throw (IO.userError e)
  unless request.operation == "refundAllowance" do throw (IO.userError "unknown operation")
  unless request.keyNonce < 2 ^ 64 do throw (IO.userError "nonce exceeds u64")
  let allowance ← checkedBalance request.allowance
  let refunds ← request.refunds.mapM checkedBalance
  let target : PublicKey := 0 :: List.replicate 32 7
  let stored : PublicKey := if request.targetMatches then target else 0 :: List.replicate 32 8
  let permission ← match request.keyKind with
    | "finite" => pure (some (AccessKeyPermission.functionCall (some allowance) request.receiverId request.methods))
    | "unlimited" => pure (some (AccessKeyPermission.functionCall none request.receiverId request.methods))
    | "full" => pure (some AccessKeyPermission.fullAccess)
    | "missing" => pure none
    | _ => throw (IO.userError "unknown key kind")
  let initial : ChainState := { accessKeys := match permission with
    | some p => [(("alice.near", stored), { nonce := request.keyNonce, permission := p })]
    | none => [] }
  let final := refunds.foldl (fun st amount => st.refundAllowance "alice.near" target amount) initial
  let amount := refunds.headD 0
  let gas := (gasRefundReceipt initial "alice.near" target amount).1
  let balance := (refundReceipt initial "alice.near" amount).1
  IO.println (Json.mkObj [
    ("targetKey", keyJson target (final.accessKey? "alice.near" target)),
    ("storedKey", keyJson stored (final.accessKey? "alice.near" stored)),
    ("gasRefund", receiptMetadata gas), ("balanceRefund", receiptMetadata balance)]).compress
