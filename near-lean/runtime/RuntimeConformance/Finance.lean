import NearRuntime.Fees

open Lean Wasm.Near Near

structure FinanceRequest where
  configDir : String
  protocolVersion : Nat
  currentPrice : String
  purchasePrice : String
  prepaidGas : Nat
  usedGas : Nat
  burntGas : Nat
  createdAccount : Bool
  deriving FromJson

def main : IO Unit := do
  let input ← (← IO.getStdin).getLine
  let request : FinanceRequest ← match Json.parse input >>= fromJson? with
    | .ok r => pure r
    | .error e => throw (IO.userError e)
  unless 84 ≤ request.protocolVersion && request.protocolVersion ≤ 86 do
    throw (IO.userError "financial reference supports protocol versions 84 through 86")
  unless [request.prepaidGas, request.usedGas, request.burntGas].all (· < 2 ^ 64) do
    throw (IO.userError "gas exceeds u64")
  let cfg ← RuntimeConfig.load request.configDir request.protocolVersion
  let some current := request.currentPrice.toNat? | throw (IO.userError "invalid price")
  let some purchase := request.purchasePrice.toNat? | throw (IO.userError "invalid price")
  unless current < 2 ^ 128 && purchase < 2 ^ 128 do
    throw (IO.userError "price exceeds u128")
  let actions : List Action := (if request.createdAccount then [.createAccount] else []) ++
    [.functionCall "go" [] request.prepaidGas 0]
  let cost := Fees.txCost cfg current "alice.near" "bob.near" actions
  unless request.burntGas ≤ request.usedGas && request.usedGas ≤ cost.gasRemaining do
    throw (IO.userError "invalid gas budget")
  let settlement := Fees.settleGas cfg purchase current cost.gasRemaining request.usedGas request.burntGas request.createdAccount
  IO.println (Json.mkObj [
    ("txGasBurnt", toJson cost.gasBurnt), ("txGasRemaining", toJson cost.gasRemaining),
    ("txReceiptPrice", toJson (toString cost.receiptGasPrice)), ("txTotal", toJson (toString cost.total)),
    ("burnPrice", toJson (toString settlement.burnPrice)), ("refund", toJson (toString settlement.refund)),
    ("priceDeficit", toJson (toString settlement.priceDeficit)), ("priceSurplus", toJson (toString settlement.priceSurplus)),
    ("refundPenalty", toJson (toString settlement.refundPenalty)), ("creationCharge", toJson (toString settlement.creationCharge))]).compress
