import NearRuntime.StakingKey

open Lean Near

structure KeyRequest where
  publicKeys : List (List Nat)
  deriving FromJson

def main : IO Unit := do
  let line ← (← IO.getStdin).getLine
  let request : KeyRequest ← IO.ofExcept (Json.parse line >>= fromJson?)
  let results ← request.publicKeys.mapM fun bytes => do
    unless bytes.all (· < 256) do throw (IO.userError "invalid public key byte")
    let key := bytes.map UInt8.ofNat
    pure (Json.mkObj [("publicKey", toJson bytes), ("suitable", toJson (StakingKey.suitable key))])
  IO.println (Json.mkObj [("results", toJson results)]).compress
