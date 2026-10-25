import ChainReplay.RegisteredCore

def main : IO Unit := do
  let request ← IO.ofExcept (Lean.Json.parse (← (← IO.getStdin).readToEnd))
  IO.println (← ChainReplay.Registered.execute request).compress
