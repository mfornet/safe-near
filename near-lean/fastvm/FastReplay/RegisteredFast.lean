import ChainReplay.RegisteredCore
import NearFastVM.Run

/-!
`registered-replay-fast`: `registered-replay` with the fast VM engine (`NearFastVM`) in place of the
specification. The same request, the same answer, expected.
-/

namespace ChainReplay

open Near

instance fastEngine : VmEngine :=
  ⟨fun cfg code codeSize method ctx storage => NearFastVM.run cfg code codeSize method ctx storage⟩

end ChainReplay

def main : IO Unit := do
  let request ← IO.ofExcept (Lean.Json.parse (← (← IO.getStdin).readToEnd))
  IO.println (← ChainReplay.Registered.execute request).compress
