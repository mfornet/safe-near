import Wasm.Syntax

/-!
# The size of a function body

Used by `Wasm.Fuel` to bound the steps that execute no instruction, and by a
runner to size its step budget. Kept apart from those proofs so the runner
does not build them.
-/

namespace Wasm.Exec

mutual
/-- Size of an instruction: one, plus its nested bodies. -/
def instrSize : Instr → Nat
  | .block _ body => codeSize body + 2
  | .loop _ body => codeSize body + 2
  | .«if» _ thenBody elseBody => codeSize thenBody + codeSize elseBody + 2
  | _ => 1

def codeSize : List Instr → Nat
  | [] => 1
  | i :: rest => instrSize i + codeSize rest
end

end Wasm.Exec
