import Interpreter.Wasm.Semantics

namespace Wasm

/-- Host state carried by a primitive continuation agrees with its input. -/
def ContinuationHostEq (host : α) : Continuation α → Prop
  | .Fallthrough st _ | .Break _ st _ | .Return st _ | .Trap st _
  | .ReturnCall _ st _ | .Throwing _ _ st _ => st.host = host
  | .Invalid _ | .OutOfFuel => True

set_option maxHeartbeats 2000000 in
/-- GC operations only affect values and the GC heap, never host state. -/
theorem execGcOp_host (m : Module) (st : Store α) (locals : Locals) (operation : GcOp) :
    ContinuationHostEq st.host (execGcOp m st locals operation) := by
  cases operation <;> dsimp only [execGcOp]
  all_goals repeat (first | rfl | trivial | split)

theorem execGcOp_fallthrough_host {m : Module} {st after : Store α}
    {locals : Locals} {operation : GcOp} {next : Locals}
    (h : execGcOp m st locals operation = .Fallthrough after next) : after.host = st.host := by
  have hp := execGcOp_host m st locals operation
  rw [h] at hp
  exact hp

theorem execGcOp_trap_host {m : Module} {st after : Store α}
    {locals : Locals} {operation : GcOp} {message : String}
    (h : execGcOp m st locals operation = .Trap after message) : after.host = st.host := by
  have hp := execGcOp_host m st locals operation
  rw [h] at hp
  exact hp

theorem execGcOp_break_host {m : Module} {st after : Store α}
    {locals : Locals} {operation : GcOp} {depth : Nat} {next : Locals}
    (h : execGcOp m st locals operation = .Break depth after next) : after.host = st.host := by
  have hp := execGcOp_host m st locals operation
  rw [h] at hp
  exact hp

end Wasm
