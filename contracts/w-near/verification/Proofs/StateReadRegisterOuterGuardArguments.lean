import Proofs.StateReadRegisterOuterArguments
import Proofs.StateReadRegisterOuterGuard

/-! Opaque twelve-instruction present-tag and allocator-argument capsule. -/
namespace WNear.Proofs.StateReadRegisterOuter
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode readI64
private theorem paid_add (s : Store NearState) (op a b : Nat) : paid (paid s op a) op b=paid s op (a+b) := by
  induction b with |zero=>rfl |succ b ih=>simp only [paid,ih];rfl
private theorem modules_paid (s : Store NearState) (op n : Nat) : (paid s op n).modules=s.modules := by
  induction n with |zero=>rfl |succ n ih=>exact ih
private theorem mems_paid (s : Store NearState) (op n : Nat) : (paid s op n).mems=s.mems := by
  induction n with |zero=>rfl |succ n ih=>exact ih

theorem wp_guard_arguments (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (scratch : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (h2 : frame.locals[2]?=some (.i32 scratch)) (hm : s.modules[frame.inst]?=some mi)
    (hi : mi.memAddrs[0]?=some index) (hmem : s.mems[index]?=some memory)
    (hb : scratch.toNat+24≤memory.byteSize)
    (hn : (readI64 memory (scratch.toNat+8)).toUInt32≠0)
    (hc : s.host.gas.Credits (12*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 12) limits
      (((stack.push (.i32 (scratch+32))).push (.i32 0)).push (.i32 (readI64 memory (scratch.toNat+16)).toUInt32)) frame callers code)) rest post) :
    WP cfg (fuel+12) (.next (atCode s limits stack frame callers
      (WNear.Binary.StateReadRegisterOuter.presentGuard++WNear.Binary.StateReadRegisterOuter.vectorArguments++code)))
      (12*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  let gs := paid s op 5
  have gm : gs.modules[frame.inst]?=some mi := by rw [modules_paid];exact hm
  have ge : gs.mems[index]?=some memory := by rw [mems_paid];exact hmem
  have gc := paid_credits s op 5 (7*op+rest) (hc.mono (by dsimp [op];omega))
  have next : WP cfg fuel (.next (atCode (paid gs op 7) limits
      (((stack.push (.i32 (scratch+32))).push (.i32 0)).push (.i32 (readI64 memory (scratch.toNat+16)).toUInt32)) frame callers code)) rest post := by
    rw [paid_add]
    exact hnext
  have args := wp_vector_arguments cfg fuel rest gs limits stack frame callers code scratch mi index memory post
    h2 gm hi ge (by omega) gc next
  have guard := wp_present_guard cfg (fuel+7) (7*op+rest) s limits stack frame callers
    (WNear.Binary.StateReadRegisterOuter.vectorArguments++code) scratch mi index memory post
    h2 hm hi hmem (by omega) hn (hc.mono (by dsimp [op];omega)) args
  have cost : 5*cfg.regularOpCost+(7*op+rest)=12*cfg.regularOpCost+rest := by dsimp [op];omega
  rw [cost] at guard
  simpa only [List.append_assoc,Nat.add_assoc,Nat.reduceAdd] using guard
end WNear.Proofs.StateReadRegisterOuter
