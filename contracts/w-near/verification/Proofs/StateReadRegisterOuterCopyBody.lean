import Proofs.StateReadRegisterOuterCopyReadback

/-! Both523 result copies are composed with the actual intermediate memory. -/
namespace WNear.Proofs.StateReadRegisterOuter
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode copyHigh copyLow firstMemory

def copied (s : Store NearState) (op index : Nat) (memory : Memory) (out scratch : UInt32) :=
  copyLow (copyHigh s op index memory out scratch) op index (firstMemory memory out scratch) out scratch

private theorem mems_paid (s : Store NearState) (op n : Nat) : (paid s op n).mems=s.mems := by
  induction n with | zero=>rfl | succ n ih=>exact ih
private theorem modules_paid (s : Store NearState) (op n : Nat) : (paid s op n).modules=s.modules := by
  induction n with | zero=>rfl | succ n ih=>exact ih

theorem wp_copy (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (out scratch : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (ho : frame.locals[0]?=some (.i32 out)) (hs : frame.locals[2]?=some (.i32 scratch))
    (hm : s.modules[frame.inst]?=some mi) (hi : mi.memAddrs[0]?=some index) (hmem : s.mems[index]?=some memory)
    (hwf : memory.wf) (hrh : (scratch+32+8).toNat+4≤memory.byteSize) (hwh : (out+8).toNat+4≤memory.byteSize)
    (hrl : scratch.toNat+32+8≤memory.byteSize) (hwl : out.toNat+8≤memory.byteSize)
    (hc : s.host.gas.Credits (14*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (copied s cfg.regularOpCost index memory out scratch) limits stack frame callers code)) rest post) :
    WP cfg (fuel+14) (.next (atCode s limits stack frame callers
      (WNear.Binary.StateReadRegisterOuter.copyHigh++WNear.Binary.StateReadRegisterOuter.copyLow++code)))
      (14*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  let one := copyHigh s op index memory out scratch
  have spec := firstMemory_spec memory out scratch hwf hwh
  have me : one.mems[index]?=some (firstMemory memory out scratch) := by
    have h : (paid s op 10).mems[index]?=some memory := by rw [mems_paid];exact hmem
    simpa only [one,copyHigh,firstMemory] using storeI32_memory (paid s op 10) index (out+8).toNat memory (readI32 memory (scratch+32+8).toNat) h
  have mo : one.modules[frame.inst]?=some mi := by
    simp only [one,copyHigh,storeI32_modules,modules_paid];exact hm
  have credits : one.host.gas.Credits (4*op+rest) := by
    simpa only [one,copyHigh,storeI32_host] using paid_credits s op 10 (4*op+rest) (hc.mono (by dsimp [op];omega))
  have low := wp_copy_low cfg fuel rest one limits stack frame callers code out scratch mi index (firstMemory memory out scratch) post ho hs mo hi me
    (by rw [spec.2.1];exact hrl) (by rw [spec.2.1];exact hwl) credits hnext
  have high := wp_copy_high cfg (fuel+4) (4*op+rest) s limits stack frame callers (WNear.Binary.StateReadRegisterOuter.copyLow++code)
    out scratch mi index memory post ho hs hm hi hmem hrh hwh (hc.mono (by dsimp [op];omega)) low
  have ce : 10*cfg.regularOpCost+(4*op+rest)=14*cfg.regularOpCost+rest := by dsimp [op];omega
  rw [ce] at high
  simpa only [List.append_assoc,Nat.add_assoc,Nat.reduceAdd] using high
end WNear.Proofs.StateReadRegisterOuter
