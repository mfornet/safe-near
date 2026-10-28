import Proofs.StateDecodeScalarArguments
import Proofs.StateDecodeSlicesResult

/-! Real362 argument loads and accepted typed call in scalar wrappers. -/
namespace WNear.Proofs.StateDecodeScalar
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode readI32

private theorem modules_paid (s : Store NearState) (op n : Nat) : (paid s op n).modules=s.modules := by
  induction n with |zero=>rfl |succ n ih=>exact ih
private theorem mems_paid (s : Store NearState) (op n : Nat) : (paid s op n).mems=s.mems := by
  induction n with |zero=>rfl |succ n ih=>exact ih
private theorem funcs_paid (s : Store NearState) (op n : Nat) : (paid s op n).funcs=s.funcs := by
  induction n with |zero=>rfl |succ n ih=>exact ih

def takeAfter (cfg : WasmConfig) (s : Store NearState) (wide : Bool) (index : Nat) (memory : Memory) (scratch pointer len : UInt32) :=
  StateDecodeSlices.callAfter false (paid s cfg.regularOpCost 8) cfg.regularOpCost index memory
    (scratch+WNear.Binary.StateDecodeScalar.takeOffset wide) pointer len (WNear.Binary.StateDecodeScalar.width wide)

theorem wp_take_call (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (wide : Bool) (scratch slice pointer len : UInt32)
    (mi : ModuleInst) (index address : Nat) (memory : Memory) (post : Post)
    (h1 : frame.locals[1]?=some (.i32 slice)) (h2 : frame.locals[2]?=some (.i32 scratch)) (h3 : frame.locals[3]?=some (.i32 len))
    (hm : s.modules[frame.inst]?=some mi) (hi : mi.memAddrs[0]?=some index) (he : s.mems[index]?=some memory)
    (hfi : mi.funcAddrs[362]?=some address)
    (hf : s.funcs[address]?=some (.wasm WNear.Binary.StateDecodeSlices.signature frame.inst (WNear.Binary.StateDecodeSlices.function false)))
    (hwf : memory.wf) (hs : slice.toNat+4≤memory.byteSize)
    (ho : (scratch+WNear.Binary.StateDecodeScalar.takeOffset wide).toNat+8≤memory.byteSize)
    (hp : readI32 memory slice.toNat=pointer) (hn : (WNear.Binary.StateDecodeScalar.width wide).toNat≤len.toNat)
    (hd : callers.length+1<limits.maxCallDepth) (hc : s.host.gas.Credits (30*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (takeAfter cfg s wide index memory scratch pointer len) limits base.toArray frame callers code)) rest post) :
    WP cfg (fuel+21) (.next (atCode s limits base.toArray frame callers (WNear.Binary.StateDecodeScalar.takeArguments wide++code)))
      (30*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  let args := paid s op 8
  let out := scratch+WNear.Binary.StateDecodeScalar.takeOffset wide
  have mm : args.modules[frame.inst]?=some mi := by rw [modules_paid];exact hm
  have me : args.mems[index]?=some memory := by rw [mems_paid];exact he
  have mf : args.funcs[address]?=some (.wasm WNear.Binary.StateDecodeSlices.signature frame.inst (WNear.Binary.StateDecodeSlices.function false)) := by rw [funcs_paid];exact hf
  have ca := paid_credits s op 8 (22*op+rest) (hc.mono (by dsimp [op];omega))
  have next : WP cfg fuel (.next (atCode (StateDecodeSlices.callAfter false args op index memory out pointer len (WNear.Binary.StateDecodeScalar.width wide)) limits base.toArray frame callers code)) rest post := hnext
  have call := StateDecodeSlices.wp_call cfg fuel rest args limits base frame callers code false out pointer len
    (WNear.Binary.StateDecodeScalar.width wide) (WNear.Binary.StateDecodeScalar.location wide) mi index address memory post
    mm hi me hfi mf hwf ho hn hd ca next
  have operands : (base++[Value.i32 out,.i32 pointer,.i32 len,.i32 (WNear.Binary.StateDecodeScalar.width wide),.i32 (WNear.Binary.StateDecodeScalar.location wide)]).toArray=
      (((((base.toArray.push (.i32 out)).push (.i32 (readI32 memory (slice.toNat+0)))).push (.i32 len)).push (.i32 (WNear.Binary.StateDecodeScalar.width wide))).push (.i32 (WNear.Binary.StateDecodeScalar.location wide))) := by
    simp only [Nat.add_zero,hp]
    apply Array.toList_inj.mp;simp
  have cn : WP cfg (fuel+13) (.next (atCode args limits
      (((((base.toArray.push (.i32 out)).push (.i32 (readI32 memory (slice.toNat+0)))).push (.i32 len)).push (.i32 (WNear.Binary.StateDecodeScalar.width wide))).push (.i32 (WNear.Binary.StateDecodeScalar.location wide))) frame callers (.call 362::code))) (22*op+rest) post := by
    rw [operands] at call
    simpa only [WNear.Binary.StateDecodeSlices.index,WNear.Binary.StateDecodeSlices.bodySteps,WNear.Binary.StateDecodeSlices.bodyCost,
      Bool.false_eq_true,ite_false,Nat.reduceAdd,op] using call
  have arguments := wp_take_arguments cfg (fuel+13) (22*op+rest) s limits base.toArray frame callers (.call 362::code) wide scratch slice len mi index memory post
    h1 h2 h3 hm hi he (by simpa only [Nat.add_zero] using hs) (hc.mono (by dsimp [op];omega)) cn
  have ce : 8*cfg.regularOpCost+(22*op+rest)=30*cfg.regularOpCost+rest := by dsimp [op];omega
  rw [ce] at arguments
  simpa only [take_code_eq,List.append_assoc,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd] using arguments
end WNear.Proofs.StateDecodeScalar
