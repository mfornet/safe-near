import Proofs.StateDecodeScalarTakeCall

/-! Actual361 remainder call rereads the current descriptor after word decoding. -/
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

def dropArgumentCount (wide : Bool) : Nat := if wide then 7 else 9
def dropAfter (cfg : WasmConfig) (s : Store NearState) (wide : Bool) (index : Nat) (memory : Memory) (scratch pointer len : UInt32) :=
  StateDecodeSlices.callAfter true (paid s cfg.regularOpCost (dropArgumentCount wide)) cfg.regularOpCost index memory
    (scratch+(if wide then 0 else 8)) pointer len (WNear.Binary.StateDecodeScalar.width wide)

theorem wp_drop_call (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (wide : Bool) (scratch slice pointer len : UInt32)
    (mi : ModuleInst) (index address : Nat) (memory : Memory) (post : Post)
    (h1 : frame.locals[1]?=some (.i32 slice)) (h2 : frame.locals[2]?=some (.i32 scratch))
    (hm : s.modules[frame.inst]?=some mi) (hi : mi.memAddrs[0]?=some index) (he : s.mems[index]?=some memory)
    (hfi : mi.funcAddrs[361]?=some address)
    (hf : s.funcs[address]?=some (.wasm WNear.Binary.StateDecodeSlices.signature frame.inst (WNear.Binary.StateDecodeSlices.function true)))
    (hwf : memory.wf) (hs : slice.toNat+8≤memory.byteSize)
    (ho : (scratch+(if wide then 0 else 8)).toNat+8≤memory.byteSize)
    (hp : readI32 memory slice.toNat=pointer) (hl : readI32 memory (slice.toNat+4)=len)
    (hn : (WNear.Binary.StateDecodeScalar.width wide).toNat≤len.toNat)
    (hd : callers.length+1<limits.maxCallDepth)
    (hc : s.host.gas.Credits ((dropArgumentCount wide+26)*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (dropAfter cfg s wide index memory scratch pointer len) limits base.toArray frame callers code)) rest post) :
    WP cfg (fuel+dropArgumentCount wide+17) (.next (atCode s limits base.toArray frame callers (WNear.Binary.StateDecodeScalar.dropArguments wide++code)))
      ((dropArgumentCount wide+26)*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  let args := paid s op (dropArgumentCount wide)
  let out := scratch+(if wide then 0 else 8)
  have mm : args.modules[frame.inst]?=some mi := by rw [modules_paid];exact hm
  have me : args.mems[index]?=some memory := by rw [mems_paid];exact he
  have mf : args.funcs[address]?=some (.wasm WNear.Binary.StateDecodeSlices.signature frame.inst (WNear.Binary.StateDecodeSlices.function true)) := by rw [funcs_paid];exact hf
  have ca := paid_credits s op (dropArgumentCount wide) (26*op+rest) (hc.mono (by simp only [Nat.add_mul,op];omega))
  have next : WP cfg fuel (.next (atCode (StateDecodeSlices.callAfter true args op index memory out pointer len (WNear.Binary.StateDecodeScalar.width wide)) limits base.toArray frame callers code)) rest post := hnext
  have call := StateDecodeSlices.wp_call cfg fuel rest args limits base frame callers code true out pointer len
    (WNear.Binary.StateDecodeScalar.width wide) (WNear.Binary.StateDecodeScalar.location wide) mi index address memory post
    mm hi me hfi mf hwf ho hn hd ca next
  let argv := ((((base.toArray.push (.i32 out)).push (.i32 (readI32 memory (slice.toNat+0)))).push (.i32 (readI32 memory (slice.toNat+4)))).push
    (.i32 (WNear.Binary.StateDecodeScalar.width wide))).push (.i32 (WNear.Binary.StateDecodeScalar.location wide))
  have operands : (base++[Value.i32 out,.i32 pointer,.i32 len,.i32 (WNear.Binary.StateDecodeScalar.width wide),.i32 (WNear.Binary.StateDecodeScalar.location wide)]).toArray=argv := by
    dsimp only [argv]
    rw [Nat.add_zero,hp,hl];apply Array.toList_inj.mp;simp
  have cn : WP cfg (fuel+17) (.next (atCode args limits argv frame callers (.call 361::code))) (26*op+rest) post := by
    rw [operands] at call
    simpa only [WNear.Binary.StateDecodeSlices.index,WNear.Binary.StateDecodeSlices.bodySteps,WNear.Binary.StateDecodeSlices.bodyCost,
      ite_true,Nat.reduceAdd,op] using call
  have inputs : WP cfg ((fuel+17)+dropArgumentCount wide) (.next (atCode s limits base.toArray frame callers
      ((if wide then dropCodeWide else dropCodeNarrow)++(.call 361::code)))) (dropArgumentCount wide*cfg.regularOpCost+(26*op+rest)) post := by
    cases wide with
    | false =>
      have proof := wp_drop_arguments_narrow cfg (fuel+17) (26*op+rest) s limits base.toArray frame callers (.call 361::code) scratch slice 0 mi index memory post
        h1 h2 hm hi he (by omega) (by omega) (hc.mono (by simp only [dropArgumentCount,Bool.false_eq_true,ite_false,op];omega))
        (by simpa only [args,argv,out,dropArgumentCount,WNear.Binary.StateDecodeScalar.width,WNear.Binary.StateDecodeScalar.location,Bool.false_eq_true,ite_false,op] using cn)
      simpa only [dropArgumentCount,Bool.false_eq_true,ite_false] using proof
    | true =>
      have proof := wp_drop_arguments_wide cfg (fuel+17) (26*op+rest) s limits base.toArray frame callers (.call 361::code) scratch slice 0 mi index memory post
        h1 h2 hm hi he (by omega) (by omega) (hc.mono (by simp only [dropArgumentCount,ite_true,op];omega))
        (by simpa only [args,argv,out,dropArgumentCount,WNear.Binary.StateDecodeScalar.width,WNear.Binary.StateDecodeScalar.location,ite_true,UInt32.add_zero,op] using cn)
      simpa only [dropArgumentCount,ite_true] using proof
  have ce : dropArgumentCount wide*cfg.regularOpCost+(26*op+rest)=(dropArgumentCount wide+26)*cfg.regularOpCost+rest := by simp only [Nat.add_mul,op];omega
  rw [ce] at inputs
  simpa only [drop_code_eq,List.append_assoc,List.cons_append,List.nil_append,Nat.add_right_comm] using inputs
end WNear.Proofs.StateDecodeScalar
