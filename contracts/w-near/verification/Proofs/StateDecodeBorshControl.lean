import Binary.StateDecodeBorsh
import Proofs.StorePairCallerState
import NearVM.MeteredI32MemoryRules
import NearVM.MeteredNumericRules
import NearVM.MeteredLoopRules

/-! Actual425's three accepted tag guards. They test offset56 and leave their
current labels intact because the actual conditional branch is false. -/
namespace WNear.Proofs.StateDecodeBorsh
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
attribute [local irreducible] WP atCode readI32
private theorem modules_paid (s : Store NearState) (op n : Nat) : (paid s op n).modules=s.modules:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem mems_paid (s : Store NearState) (op n : Nat) : (paid s op n).mems=s.mems:=by
  induction n with|zero=>rfl|succ n ih=>exact ih

def guardCode (depth : Nat) : Expr := [.local_get 2,.load .i32 none {align:=2,offset:=56},.i32_const 1,.i32_relop .eq,.br_if depth]
theorem prefix_guard_exact : WNear.Binary.StateDecodeBorsh.prefixGuard=guardCode 0:=rfl
theorem wide_guard_exact : WNear.Binary.StateDecodeBorsh.wideGuard=guardCode 1:=rfl
theorem narrow_guard_exact : WNear.Binary.StateDecodeBorsh.narrowGuard=guardCode 0:=rfl

theorem wp_guard (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (depth : Nat) (pointer : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (h2 : frame.locals[2]?=some (.i32 pointer)) (hm : s.modules[frame.inst]?=some mi)
    (hi : mi.memAddrs[0]?=some index) (he : s.mems[index]?=some memory)
    (hb : pointer.toNat+60≤memory.byteSize) (hn : readI32 memory (pointer.toNat+56)≠1)
    (hc : s.host.gas.Credits (5*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 5) limits stack frame callers code)) rest post) :
    WP cfg (fuel+5) (.next (atCode s limits stack frame callers (guardCode depth++code)))
      (5*cfg.regularOpCost+rest) post := by
  let op:=cfg.regularOpCost
  let value:=readI32 memory (pointer.toNat+56)
  have zero : Numeric.bool (Numeric.irelop32 .eq value 1)=0:=by simp[Numeric.bool,Numeric.irelop32,value,hn]
  have branch:=wp_br_if_zero cfg fuel rest (paid s op 4) limits stack frame callers code depth post
    (paid_credits s op 4 _ (hc.mono (by dsimp[op];omega))) hnext
  have rel:=wp_i32_relop cfg (fuel+1) (op+rest) (paid s op 3) limits stack frame callers (.br_if depth::code) .eq value 1 post
    (paid_credits s op 3 _ (hc.mono (by dsimp[op];omega))) (by simpa only[zero,paid,op] using branch)
  have constant:=wp_i32_const cfg (fuel+2) (op+(op+rest)) (paid s op 2) limits (stack.push (.i32 value)) frame callers
    (.i32_relop .eq::.br_if depth::code) 1 post (paid_credits s op 2 _ (hc.mono (by dsimp[op];omega))) rel
  have load:=wp_i32_load cfg (fuel+3) (op+(op+(op+rest))) (paid s op 1) limits stack frame callers
    (.i32_const 1::.i32_relop .eq::.br_if depth::code) {align:=2,offset:=56} pointer mi index memory post
    (by rw[modules_paid];exact hm) hi (by rw[mems_paid];exact he) (by simpa only[Nat.add_zero] using hb)
    (paid_credits s op 1 _ (hc.mono (by dsimp[op];omega))) constant
  have get:=wp_local_get cfg (fuel+4) (op+(op+(op+(op+rest)))) s limits stack frame callers
    (.load .i32 none {align:=2,offset:=56}::.i32_const 1::.i32_relop .eq::.br_if depth::code) 2 (.i32 pointer) post h2
    (hc.mono (by dsimp[op];omega)) load
  simpa only[guardCode,List.cons_append,List.nil_append,
    show cfg.regularOpCost+(op+(op+(op+(op+rest))))=5*cfg.regularOpCost+rest by dsimp[op];omega] using get
end WNear.Proofs.StateDecodeBorsh
