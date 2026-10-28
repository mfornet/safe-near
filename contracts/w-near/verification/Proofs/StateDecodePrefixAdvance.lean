import Binary.StateDecodePrefix
import Proofs.StorePairCallerState
import NearVM.MeteredScalarRules
import NearVM.MeteredMemoryRules

/-! The actual four-instruction slice descriptor advance loads before writing,
so arbitrary source/destination aliases retain their sequential meaning. -/
namespace WNear.Proofs.StateDecodePrefix
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
attribute [local irreducible] WP atCode readI64
private theorem modules_paid (s : Store NearState) (op n : Nat) : (paid s op n).modules=s.modules := by
  induction n with |zero=>rfl|succ n ih=>exact ih
private theorem mems_paid (s : Store NearState) (op n : Nat) : (paid s op n).mems=s.mems := by
  induction n with |zero=>rfl|succ n ih=>exact ih

def advanceAfter (s : Store NearState) (op i : Nat) (m : Memory) (scratch slice : UInt32) :=
  storeI64 (paid s op 4) i slice.toNat m (readI64 m (scratch.toNat+32))

theorem wp_advance_four (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame) (code : Expr)
    (scratch slice : UInt32) (mi : ModuleInst) (i : Nat) (m : Memory) (post : Post)
    (h1 : frame.locals[1]?=some (.i32 slice)) (h2 : frame.locals[2]?=some (.i32 scratch))
    (hm : s.modules[frame.inst]?=some mi) (hi : mi.memAddrs[0]?=some i) (he : s.mems[i]?=some m)
    (hbS : scratch.toNat+40≤m.byteSize) (hbT : slice.toNat+8≤m.byteSize)
    (hc : s.host.gas.Credits (4*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (advanceAfter s cfg.regularOpCost i m scratch slice) limits stack frame callers code)) rest post) :
    WP cfg (fuel+4) (.next (atCode s limits stack frame callers (WNear.Binary.StateDecodePrefix.advanceFour++code)))
      (4*cfg.regularOpCost+rest) post := by
  let op:=cfg.regularOpCost
  have mm2 : (paid s op 2).modules[frame.inst]?=some mi:=by rw[modules_paid];exact hm
  have mm3 : (paid s op 3).modules[frame.inst]?=some mi:=by rw[modules_paid];exact hm
  have me2 : (paid s op 2).mems[i]?=some m:=by rw[mems_paid];exact he
  have me3 : (paid s op 3).mems[i]?=some m:=by rw[mems_paid];exact he
  have store:=wp_i64_store cfg fuel rest (paid s op 3) limits stack frame callers code {align:=2,offset:=0} slice
    (readI64 m (scratch.toNat+32)) mi i m post mm3 hi me3 hbT (paid_credits s op 3 _ (hc.mono (by dsimp[op];omega))) hnext
  have load:=wp_i64_load cfg (fuel+1) (op+rest) (paid s op 2) limits (stack.push (.i32 slice)) frame callers
    (.store .i64 none {align:=2,offset:=0}::code) {align:=3,offset:=32} scratch mi i m post mm2 hi me2 hbS
    (paid_credits s op 2 _ (hc.mono (by dsimp[op];omega))) store
  have source:=wp_local_get cfg (fuel+2) (op+(op+rest)) (paid s op 1) limits (stack.push (.i32 slice)) frame callers
    (.load .i64 none {align:=3,offset:=32}::.store .i64 none {align:=2,offset:=0}::code) 2 (.i32 scratch) post h2
    (paid_credits s op 1 _ (hc.mono (by dsimp[op];omega))) load
  have target:=wp_local_get cfg (fuel+3) (op+(op+(op+rest))) s limits stack frame callers
    (.local_get 2::.load .i64 none {align:=3,offset:=32}::.store .i64 none {align:=2,offset:=0}::code) 1 (.i32 slice) post h1
    (hc.mono (by dsimp[op];omega)) source
  simpa only[WNear.Binary.StateDecodePrefix.advanceFour,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd,
    show cfg.regularOpCost+(op+(op+(op+rest)))=4*cfg.regularOpCost+rest by dsimp[op];omega] using target
end WNear.Proofs.StateDecodePrefix
