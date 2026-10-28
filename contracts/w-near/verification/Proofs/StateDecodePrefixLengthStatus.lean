import Binary.StateDecodePrefix
import Proofs.StorePairCallerState
import NearVM.MeteredI32MemoryRules
import NearVM.MeteredLoopRules

/-! The real length helper's accepted zero tag skips the rejection branch. -/
namespace WNear.Proofs.StateDecodePrefix
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
attribute [local irreducible] WP atCode readI32
private theorem modules_paid (s : Store NearState) (op n : Nat) : (paid s op n).modules=s.modules := by
  induction n with |zero=>rfl|succ n ih=>exact ih
private theorem mems_paid (s : Store NearState) (op n : Nat) : (paid s op n).mems=s.mems := by
  induction n with |zero=>rfl|succ n ih=>exact ih

theorem wp_length_status (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (scratch : UInt32) (mi : ModuleInst) (i : Nat) (m : Memory) (post : Post)
    (h2 : frame.locals[2]?=some (.i32 scratch)) (hm : s.modules[frame.inst]?=some mi)
    (hi : mi.memAddrs[0]?=some i) (he : s.mems[i]?=some m) (hb : scratch.toNat+28≤m.byteSize)
    (hz : readI32 m (scratch.toNat+24)=0) (hc : s.host.gas.Credits (3*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 3) limits stack frame callers code)) rest post) :
    WP cfg (fuel+3) (.next (atCode s limits stack frame callers (WNear.Binary.StateDecodePrefix.lengthStatus++code)))
      (3*cfg.regularOpCost+rest) post := by
  let op:=cfg.regularOpCost
  have branch:=wp_br_if_zero cfg fuel rest (paid s op 2) limits stack frame callers code 2 post
    (paid_credits s op 2 _ (hc.mono (by dsimp[op];omega))) hnext
  have mm:(paid s op 1).modules[frame.inst]?=some mi:=by rw[modules_paid];exact hm
  have me:(paid s op 1).mems[i]?=some m:=by rw[mems_paid];exact he
  have load:=wp_i32_load cfg (fuel+1) (op+rest) (paid s op 1) limits stack frame callers (.br_if 2::code)
    {align:=2,offset:=24} scratch mi i m post mm hi me hb
    (paid_credits s op 1 _ (hc.mono (by dsimp[op];omega))) (by simpa only[hz,paid,op] using branch)
  have get:=wp_local_get cfg (fuel+2) (op+(op+rest)) s limits stack frame callers
    (.load .i32 none {align:=2,offset:=24}::.br_if 2::code) 2 (.i32 scratch) post h2 (hc.mono (by dsimp[op];omega)) load
  simpa only[WNear.Binary.StateDecodePrefix.lengthStatus,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd,
    show cfg.regularOpCost+(op+(op+rest))=3*cfg.regularOpCost+rest by dsimp[op];omega] using get
end WNear.Proofs.StateDecodePrefix
