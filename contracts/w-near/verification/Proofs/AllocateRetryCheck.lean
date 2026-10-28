import Proofs.AllocateRetryArguments

/-! The actual successful growth result check in581. -/
namespace WNear.Proofs.AllocateRetry
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode

theorem wp_record_check (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (record : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (h3 : frame.locals[3]?=some (.i32 record)) (hm : s.modules[frame.inst]?=some mi)
    (hi : mi.memAddrs[0]?=some index) (hmem : s.mems[index]?=some memory)
    (hb : record.toNat+4≤memory.byteSize) (hz : readI32 memory record.toNat=0)
    (hc : s.host.gas.Credits (5*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 5) limits stack (missedFrame frame) callers code)) rest post) :
    WP cfg (fuel+5) (.next (atCode s limits stack frame callers (WNear.Binary.AllocateRetry.growthCheck++code)))
      (5*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  let ff := missedFrame frame
  have h3f : ff.locals[3]?=some (.i32 record) := by simp [ff,missedFrame,h3]
  have branch := wp_br_if_zero cfg fuel rest (paid s op 4) limits stack ff callers code 0 post
    (paid_credits s op 4 _ (hc.mono (by dsimp [op];omega))) hnext
  have load := wp_i32_load cfg (fuel+1) (op+rest) (paid s op 3) limits stack ff callers (.br_if 0::code)
    {align:=2,offset:=0} record mi index memory post hm hi hmem hb
    (paid_credits s op 3 _ (hc.mono (by dsimp [op];omega)))
    (by simpa only [Nat.add_zero,hz,paid,op] using branch)
  have get := wp_local_get cfg (fuel+2) (op+(op+rest)) (paid s op 2) limits stack ff callers
    (.load .i32 none {align:=2,offset:=0}::.br_if 0::code) 3 (.i32 record) post h3f
    (paid_credits s op 2 _ (hc.mono (by dsimp [op];omega))) load
  have set := wp_local_set cfg (fuel+3) (op+(op+(op+rest))) (paid s op 1) limits stack frame callers
    (.local_get 3::.load .i32 none {align:=2,offset:=0}::.br_if 0::code) 1 (.i32 0) post
    (paid_credits s op 1 _ (hc.mono (by dsimp [op];omega))) get
  have first := wp_i32_const cfg (fuel+4) (op+(op+(op+(op+rest)))) s limits stack frame callers _ 0 post
    (hc.mono (by dsimp [op];omega)) set
  have cost : cfg.regularOpCost+(op+(op+(op+(op+rest))))=5*cfg.regularOpCost+rest := by dsimp [op];omega
  simpa only [WNear.Binary.AllocateRetry.growthCheck,List.append_eq,List.cons_append,List.nil_append,cost,Nat.add_assoc,Nat.reduceAdd] using first
end WNear.Proofs.AllocateRetry
