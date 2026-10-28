import Proofs.StateDecodePrefixGuard

/-! Actual scalar-decoder argument instructions, excluding the separately proved calls. -/
namespace WNear.Proofs.StateDecodePrefix
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode readI32
private theorem modules_paid (s : Store NearState) (op n : Nat) : (paid s op n).modules=s.modules := by
  induction n with |zero=>rfl |succ n ih=>exact ih
private theorem mems_paid (s : Store NearState) (op n : Nat) : (paid s op n).mems=s.mems := by
  induction n with |zero=>rfl |succ n ih=>exact ih

def takeCode : Expr := [.local_get 2,.i32_const (40),.i32_binop .add,.local_get 1,.load .i32 none {align:=2,offset:=0},.local_get 3,.i32_const (4),.i32_const (1052240)]

theorem wp_take_arguments (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (scratch slice len : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (h1 : frame.locals[1]?=some (.i32 slice))
    (h2 : frame.locals[2]?=some (.i32 scratch))
    (h3 : frame.locals[3]?=some (.i32 len))
    (hm : s.modules[frame.inst]?=some mi) (hi : mi.memAddrs[0]?=some index) (he : s.mems[index]?=some memory)
    (b4 : slice.toNat+(0)+4≤memory.byteSize)
    (hc : s.host.gas.Credits (8*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 8) limits
      ((((((stack).push (.i32 (scratch+(40)))).push (.i32 (readI32 memory (slice.toNat+(0))))).push (.i32 (len))).push (.i32 (4))).push (.i32 (1052240))) frame callers code)) rest post) :
    WP cfg (fuel+8) (.next (atCode s limits stack frame callers (takeCode++code)))
      (8*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  have mm4 : (paid s op 4).modules[frame.inst]?=some mi := by rw [modules_paid];exact hm
  have me4 : (paid s op 4).mems[index]?=some memory := by rw [mems_paid];exact he
  have p7 := wp_i32_const cfg fuel (rest) (paid s op 7) limits (((((stack).push (.i32 (scratch+(40)))).push (.i32 (readI32 memory (slice.toNat+(0))))).push (.i32 (len))).push (.i32 (4))) frame callers code (1052240) post  (paid_credits s op 7 _ (hc.mono (by dsimp [op];omega))) hnext
  have p6 := wp_i32_const cfg (fuel+1) (op+(rest)) (paid s op 6) limits ((((stack).push (.i32 (scratch+(40)))).push (.i32 (readI32 memory (slice.toNat+(0))))).push (.i32 (len))) frame callers (.i32_const (1052240)::code) (4) post  (paid_credits s op 6 _ (hc.mono (by dsimp [op];omega))) p7
  have p5 := wp_local_get cfg (fuel+2) (op+(op+(rest))) (paid s op 5) limits (((stack).push (.i32 (scratch+(40)))).push (.i32 (readI32 memory (slice.toNat+(0))))) frame callers (.i32_const (4)::.i32_const (1052240)::code) 3 (.i32 len) post h3 (paid_credits s op 5 _ (hc.mono (by dsimp [op];omega))) p6
  have p4 := wp_i32_load cfg (fuel+3) (op+(op+(op+(rest)))) (paid s op 4) limits ((stack).push (.i32 (scratch+(40)))) frame callers (.local_get 3::.i32_const (4)::.i32_const (1052240)::code) {align:=2,offset:=0} slice mi index memory post mm4 hi me4 b4 (paid_credits s op 4 _ (hc.mono (by dsimp [op];omega))) p5
  have p3 := wp_local_get cfg (fuel+4) (op+(op+(op+(op+(rest))))) (paid s op 3) limits ((stack).push (.i32 (scratch+(40)))) frame callers (.load .i32 none {align:=2,offset:=0}::.local_get 3::.i32_const (4)::.i32_const (1052240)::code) 1 (.i32 slice) post h1 (paid_credits s op 3 _ (hc.mono (by dsimp [op];omega))) p4
  have p2 := wp_i32_add cfg (fuel+5) (op+(op+(op+(op+(op+(rest)))))) (paid s op 2) limits (stack) frame callers (.local_get 1::.load .i32 none {align:=2,offset:=0}::.local_get 3::.i32_const (4)::.i32_const (1052240)::code) scratch (40) post  (paid_credits s op 2 _ (hc.mono (by dsimp [op];omega))) p3
  have p1 := wp_i32_const cfg (fuel+6) (op+(op+(op+(op+(op+(op+(rest))))))) (paid s op 1) limits ((stack).push (.i32 (scratch))) frame callers (.i32_binop .add::.local_get 1::.load .i32 none {align:=2,offset:=0}::.local_get 3::.i32_const (4)::.i32_const (1052240)::code) (40) post  (paid_credits s op 1 _ (hc.mono (by dsimp [op];omega))) p2
  have p0 := wp_local_get cfg (fuel+7) (op+(op+(op+(op+(op+(op+(op+(rest)))))))) s limits (stack) frame callers (.i32_const (40)::.i32_binop .add::.local_get 1::.load .i32 none {align:=2,offset:=0}::.local_get 3::.i32_const (4)::.i32_const (1052240)::code) 2 (.i32 scratch) post h2 (hc.mono (by dsimp [op];omega)) p1
  have cost : cfg.regularOpCost+(op+(op+(op+(op+(op+(op+(op+(rest))))))))=8*cfg.regularOpCost+rest := by dsimp [op];omega
  simpa only [takeCode,List.cons_append,List.nil_append,cost] using p0

theorem take_code_eq : WNear.Binary.StateDecodePrefix.takeFour=takeCode++[.call 362] := rfl
end WNear.Proofs.StateDecodePrefix
