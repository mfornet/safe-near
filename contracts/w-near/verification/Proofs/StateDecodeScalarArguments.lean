import Proofs.StateDecodeScalarGuard

/-! Actual scalar-decoder argument instructions, excluding the separately proved calls. -/
namespace WNear.Proofs.StateDecodeScalar
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode readI32
private theorem modules_paid (s : Store NearState) (op n : Nat) : (paid s op n).modules=s.modules := by
  induction n with |zero=>rfl |succ n ih=>exact ih
private theorem mems_paid (s : Store NearState) (op n : Nat) : (paid s op n).mems=s.mems := by
  induction n with |zero=>rfl |succ n ih=>exact ih

def takeCode (wide : Bool) : Expr := [.local_get 2,.i32_const (WNear.Binary.StateDecodeScalar.takeOffset wide),.i32_binop .add,.local_get 1,.load .i32 none {align:=2,offset:=0},.local_get 3,.i32_const (WNear.Binary.StateDecodeScalar.width wide),.i32_const (WNear.Binary.StateDecodeScalar.location wide)]

theorem wp_take_arguments (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (wide : Bool) (scratch slice len : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (h1 : frame.locals[1]?=some (.i32 slice))
    (h2 : frame.locals[2]?=some (.i32 scratch))
    (h3 : frame.locals[3]?=some (.i32 len))
    (hm : s.modules[frame.inst]?=some mi) (hi : mi.memAddrs[0]?=some index) (he : s.mems[index]?=some memory)
    (b4 : slice.toNat+(0)+4≤memory.byteSize)
    (hc : s.host.gas.Credits (8*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 8) limits
      ((((((stack).push (.i32 (scratch+(WNear.Binary.StateDecodeScalar.takeOffset wide)))).push (.i32 (readI32 memory (slice.toNat+(0))))).push (.i32 (len))).push (.i32 (WNear.Binary.StateDecodeScalar.width wide))).push (.i32 (WNear.Binary.StateDecodeScalar.location wide))) frame callers code)) rest post) :
    WP cfg (fuel+8) (.next (atCode s limits stack frame callers (takeCode wide++code)))
      (8*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  have mm4 : (paid s op 4).modules[frame.inst]?=some mi := by rw [modules_paid];exact hm
  have me4 : (paid s op 4).mems[index]?=some memory := by rw [mems_paid];exact he
  have p7 := wp_i32_const cfg fuel (rest) (paid s op 7) limits (((((stack).push (.i32 (scratch+(WNear.Binary.StateDecodeScalar.takeOffset wide)))).push (.i32 (readI32 memory (slice.toNat+(0))))).push (.i32 (len))).push (.i32 (WNear.Binary.StateDecodeScalar.width wide))) frame callers code (WNear.Binary.StateDecodeScalar.location wide) post  (paid_credits s op 7 _ (hc.mono (by dsimp [op];omega))) hnext
  have p6 := wp_i32_const cfg (fuel+1) (op+(rest)) (paid s op 6) limits ((((stack).push (.i32 (scratch+(WNear.Binary.StateDecodeScalar.takeOffset wide)))).push (.i32 (readI32 memory (slice.toNat+(0))))).push (.i32 (len))) frame callers (.i32_const (WNear.Binary.StateDecodeScalar.location wide)::code) (WNear.Binary.StateDecodeScalar.width wide) post  (paid_credits s op 6 _ (hc.mono (by dsimp [op];omega))) p7
  have p5 := wp_local_get cfg (fuel+2) (op+(op+(rest))) (paid s op 5) limits (((stack).push (.i32 (scratch+(WNear.Binary.StateDecodeScalar.takeOffset wide)))).push (.i32 (readI32 memory (slice.toNat+(0))))) frame callers (.i32_const (WNear.Binary.StateDecodeScalar.width wide)::.i32_const (WNear.Binary.StateDecodeScalar.location wide)::code) 3 (.i32 len) post h3 (paid_credits s op 5 _ (hc.mono (by dsimp [op];omega))) p6
  have p4 := wp_i32_load cfg (fuel+3) (op+(op+(op+(rest)))) (paid s op 4) limits ((stack).push (.i32 (scratch+(WNear.Binary.StateDecodeScalar.takeOffset wide)))) frame callers (.local_get 3::.i32_const (WNear.Binary.StateDecodeScalar.width wide)::.i32_const (WNear.Binary.StateDecodeScalar.location wide)::code) {align:=2,offset:=0} slice mi index memory post mm4 hi me4 b4 (paid_credits s op 4 _ (hc.mono (by dsimp [op];omega))) p5
  have p3 := wp_local_get cfg (fuel+4) (op+(op+(op+(op+(rest))))) (paid s op 3) limits ((stack).push (.i32 (scratch+(WNear.Binary.StateDecodeScalar.takeOffset wide)))) frame callers (.load .i32 none {align:=2,offset:=0}::.local_get 3::.i32_const (WNear.Binary.StateDecodeScalar.width wide)::.i32_const (WNear.Binary.StateDecodeScalar.location wide)::code) 1 (.i32 slice) post h1 (paid_credits s op 3 _ (hc.mono (by dsimp [op];omega))) p4
  have p2 := wp_i32_add cfg (fuel+5) (op+(op+(op+(op+(op+(rest)))))) (paid s op 2) limits (stack) frame callers (.local_get 1::.load .i32 none {align:=2,offset:=0}::.local_get 3::.i32_const (WNear.Binary.StateDecodeScalar.width wide)::.i32_const (WNear.Binary.StateDecodeScalar.location wide)::code) scratch (WNear.Binary.StateDecodeScalar.takeOffset wide) post  (paid_credits s op 2 _ (hc.mono (by dsimp [op];omega))) p3
  have p1 := wp_i32_const cfg (fuel+6) (op+(op+(op+(op+(op+(op+(rest))))))) (paid s op 1) limits ((stack).push (.i32 (scratch))) frame callers (.i32_binop .add::.local_get 1::.load .i32 none {align:=2,offset:=0}::.local_get 3::.i32_const (WNear.Binary.StateDecodeScalar.width wide)::.i32_const (WNear.Binary.StateDecodeScalar.location wide)::code) (WNear.Binary.StateDecodeScalar.takeOffset wide) post  (paid_credits s op 1 _ (hc.mono (by dsimp [op];omega))) p2
  have p0 := wp_local_get cfg (fuel+7) (op+(op+(op+(op+(op+(op+(op+(rest)))))))) s limits (stack) frame callers (.i32_const (WNear.Binary.StateDecodeScalar.takeOffset wide)::.i32_binop .add::.local_get 1::.load .i32 none {align:=2,offset:=0}::.local_get 3::.i32_const (WNear.Binary.StateDecodeScalar.width wide)::.i32_const (WNear.Binary.StateDecodeScalar.location wide)::code) 2 (.i32 scratch) post h2 (hc.mono (by dsimp [op];omega)) p1
  have cost : cfg.regularOpCost+(op+(op+(op+(op+(op+(op+(op+(rest))))))))=8*cfg.regularOpCost+rest := by dsimp [op];omega
  simpa only [takeCode,List.cons_append,List.nil_append,cost] using p0

def wordCode (wide : Bool) : Expr := [.local_get 2,.i32_const (WNear.Binary.StateDecodeScalar.wordOffset wide),.i32_binop .add,.local_get 2,.load .i32 none {align:=2,offset:=(WNear.Binary.StateDecodeScalar.takeOffset wide).toNat},.local_get 2,.load .i32 none {align:=2,offset:=(WNear.Binary.StateDecodeScalar.takeOffset wide).toNat+4}]

theorem wp_word_arguments (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (wide : Bool) (scratch _slice _len : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (h2 : frame.locals[2]?=some (.i32 scratch))
    (hm : s.modules[frame.inst]?=some mi) (hi : mi.memAddrs[0]?=some index) (he : s.mems[index]?=some memory)
    (b4 : scratch.toNat+((WNear.Binary.StateDecodeScalar.takeOffset wide).toNat)+4≤memory.byteSize)
    (b6 : scratch.toNat+((WNear.Binary.StateDecodeScalar.takeOffset wide).toNat+4)+4≤memory.byteSize)
    (hc : s.host.gas.Credits (7*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 7) limits
      ((((stack).push (.i32 (scratch+(WNear.Binary.StateDecodeScalar.wordOffset wide)))).push (.i32 (readI32 memory (scratch.toNat+((WNear.Binary.StateDecodeScalar.takeOffset wide).toNat))))).push (.i32 (readI32 memory (scratch.toNat+((WNear.Binary.StateDecodeScalar.takeOffset wide).toNat+4))))) frame callers code)) rest post) :
    WP cfg (fuel+7) (.next (atCode s limits stack frame callers (wordCode wide++code)))
      (7*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  have mm4 : (paid s op 4).modules[frame.inst]?=some mi := by rw [modules_paid];exact hm
  have me4 : (paid s op 4).mems[index]?=some memory := by rw [mems_paid];exact he
  have mm6 : (paid s op 6).modules[frame.inst]?=some mi := by rw [modules_paid];exact hm
  have me6 : (paid s op 6).mems[index]?=some memory := by rw [mems_paid];exact he
  have p6 := wp_i32_load cfg fuel (rest) (paid s op 6) limits (((stack).push (.i32 (scratch+(WNear.Binary.StateDecodeScalar.wordOffset wide)))).push (.i32 (readI32 memory (scratch.toNat+((WNear.Binary.StateDecodeScalar.takeOffset wide).toNat))))) frame callers code {align:=2,offset:=(WNear.Binary.StateDecodeScalar.takeOffset wide).toNat+4} scratch mi index memory post mm6 hi me6 b6 (paid_credits s op 6 _ (hc.mono (by dsimp [op];omega))) hnext
  have p5 := wp_local_get cfg (fuel+1) (op+(rest)) (paid s op 5) limits (((stack).push (.i32 (scratch+(WNear.Binary.StateDecodeScalar.wordOffset wide)))).push (.i32 (readI32 memory (scratch.toNat+((WNear.Binary.StateDecodeScalar.takeOffset wide).toNat))))) frame callers (.load .i32 none {align:=2,offset:=(WNear.Binary.StateDecodeScalar.takeOffset wide).toNat+4}::code) 2 (.i32 scratch) post h2 (paid_credits s op 5 _ (hc.mono (by dsimp [op];omega))) p6
  have p4 := wp_i32_load cfg (fuel+2) (op+(op+(rest))) (paid s op 4) limits ((stack).push (.i32 (scratch+(WNear.Binary.StateDecodeScalar.wordOffset wide)))) frame callers (.local_get 2::.load .i32 none {align:=2,offset:=(WNear.Binary.StateDecodeScalar.takeOffset wide).toNat+4}::code) {align:=2,offset:=(WNear.Binary.StateDecodeScalar.takeOffset wide).toNat} scratch mi index memory post mm4 hi me4 b4 (paid_credits s op 4 _ (hc.mono (by dsimp [op];omega))) p5
  have p3 := wp_local_get cfg (fuel+3) (op+(op+(op+(rest)))) (paid s op 3) limits ((stack).push (.i32 (scratch+(WNear.Binary.StateDecodeScalar.wordOffset wide)))) frame callers (.load .i32 none {align:=2,offset:=(WNear.Binary.StateDecodeScalar.takeOffset wide).toNat}::.local_get 2::.load .i32 none {align:=2,offset:=(WNear.Binary.StateDecodeScalar.takeOffset wide).toNat+4}::code) 2 (.i32 scratch) post h2 (paid_credits s op 3 _ (hc.mono (by dsimp [op];omega))) p4
  have p2 := wp_i32_add cfg (fuel+4) (op+(op+(op+(op+(rest))))) (paid s op 2) limits (stack) frame callers (.local_get 2::.load .i32 none {align:=2,offset:=(WNear.Binary.StateDecodeScalar.takeOffset wide).toNat}::.local_get 2::.load .i32 none {align:=2,offset:=(WNear.Binary.StateDecodeScalar.takeOffset wide).toNat+4}::code) scratch (WNear.Binary.StateDecodeScalar.wordOffset wide) post  (paid_credits s op 2 _ (hc.mono (by dsimp [op];omega))) p3
  have p1 := wp_i32_const cfg (fuel+5) (op+(op+(op+(op+(op+(rest)))))) (paid s op 1) limits ((stack).push (.i32 (scratch))) frame callers (.i32_binop .add::.local_get 2::.load .i32 none {align:=2,offset:=(WNear.Binary.StateDecodeScalar.takeOffset wide).toNat}::.local_get 2::.load .i32 none {align:=2,offset:=(WNear.Binary.StateDecodeScalar.takeOffset wide).toNat+4}::code) (WNear.Binary.StateDecodeScalar.wordOffset wide) post  (paid_credits s op 1 _ (hc.mono (by dsimp [op];omega))) p2
  have p0 := wp_local_get cfg (fuel+6) (op+(op+(op+(op+(op+(op+(rest))))))) s limits (stack) frame callers (.i32_const (WNear.Binary.StateDecodeScalar.wordOffset wide)::.i32_binop .add::.local_get 2::.load .i32 none {align:=2,offset:=(WNear.Binary.StateDecodeScalar.takeOffset wide).toNat}::.local_get 2::.load .i32 none {align:=2,offset:=(WNear.Binary.StateDecodeScalar.takeOffset wide).toNat+4}::code) 2 (.i32 scratch) post h2 (hc.mono (by dsimp [op];omega)) p1
  have cost : cfg.regularOpCost+(op+(op+(op+(op+(op+(op+(rest)))))))=7*cfg.regularOpCost+rest := by dsimp [op];omega
  simpa only [wordCode,List.cons_append,List.nil_append,cost] using p0

def dropCodeWide : Expr := [.local_get 2,.local_get 1,.load .i32 none {align:=2,offset:=0},.local_get 1,.load .i32 none {align:=2,offset:=4},.i32_const (16),.i32_const (1052272)]

theorem wp_drop_arguments_wide (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (scratch slice _len : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (h1 : frame.locals[1]?=some (.i32 slice))
    (h2 : frame.locals[2]?=some (.i32 scratch))
    (hm : s.modules[frame.inst]?=some mi) (hi : mi.memAddrs[0]?=some index) (he : s.mems[index]?=some memory)
    (b2 : slice.toNat+(0)+4≤memory.byteSize)
    (b4 : slice.toNat+(4)+4≤memory.byteSize)
    (hc : s.host.gas.Credits (7*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 7) limits
      ((((((stack).push (.i32 (scratch))).push (.i32 (readI32 memory (slice.toNat+(0))))).push (.i32 (readI32 memory (slice.toNat+(4))))).push (.i32 (16))).push (.i32 (1052272))) frame callers code)) rest post) :
    WP cfg (fuel+7) (.next (atCode s limits stack frame callers (dropCodeWide++code)))
      (7*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  have mm2 : (paid s op 2).modules[frame.inst]?=some mi := by rw [modules_paid];exact hm
  have me2 : (paid s op 2).mems[index]?=some memory := by rw [mems_paid];exact he
  have mm4 : (paid s op 4).modules[frame.inst]?=some mi := by rw [modules_paid];exact hm
  have me4 : (paid s op 4).mems[index]?=some memory := by rw [mems_paid];exact he
  have p6 := wp_i32_const cfg fuel (rest) (paid s op 6) limits (((((stack).push (.i32 (scratch))).push (.i32 (readI32 memory (slice.toNat+(0))))).push (.i32 (readI32 memory (slice.toNat+(4))))).push (.i32 (16))) frame callers code (1052272) post  (paid_credits s op 6 _ (hc.mono (by dsimp [op];omega))) hnext
  have p5 := wp_i32_const cfg (fuel+1) (op+(rest)) (paid s op 5) limits ((((stack).push (.i32 (scratch))).push (.i32 (readI32 memory (slice.toNat+(0))))).push (.i32 (readI32 memory (slice.toNat+(4))))) frame callers (.i32_const (1052272)::code) (16) post  (paid_credits s op 5 _ (hc.mono (by dsimp [op];omega))) p6
  have p4 := wp_i32_load cfg (fuel+2) (op+(op+(rest))) (paid s op 4) limits (((stack).push (.i32 (scratch))).push (.i32 (readI32 memory (slice.toNat+(0))))) frame callers (.i32_const (16)::.i32_const (1052272)::code) {align:=2,offset:=4} slice mi index memory post mm4 hi me4 b4 (paid_credits s op 4 _ (hc.mono (by dsimp [op];omega))) p5
  have p3 := wp_local_get cfg (fuel+3) (op+(op+(op+(rest)))) (paid s op 3) limits (((stack).push (.i32 (scratch))).push (.i32 (readI32 memory (slice.toNat+(0))))) frame callers (.load .i32 none {align:=2,offset:=4}::.i32_const (16)::.i32_const (1052272)::code) 1 (.i32 slice) post h1 (paid_credits s op 3 _ (hc.mono (by dsimp [op];omega))) p4
  have p2 := wp_i32_load cfg (fuel+4) (op+(op+(op+(op+(rest))))) (paid s op 2) limits ((stack).push (.i32 (scratch))) frame callers (.local_get 1::.load .i32 none {align:=2,offset:=4}::.i32_const (16)::.i32_const (1052272)::code) {align:=2,offset:=0} slice mi index memory post mm2 hi me2 b2 (paid_credits s op 2 _ (hc.mono (by dsimp [op];omega))) p3
  have p1 := wp_local_get cfg (fuel+5) (op+(op+(op+(op+(op+(rest)))))) (paid s op 1) limits ((stack).push (.i32 (scratch))) frame callers (.load .i32 none {align:=2,offset:=0}::.local_get 1::.load .i32 none {align:=2,offset:=4}::.i32_const (16)::.i32_const (1052272)::code) 1 (.i32 slice) post h1 (paid_credits s op 1 _ (hc.mono (by dsimp [op];omega))) p2
  have p0 := wp_local_get cfg (fuel+6) (op+(op+(op+(op+(op+(op+(rest))))))) s limits (stack) frame callers (.local_get 1::.load .i32 none {align:=2,offset:=0}::.local_get 1::.load .i32 none {align:=2,offset:=4}::.i32_const (16)::.i32_const (1052272)::code) 2 (.i32 scratch) post h2 (hc.mono (by dsimp [op];omega)) p1
  have cost : cfg.regularOpCost+(op+(op+(op+(op+(op+(op+(rest)))))))=7*cfg.regularOpCost+rest := by dsimp [op];omega
  simpa only [dropCodeWide,List.cons_append,List.nil_append,cost] using p0

def dropCodeNarrow : Expr := [.local_get 2,.i32_const (8),.i32_binop .add,.local_get 1,.load .i32 none {align:=2,offset:=0},.local_get 1,.load .i32 none {align:=2,offset:=4},.i32_const (8),.i32_const (1052256)]

theorem wp_drop_arguments_narrow (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (scratch slice _len : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (h1 : frame.locals[1]?=some (.i32 slice))
    (h2 : frame.locals[2]?=some (.i32 scratch))
    (hm : s.modules[frame.inst]?=some mi) (hi : mi.memAddrs[0]?=some index) (he : s.mems[index]?=some memory)
    (b4 : slice.toNat+(0)+4≤memory.byteSize)
    (b6 : slice.toNat+(4)+4≤memory.byteSize)
    (hc : s.host.gas.Credits (9*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 9) limits
      ((((((stack).push (.i32 (scratch+(8)))).push (.i32 (readI32 memory (slice.toNat+(0))))).push (.i32 (readI32 memory (slice.toNat+(4))))).push (.i32 (8))).push (.i32 (1052256))) frame callers code)) rest post) :
    WP cfg (fuel+9) (.next (atCode s limits stack frame callers (dropCodeNarrow++code)))
      (9*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  have mm4 : (paid s op 4).modules[frame.inst]?=some mi := by rw [modules_paid];exact hm
  have me4 : (paid s op 4).mems[index]?=some memory := by rw [mems_paid];exact he
  have mm6 : (paid s op 6).modules[frame.inst]?=some mi := by rw [modules_paid];exact hm
  have me6 : (paid s op 6).mems[index]?=some memory := by rw [mems_paid];exact he
  have p8 := wp_i32_const cfg fuel (rest) (paid s op 8) limits (((((stack).push (.i32 (scratch+(8)))).push (.i32 (readI32 memory (slice.toNat+(0))))).push (.i32 (readI32 memory (slice.toNat+(4))))).push (.i32 (8))) frame callers code (1052256) post  (paid_credits s op 8 _ (hc.mono (by dsimp [op];omega))) hnext
  have p7 := wp_i32_const cfg (fuel+1) (op+(rest)) (paid s op 7) limits ((((stack).push (.i32 (scratch+(8)))).push (.i32 (readI32 memory (slice.toNat+(0))))).push (.i32 (readI32 memory (slice.toNat+(4))))) frame callers (.i32_const (1052256)::code) (8) post  (paid_credits s op 7 _ (hc.mono (by dsimp [op];omega))) p8
  have p6 := wp_i32_load cfg (fuel+2) (op+(op+(rest))) (paid s op 6) limits (((stack).push (.i32 (scratch+(8)))).push (.i32 (readI32 memory (slice.toNat+(0))))) frame callers (.i32_const (8)::.i32_const (1052256)::code) {align:=2,offset:=4} slice mi index memory post mm6 hi me6 b6 (paid_credits s op 6 _ (hc.mono (by dsimp [op];omega))) p7
  have p5 := wp_local_get cfg (fuel+3) (op+(op+(op+(rest)))) (paid s op 5) limits (((stack).push (.i32 (scratch+(8)))).push (.i32 (readI32 memory (slice.toNat+(0))))) frame callers (.load .i32 none {align:=2,offset:=4}::.i32_const (8)::.i32_const (1052256)::code) 1 (.i32 slice) post h1 (paid_credits s op 5 _ (hc.mono (by dsimp [op];omega))) p6
  have p4 := wp_i32_load cfg (fuel+4) (op+(op+(op+(op+(rest))))) (paid s op 4) limits ((stack).push (.i32 (scratch+(8)))) frame callers (.local_get 1::.load .i32 none {align:=2,offset:=4}::.i32_const (8)::.i32_const (1052256)::code) {align:=2,offset:=0} slice mi index memory post mm4 hi me4 b4 (paid_credits s op 4 _ (hc.mono (by dsimp [op];omega))) p5
  have p3 := wp_local_get cfg (fuel+5) (op+(op+(op+(op+(op+(rest)))))) (paid s op 3) limits ((stack).push (.i32 (scratch+(8)))) frame callers (.load .i32 none {align:=2,offset:=0}::.local_get 1::.load .i32 none {align:=2,offset:=4}::.i32_const (8)::.i32_const (1052256)::code) 1 (.i32 slice) post h1 (paid_credits s op 3 _ (hc.mono (by dsimp [op];omega))) p4
  have p2 := wp_i32_add cfg (fuel+6) (op+(op+(op+(op+(op+(op+(rest))))))) (paid s op 2) limits (stack) frame callers (.local_get 1::.load .i32 none {align:=2,offset:=0}::.local_get 1::.load .i32 none {align:=2,offset:=4}::.i32_const (8)::.i32_const (1052256)::code) scratch (8) post  (paid_credits s op 2 _ (hc.mono (by dsimp [op];omega))) p3
  have p1 := wp_i32_const cfg (fuel+7) (op+(op+(op+(op+(op+(op+(op+(rest)))))))) (paid s op 1) limits ((stack).push (.i32 (scratch))) frame callers (.i32_binop .add::.local_get 1::.load .i32 none {align:=2,offset:=0}::.local_get 1::.load .i32 none {align:=2,offset:=4}::.i32_const (8)::.i32_const (1052256)::code) (8) post  (paid_credits s op 1 _ (hc.mono (by dsimp [op];omega))) p2
  have p0 := wp_local_get cfg (fuel+8) (op+(op+(op+(op+(op+(op+(op+(op+(rest))))))))) s limits (stack) frame callers (.i32_const (8)::.i32_binop .add::.local_get 1::.load .i32 none {align:=2,offset:=0}::.local_get 1::.load .i32 none {align:=2,offset:=4}::.i32_const (8)::.i32_const (1052256)::code) 2 (.i32 scratch) post h2 (hc.mono (by dsimp [op];omega)) p1
  have cost : cfg.regularOpCost+(op+(op+(op+(op+(op+(op+(op+(op+(rest)))))))))=9*cfg.regularOpCost+rest := by dsimp [op];omega
  simpa only [dropCodeNarrow,List.cons_append,List.nil_append,cost] using p0

theorem take_code_eq (wide : Bool) : WNear.Binary.StateDecodeScalar.takeArguments wide=takeCode wide++[.call 362] := rfl
theorem word_code_eq (wide : Bool) : WNear.Binary.StateDecodeScalar.wordArguments wide=wordCode wide++[.call (if wide then 694 else 710)] := rfl
theorem drop_code_eq (wide : Bool) : WNear.Binary.StateDecodeScalar.dropArguments wide=
    (if wide then dropCodeWide else dropCodeNarrow)++[.call 361] := by cases wide <;> rfl
end WNear.Proofs.StateDecodeScalar
