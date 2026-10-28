import Proofs.AllocateVectorPhases
import NearVM.MeteredNumericRules

/-! The two real686 layout checks, under byte-level readback and a native signed bound. -/
namespace WNear.Proofs.AllocateVector
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode readI32

theorem wp_alignment_guard (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (scratch : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (h3 : frame.locals[3]?=some (.i32 scratch)) (hm : s.modules[frame.inst]?=some mi)
    (hi : mi.memAddrs[0]?=some index) (hmem : s.mems[index]?=some memory)
    (hb : scratch.toNat+28+4≤memory.byteSize) (ha : readI32 memory (scratch.toNat+28)=1)
    (hc : s.host.gas.Credits (5*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 5) limits stack
      (loadedFrame frame 1 1) callers code)) rest post) :
    WP cfg (fuel+5) (.next (atCode s limits stack frame callers
      ([.local_get 3,.load .i32 none {align:=2,offset:=28},.local_tee 1,.i32_eqz,.br_if 0]++code)))
      (5*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  let ff := loadedFrame frame 1 1
  have br := wp_br_if_zero cfg fuel rest (paid s op 4) limits stack ff callers code 0 post
    (paid_credits s op 4 _ (hc.mono (by dsimp [op];omega))) hnext
  have eq := wp_i32_eqz cfg (fuel+1) (op+rest) (paid s op 3) limits stack ff callers (.br_if 0::code) 1 post
    (paid_credits s op 3 _ (hc.mono (by dsimp [op];omega))) br
  have te := wp_local_tee cfg (fuel+2) (op+(op+rest)) (paid s op 2) limits stack frame callers
    (.i32_eqz::.br_if 0::code) 1 (.i32 1) post (paid_credits s op 2 _ (hc.mono (by dsimp [op];omega))) eq
  have mm : (paid s op 1).modules[frame.inst]?=some mi := hm
  have me : (paid s op 1).mems[index]?=some memory := hmem
  have tn : WP cfg (fuel+3) (.next (atCode (paid s op 2) limits
      (stack.push (.i32 (readI32 memory (scratch.toNat+28)))) frame callers
      (.local_tee 1::.i32_eqz::.br_if 0::code))) (op+(op+(op+rest))) post := by rw [ha];exact te
  have ld := wp_i32_load cfg (fuel+3) (op+(op+(op+rest))) (paid s op 1) limits stack frame callers
    (.local_tee 1::.i32_eqz::.br_if 0::code) {align:=2,offset:=28} scratch mi index memory post mm hi me hb
    (paid_credits s op 1 _ (hc.mono (by dsimp [op];omega))) tn
  have g := wp_local_get cfg (fuel+4) (op+(op+(op+(op+rest)))) s limits stack frame callers
    (.load .i32 none {align:=2,offset:=28}::.local_tee 1::.i32_eqz::.br_if 0::code) 3 (.i32 scratch) post h3
    (hc.mono (by dsimp [op];omega)) ld
  simpa only [List.cons_append,List.nil_append,
    show cfg.regularOpCost+(op+(op+(op+(op+rest))))=5*cfg.regularOpCost+rest by dsimp [op];omega] using g

theorem wp_size_guard (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (scratch size : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (h3 : frame.locals[3]?=some (.i32 scratch)) (hm : s.modules[frame.inst]?=some mi)
    (hi : mi.memAddrs[0]?=some index) (hmem : s.mems[index]?=some memory)
    (hb : scratch.toNat+24+4≤memory.byteSize) (ha : readI32 memory (scratch.toNat+24)=size)
    (hn : size.toNat<2^31)
    (hc : s.host.gas.Credits (6*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 6) limits stack
      (loadedFrame frame 4 size) callers code)) rest post) :
    WP cfg (fuel+6) (.next (atCode s limits stack frame callers
      ([.local_get 3,.load .i32 none {align:=2,offset:=24},.local_tee 4,
        .i32_const 4294967295,.i32_relop .le_s,.br_if 0]++code))) (6*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  let ff := loadedFrame frame 4 size
  have cmp : Numeric.irelop32 .le_s size 4294967295=false := by
    have bound : size.toNat<2147483648 := hn
    simp [Numeric.irelop32,UInt32.toIntS,bound]
    omega
  have br := wp_br_if_zero cfg fuel rest (paid s op 5) limits stack ff callers code 0 post
    (paid_credits s op 5 _ (hc.mono (by dsimp [op];omega))) hnext
  have rn : WP cfg (fuel+1) (.next (atCode (paid s op 5) limits
      (stack.push (.i32 (Numeric.bool (Numeric.irelop32 .le_s size 4294967295)))) ff callers (.br_if 0::code))) (op+rest) post := by
    simpa only [cmp,Numeric.bool,Bool.false_eq_true,ite_false] using br
  have rel := wp_i32_relop cfg (fuel+1) (op+rest) (paid s op 4) limits stack ff callers (.br_if 0::code)
    .le_s size 4294967295 post (paid_credits s op 4 _ (hc.mono (by dsimp [op];omega))) rn
  have con := wp_i32_const cfg (fuel+2) (op+(op+rest)) (paid s op 3) limits (stack.push (.i32 size)) ff callers
    (.i32_relop .le_s::.br_if 0::code) 4294967295 post (paid_credits s op 3 _ (hc.mono (by dsimp [op];omega))) rel
  have te := wp_local_tee cfg (fuel+3) (op+(op+(op+rest))) (paid s op 2) limits stack frame callers
    (.i32_const 4294967295::.i32_relop .le_s::.br_if 0::code) 4 (.i32 size) post
    (paid_credits s op 2 _ (hc.mono (by dsimp [op];omega))) con
  have mm : (paid s op 1).modules[frame.inst]?=some mi := hm
  have me : (paid s op 1).mems[index]?=some memory := hmem
  have tn : WP cfg (fuel+4) (.next (atCode (paid s op 2) limits
      (stack.push (.i32 (readI32 memory (scratch.toNat+24)))) frame callers
      (.local_tee 4::.i32_const 4294967295::.i32_relop .le_s::.br_if 0::code))) (op+(op+(op+(op+rest)))) post := by rw [ha];exact te
  have ld := wp_i32_load cfg (fuel+4) (op+(op+(op+(op+rest)))) (paid s op 1) limits stack frame callers
    (.local_tee 4::.i32_const 4294967295::.i32_relop .le_s::.br_if 0::code) {align:=2,offset:=24} scratch mi index memory post mm hi me hb
    (paid_credits s op 1 _ (hc.mono (by dsimp [op];omega))) tn
  have g := wp_local_get cfg (fuel+5) (op+(op+(op+(op+(op+rest))))) s limits stack frame callers
    (.load .i32 none {align:=2,offset:=24}::.local_tee 4::.i32_const 4294967295::.i32_relop .le_s::.br_if 0::code)
    3 (.i32 scratch) post h3 (hc.mono (by dsimp [op];omega)) ld
  simpa only [List.cons_append,List.nil_append,
    show cfg.regularOpCost+(op+(op+(op+(op+(op+rest)))))=6*cfg.regularOpCost+rest by dsimp [op];omega] using g
end WNear.Proofs.AllocateVector
