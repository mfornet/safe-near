import Binary.StateDecodeScalar
import Proofs.StorePairCallerState
import Proofs.ValueReturnBorrow
import NearVM.MeteredScalarRules
import NearVM.MeteredMemoryRules

/-! Scalar decoder snapshots are cached before any caller-visible output write. -/
namespace WNear.Proofs.StateDecodeScalar
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode readI64

private theorem paid_modules (s : Store NearState) (op n : Nat) : (paid s op n).modules=s.modules := by
  induction n with |zero=>rfl |succ n ih=>exact ih
private theorem paid_mems (s : Store NearState) (op n : Nat) : (paid s op n).mems=s.mems := by
  induction n with |zero=>rfl |succ n ih=>exact ih

def loaded64Frame (frame : CallFrame) (target : Nat) (value : UInt64) :=
  {frame with locals:=frame.locals.set! target (.i64 value)}

theorem wp_load64_set (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (arg : MemArg) (pointer : UInt32) (target : Nat)
    (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (hm : s.modules[frame.inst]?=some mi) (hi : mi.memAddrs[0]?=some index)
    (hmem : s.mems[index]?=some memory) (hb : pointer.toNat+arg.offset+8≤memory.byteSize)
    (hc : s.host.gas.Credits (2*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 2) limits stack
      (loaded64Frame frame target (readI64 memory (pointer.toNat+arg.offset))) callers code)) rest post) :
    WP cfg (fuel+2) (.next (atCode s limits (stack.push (.i32 pointer)) frame callers
      (.load .i64 none arg::.local_set target::code))) (2*cfg.regularOpCost+rest) post := by
  let op:=cfg.regularOpCost
  have set := wp_local_set cfg fuel rest (paid s op 1) limits stack frame callers code target
    (.i64 (readI64 memory (pointer.toNat+arg.offset))) post
    (paid_credits s op 1 _ (hc.mono (by dsimp[op];omega))) hnext
  have load := wp_i64_load cfg (fuel+1) (op+rest) s limits stack frame callers (.local_set target::code)
    arg pointer mi index memory post hm hi hmem hb (hc.mono (by dsimp[op];omega)) set
  simpa only [show cfg.regularOpCost+(op+rest)=2*cfg.regularOpCost+rest by dsimp[op];omega] using load

theorem wp_load64_local (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (source target : Nat) (arg : MemArg) (pointer : UInt32)
    (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (hl : frame.locals[source]?=some (.i32 pointer)) (hm : s.modules[frame.inst]?=some mi)
    (hi : mi.memAddrs[0]?=some index) (hmem : s.mems[index]?=some memory)
    (hb : pointer.toNat+arg.offset+8≤memory.byteSize)
    (hc : s.host.gas.Credits (3*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 3) limits stack
      (loaded64Frame frame target (readI64 memory (pointer.toNat+arg.offset))) callers code)) rest post) :
    WP cfg (fuel+3) (.next (atCode s limits stack frame callers
      (.local_get source::.load .i64 none arg::.local_set target::code))) (3*cfg.regularOpCost+rest) post := by
  let op:=cfg.regularOpCost
  have load := wp_load64_set cfg fuel rest (paid s op 1) limits stack frame callers code arg pointer target
    mi index memory post hm hi hmem hb (paid_credits s op 1 _ (hc.mono (by dsimp[op];omega)))
    (by simpa only [paid,op] using hnext)
  have get := wp_local_get cfg (fuel+2) (2*op+rest) s limits stack frame callers
    (.load .i64 none arg::.local_set target::code) source (.i32 pointer) post hl
    (hc.mono (by dsimp[op];omega)) load
  simpa only [Nat.add_assoc,Nat.reduceAdd,
    show cfg.regularOpCost+(2*op+rest)=3*cfg.regularOpCost+rest by dsimp[op];omega] using get

theorem wp_added_load64_local (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (source target : Nat) (arg : MemArg) (pointer delta : UInt32)
    (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (hl : frame.locals[source]?=some (.i32 pointer)) (hm : s.modules[frame.inst]?=some mi)
    (hi : mi.memAddrs[0]?=some index) (hmem : s.mems[index]?=some memory)
    (hb : (pointer+delta).toNat+arg.offset+8≤memory.byteSize)
    (hc : s.host.gas.Credits (5*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 5) limits stack
      (loaded64Frame frame target (readI64 memory ((pointer+delta).toNat+arg.offset))) callers code)) rest post) :
    WP cfg (fuel+5) (.next (atCode s limits stack frame callers
      (.local_get source::.i32_const delta::.i32_binop .add::.load .i64 none arg::.local_set target::code)))
      (5*cfg.regularOpCost+rest) post := by
  let op:=cfg.regularOpCost
  have load := wp_load64_set cfg fuel rest (paid s op 3) limits stack frame callers code arg (pointer+delta) target
    mi index memory post hm hi hmem hb (paid_credits s op 3 _ (hc.mono (by dsimp[op];omega)))
    (by simpa only [paid,op] using hnext)
  have add := wp_i32_add cfg (fuel+2) (2*op+rest) (paid s op 2) limits stack frame callers
    (.load .i64 none arg::.local_set target::code) pointer delta post
    (paid_credits s op 2 _ (hc.mono (by dsimp[op];omega))) load
  have constant := wp_i32_const cfg (fuel+3) (op+(2*op+rest)) (paid s op 1) limits
    (stack.push (.i32 pointer)) frame callers (.i32_binop .add::.load .i64 none arg::.local_set target::code) delta post
    (paid_credits s op 1 _ (hc.mono (by dsimp[op];omega))) add
  have get := wp_local_get cfg (fuel+4) (op+(op+(2*op+rest))) s limits stack frame callers
    (.i32_const delta::.i32_binop .add::.load .i64 none arg::.local_set target::code) source (.i32 pointer) post hl
    (hc.mono (by dsimp[op];omega)) constant
  simpa only [Nat.add_assoc,Nat.reduceAdd,
    show cfg.regularOpCost+(op+(op+(2*op+rest)))=5*cfg.regularOpCost+rest by dsimp[op];omega] using get
def cacheFrame (wide : Bool) (frame : CallFrame) (memory : Memory) (scratch : UInt32) :=
  if wide then loaded64Frame (loaded64Frame frame 4 (readI64 memory (scratch+25).toNat)) 5 (readI64 memory (scratch.toNat+17))
  else loaded64Frame frame 4 (readI64 memory (scratch.toNat+25))
def cacheCost (wide : Bool) : Nat := if wide then 8 else 3

theorem wp_cache (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (wide : Bool) (scratch : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (h2 : frame.locals[2]?=some (.i32 scratch)) (hm : s.modules[frame.inst]?=some mi)
    (hi : mi.memAddrs[0]?=some index) (hmem : s.mems[index]?=some memory)
    (hb : scratch.toNat+33≤memory.byteSize) (ha : (scratch+25).toNat=scratch.toNat+25)
    (hc : s.host.gas.Credits (cacheCost wide*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost (cacheCost wide)) limits stack
      (cacheFrame wide frame memory scratch) callers code)) rest post) :
    WP cfg (fuel+cacheCost wide) (.next (atCode s limits stack frame callers
      (WNear.Binary.StateDecodeScalar.cache wide++code))) (cacheCost wide*cfg.regularOpCost+rest) post := by
  cases wide with
  | false=>
    simp only [cacheCost,Bool.false_eq_true,ite_false] at hc hnext ⊢
    have step := wp_load64_local cfg fuel rest s limits stack frame callers code 2 4 {align:=0,offset:=25}
      scratch mi index memory post h2 hm hi hmem (by omega) hc hnext
    simpa only [cacheCost,WNear.Binary.StateDecodeScalar.cache,Bool.false_eq_true,ite_false,List.cons_append,List.nil_append] using step
  | true=>
    simp only [cacheCost,ite_true] at hc hnext ⊢
    let op:=cfg.regularOpCost
    let ff:=loaded64Frame frame 4 (readI64 memory (scratch+25).toNat)
    have h2f : ff.locals[2]?=some (.i32 scratch) := by simp [ff,loaded64Frame,h2]
    have mm : (paid s op 5).modules[ff.inst]?=some mi := by
      rw [paid_modules]
      simpa only [ff,loaded64Frame] using hm
    have me : (paid s op 5).mems[index]?=some memory := by
      rw [paid_mems]
      exact hmem
    have low := wp_load64_local cfg fuel rest (paid s op 5) limits stack ff callers code 2 5 {align:=0,offset:=17}
      scratch mi index memory post h2f mm hi me (by change scratch.toNat+17+8≤memory.byteSize;omega)
      (paid_credits s op 5 _ (hc.mono (by dsimp[op];omega)))
      (by simpa only [cacheFrame,cacheCost,ite_true,ff,paid,op] using hnext)
    have highNext : WP cfg (fuel+3) (.next (atCode (paid s op 5) limits stack ff callers
      ([.local_get 2,.load .i64 none {align:=0,offset:=17},.local_set 5]++code))) (3*op+rest) post := by
      simpa only [List.cons_append,List.nil_append] using low
    have high := wp_added_load64_local cfg (fuel+3) (3*op+rest) s limits stack frame callers
      ([.local_get 2,.load .i64 none {align:=0,offset:=17},.local_set 5]++code) 2 4 {align:=0,offset:=0}
      scratch 25 mi index memory post h2 hm hi hmem (by rw [ha];omega)
      (hc.mono (by dsimp[op];omega)) highNext
    simpa only [WNear.Binary.StateDecodeScalar.cache,cacheCost,ite_true,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd,
      show 5*cfg.regularOpCost+(3*op+rest)=8*cfg.regularOpCost+rest by dsimp[op];omega] using high
end WNear.Proofs.StateDecodeScalar
