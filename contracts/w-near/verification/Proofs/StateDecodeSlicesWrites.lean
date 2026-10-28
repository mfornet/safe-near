import Proofs.StateDecodeSlicesStores

/-! Actual slice output stores preserve their sequential high-then-low memory. -/
namespace WNear.Proofs.StateDecodeSlices
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode

def wordCount (drop : Bool) : Nat := if drop then 5 else 3
def highWord (drop : Bool) (len split : UInt32) := if drop then len-split else split
def lowWord (drop : Bool) (pointer split : UInt32) := if drop then pointer+split else pointer
def firstMemory (drop : Bool) (memory : Memory) (out len split : UInt32) :=
  writeI32 memory (out.toNat+4) (highWord drop len split)
def finalMemory (drop : Bool) (memory : Memory) (out pointer len split : UInt32) :=
  writeI32 (firstMemory drop memory out len split) out.toNat (lowWord drop pointer split)
def highStore (drop : Bool) (s : Store NearState) (op index : Nat) (memory : Memory) (out len split : UInt32) :=
  storeI32 (paid s op (wordCount drop)) index (out.toNat+4) memory (highWord drop len split)
def writesAfter (drop : Bool) (s : Store NearState) (op index : Nat) (memory : Memory) (out pointer len split : UInt32) :=
  storeI32 (paid (highStore drop s op index memory out len split) op (wordCount drop)) index out.toNat
    (firstMemory drop memory out len split) (lowWord drop pointer split)

private theorem modules_paid (s : Store NearState) (op n : Nat) : (paid s op n).modules=s.modules := by
  induction n with |zero=>rfl |succ n ih=>exact ih
private theorem mems_paid (s : Store NearState) (op n : Nat) : (paid s op n).mems=s.mems := by
  induction n with |zero=>rfl |succ n ih=>exact ih

theorem wp_writes (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (drop : Bool) (out pointer len split : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (h0 : frame.locals[0]?=some (.i32 out)) (h1 : frame.locals[1]?=some (.i32 pointer))
    (h2 : frame.locals[2]?=some (.i32 len)) (h3 : frame.locals[3]?=some (.i32 split))
    (hm : s.modules[frame.inst]?=some mi) (hi : mi.memAddrs[0]?=some index) (he : s.mems[index]?=some memory)
    (hwf : memory.wf) (hb : out.toNat+8≤memory.byteSize)
    (hc : s.host.gas.Credits ((2*wordCount drop)*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (writesAfter drop s cfg.regularOpCost index memory out pointer len split)
      limits stack frame callers code)) rest post) :
    WP cfg (fuel+2*wordCount drop) (.next (atCode s limits stack frame callers
      ((if drop then WNear.Binary.StateDecodeSlices.dropWrites else WNear.Binary.StateDecodeSlices.takeWrites)++code)))
      ((2*wordCount drop)*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  cases drop with
  | false =>
    let one := highStore false s op index memory out len split
    have spec := writeI32_spec memory (out.toNat+4) split hwf (by omega)
    have mm : one.modules[frame.inst]?=some mi := by
      simp only [one,highStore,storeI32_modules,modules_paid];exact hm
    have me : one.mems[index]?=some (firstMemory false memory out len split) := by
      have mp : (paid s op 3).mems[index]?=some memory := by rw [mems_paid];exact he
      simpa only [one,highStore,wordCount,firstMemory,highWord,ite_true,Bool.false_eq_true,ite_false] using
        storeI32_memory (paid s op 3) index (out.toNat+4) memory split mp
    have co : one.host.gas.Credits (3*op+rest) := by
      simpa only [one,highStore,wordCount,storeI32_host,ite_true,Bool.false_eq_true,ite_false] using
        paid_credits s op 3 (3*op+rest) (hc.mono (by simp only [wordCount,Bool.false_eq_true,ite_false,Nat.reduceMul,op];omega))
    have bound : out.toNat+0+4≤(firstMemory false memory out len split).byteSize := by
      simpa only [firstMemory,highWord,ite_true,Bool.false_eq_true,ite_false,spec.2.1] using (show out.toNat+0+4≤memory.byteSize by omega)
    have ln : WP cfg fuel (.next (atCode (wordStore one op index (firstMemory false memory out len split) out pointer 0) limits stack frame callers code)) rest post := by
      simpa only [writesAfter,one,wordStore,wordCount,lowWord,Bool.false_eq_true,ite_false,Nat.add_zero,op] using hnext
    have low := wp_word_store cfg fuel rest one limits stack frame callers code out pointer 1 0 mi index (firstMemory false memory out len split) post
      h0 h1 mm hi me bound co ln
    have lowN : WP cfg (fuel+3) (.next (atCode (wordStore s op index memory out split 4) limits stack frame callers
        (.local_get 0::.local_get 1::.store .i32 none {align:=2,offset:=0}::code))) (3*op+rest) post := by
      simpa only [one,highStore,wordStore,wordCount,highWord,Bool.false_eq_true,ite_false,op] using low
    have high := wp_word_store cfg (fuel+3) (3*op+rest) s limits stack frame callers
      (.local_get 0::.local_get 1::.store .i32 none {align:=2,offset:=0}::code) out split 3 4 mi index memory post
      h0 h3 hm hi he (by omega) (hc.mono (by simp only [wordCount,Bool.false_eq_true,ite_false,op];omega)) lowN
    simpa only [WNear.Binary.StateDecodeSlices.takeWrites,wordCount,ite_true,Bool.false_eq_true,ite_false,
      List.cons_append,List.nil_append,Nat.reduceMul,Nat.add_assoc,Nat.reduceAdd,
      show 3*cfg.regularOpCost+(3*op+rest)=6*cfg.regularOpCost+rest by dsimp [op];omega] using high
  | true =>
    let one := highStore true s op index memory out len split
    have spec := writeI32_spec memory (out.toNat+4) (len-split) hwf (by omega)
    have mm : one.modules[frame.inst]?=some mi := by
      simp only [one,highStore,storeI32_modules,modules_paid];exact hm
    have me : one.mems[index]?=some (firstMemory true memory out len split) := by
      have mp : (paid s op 5).mems[index]?=some memory := by rw [mems_paid];exact he
      simpa only [one,highStore,wordCount,firstMemory,highWord,ite_true,Bool.false_eq_true,ite_false] using
        storeI32_memory (paid s op 5) index (out.toNat+4) memory (len-split) mp
    have co : one.host.gas.Credits (5*op+rest) := by
      simpa only [one,highStore,wordCount,storeI32_host,ite_true,Bool.false_eq_true,ite_false] using
        paid_credits s op 5 (5*op+rest) (hc.mono (by simp only [wordCount,ite_true,Nat.reduceMul,op];omega))
    have bound : out.toNat+0+4≤(firstMemory true memory out len split).byteSize := by
      simpa only [firstMemory,highWord,ite_true,Bool.false_eq_true,ite_false,spec.2.1] using (show out.toNat+0+4≤memory.byteSize by omega)
    have ln : WP cfg fuel (.next (atCode (binaryStore one op index (firstMemory true memory out len split) out pointer split 0 false) limits stack frame callers code)) rest post := by
      simpa only [writesAfter,one,binaryStore,binaryWord,wordCount,lowWord,ite_true,Bool.false_eq_true,ite_false,Nat.add_zero,op] using hnext
    have low := wp_binary_store cfg fuel rest one limits stack frame callers code out pointer split 1 3 0 false mi index (firstMemory true memory out len split) post
      h0 h1 h3 mm hi me bound co ln
    have lowN : WP cfg (fuel+5) (.next (atCode (binaryStore s op index memory out len split 4 true) limits stack frame callers
        (.local_get 0::.local_get 1::.local_get 3::.i32_binop .add::.store .i32 none {align:=2,offset:=0}::code))) (5*op+rest) post := by
      simpa only [one,highStore,binaryStore,binaryWord,wordCount,highWord,Bool.false_eq_true,ite_false,ite_true,op] using low
    have high := wp_binary_store cfg (fuel+5) (5*op+rest) s limits stack frame callers
      (.local_get 0::.local_get 1::.local_get 3::.i32_binop .add::.store .i32 none {align:=2,offset:=0}::code) out len split 2 3 4 true mi index memory post
      h0 h2 h3 hm hi he (by omega) (hc.mono (by simp only [wordCount,ite_true,op];omega)) lowN
    simpa only [WNear.Binary.StateDecodeSlices.dropWrites,wordCount,ite_true,Bool.false_eq_true,ite_false,
      List.cons_append,List.nil_append,Nat.reduceMul,Nat.add_assoc,Nat.reduceAdd,
      show 5*cfg.regularOpCost+(5*op+rest)=10*cfg.regularOpCost+rest by dsimp [op];omega] using high
end WNear.Proofs.StateDecodeSlices
