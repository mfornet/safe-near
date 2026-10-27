import Binary.AllocateArithmetic
import Proofs.AllocateArithmetic
import Proofs.ValueReturnBorrow

/-! Composition of all actual scalar fit checks in the end-split branch. -/
namespace WNear.Proofs.Allocate
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
open ValueReturnBorrow (paid_add)
set_option maxRecDepth 16384
set_option maxHeartbeats 700000
attribute [local irreducible] WP atCode

def arithmeticFrame (frame : CallFrame) (memory : Memory) (head words : UInt32) :=
  let first := frame.locals.set! 10 (.i32 (head+8+8))
  let second := first.set! 13 (.i32 (head+8+8+64))
  let third := second.set! 10 (.i32 (splitPointer memory head words))
  let fourth := third.set! 9 (.i32 (splitHeader memory head words))
  {frame with locals := fourth.set! 2 (.i32 (splitLength memory head words))}

/-- All five real overflow/fit guards, closed from an original header interval.
No execution or future-memory outcome is supplied as a premise. -/
theorem wp_split_arithmetic (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (memory : Memory) (head words : UInt32) (post : Post)
    (hbase : frame.locals[9]? = some (.i32 (head+8))) (hquantum : frame.locals[13]? = some (.i32 64))
    (hp : frame.locals[12]? = some (.i32 (splitPointer memory head words)))
    (hmask : frame.locals[6]? = some (.i32 4294967295))
    (he : frame.locals[11]? = some (.i32 (endWord memory head))) (hs : 14 ≤ frame.locals.size)
    (hn : SplitNative memory head words) (hc : s.host.gas.Credits (35*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 35) limits stack
      (arithmeticFrame frame memory head words) callers code)) rest post) :
    WP cfg (fuel+35) (.next (atCode s limits stack frame callers (WNear.Binary.Allocate.splitArithmetic++code)))
      (35*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  let f1 : CallFrame := {frame with locals:=frame.locals.set! 10 (.i32 (head+8+8))}
  let f2 : CallFrame := {f1 with locals:=f1.locals.set! 13 (.i32 (head+8+8+64))}
  let f3 : CallFrame := {f2 with locals:=f2.locals.set! 10 (.i32 (splitPointer memory head words))}
  let f4 : CallFrame := {f3 with locals:=f3.locals.set! 9 (.i32 (splitHeader memory head words))}
  have v10 : 10 < frame.locals.size := by omega
  have v13 : 13 < frame.locals.size := by omega
  have v9 : 9 < frame.locals.size := by omega
  have b1 : f1.locals[10]? = some (.i32 (head+8+8)) := by simp [f1,v10]
  have q1 : f1.locals[13]? = some (.i32 64) := by simp [f1,hquantum]
  have m2 : f2.locals[13]? = some (.i32 (head+8+8+64)) := by simp [f2,f1,v13]
  have p2 : f2.locals[12]? = some (.i32 (splitPointer memory head words)) := by simp [f2,f1,hp]
  have a2 : f2.locals[6]? = some (.i32 4294967295) := by simp [f2,f1,hmask]
  have p3 : f3.locals[10]? = some (.i32 (splitPointer memory head words)) := by simp [f3,f2,f1,v10]
  have h4 : f4.locals[9]? = some (.i32 (splitHeader memory head words)) := by simp [f4,f3,f2,f1,v9]
  have e4 : f4.locals[11]? = some (.i32 (endWord memory head)) := by simp [f4,f3,f2,f1,he]
  have c28 := paid_credits s op 28 (7*op+rest) (hc.mono (by dsimp [op]; omega))
  have lastNext : WP cfg fuel (.next (atCode (paid (paid s op 28) op 7) limits stack
      {f4 with locals:=f4.locals.set! 2 (.i32 (splitLength memory head words))} callers code)) rest post := by
    simpa only [paid_add,Nat.reduceAdd,op,f4,f3,f2,f1,arithmeticFrame] using hnext
  have last := wp_split_length cfg fuel rest (paid s op 28) limits stack f4 callers code memory head words post e4 h4 hn c28 lastNext
  have next4 : WP cfg (fuel+7) (.next (atCode (paid (paid s op 21) op 7) limits stack
      {f3 with locals:=f3.locals.set! 9 (.i32 (splitHeader memory head words))} callers (WNear.Binary.Allocate.splitLength++code)))
      (7*op+rest) post := by
    simpa only [paid_add,Nat.reduceAdd,WNear.Binary.Allocate.splitLength] using last
  have fourth := wp_split_header cfg (fuel+7) (7*op+rest) (paid s op 21) limits stack f3 callers
    (WNear.Binary.Allocate.splitLength++code) memory head words post p3 hn
    (paid_credits s op 21 _ (hc.mono (by dsimp [op]; omega))) next4
  have next3 : WP cfg (fuel+14) (.next (atCode (paid (paid s op 14) op 7) limits stack
      {f2 with locals:=f2.locals.set! 10 (.i32 (splitPointer memory head words))} callers
      (WNear.Binary.Allocate.splitHeader++WNear.Binary.Allocate.splitLength++code))) (14*op+rest) post := by
    have cost : 7*cfg.regularOpCost+(7*op+rest)=14*op+rest := by dsimp [op]; omega
    rw [cost] at fourth
    simpa only [paid_add,Nat.reduceAdd,WNear.Binary.Allocate.splitHeader,Nat.add_assoc,List.append_assoc] using fourth
  have third := wp_split_fit cfg (fuel+14) (14*op+rest) (paid s op 14) limits stack f2 callers
    (WNear.Binary.Allocate.splitHeader++WNear.Binary.Allocate.splitLength++code) memory head words post m2 p2 a2 hn
    (paid_credits s op 14 _ (hc.mono (by dsimp [op]; omega))) next3
  have next2 : WP cfg (fuel+21) (.next (atCode (paid (paid s op 7) op 7) limits stack
      {f1 with locals:=f1.locals.set! 13 (.i32 (head+8+8+64))} callers
      (WNear.Binary.Allocate.splitFit++WNear.Binary.Allocate.splitHeader++WNear.Binary.Allocate.splitLength++code))) (21*op+rest) post := by
    have cost : 7*cfg.regularOpCost+(14*op+rest)=21*op+rest := by dsimp [op]; omega
    rw [cost] at third
    simpa only [paid_add,Nat.reduceAdd,WNear.Binary.Allocate.splitFit,Nat.add_assoc,List.append_assoc] using third
  have second := wp_split_minimum cfg (fuel+21) (21*op+rest) (paid s op 7) limits stack f1 callers
    (WNear.Binary.Allocate.splitFit++WNear.Binary.Allocate.splitHeader++WNear.Binary.Allocate.splitLength++code) memory head words post b1 q1 hn
    (paid_credits s op 7 _ (hc.mono (by dsimp [op]; omega))) next2
  have next1 : WP cfg (fuel+28) (.next (atCode (paid s op 7) limits stack f1 callers
      (WNear.Binary.Allocate.splitMinimum++WNear.Binary.Allocate.splitFit++WNear.Binary.Allocate.splitHeader++WNear.Binary.Allocate.splitLength++code))) (28*op+rest) post := by
    have cost : 7*cfg.regularOpCost+(21*op+rest)=28*op+rest := by dsimp [op]; omega
    rw [cost] at second
    simpa only [paid_add,Nat.reduceAdd,WNear.Binary.Allocate.splitMinimum,Nat.add_assoc,List.append_assoc] using second
  have result := wp_split_base cfg (fuel+28) (28*op+rest) s limits stack frame callers
    (WNear.Binary.Allocate.splitMinimum++WNear.Binary.Allocate.splitFit++WNear.Binary.Allocate.splitHeader++WNear.Binary.Allocate.splitLength++code)
    memory head words post hbase hn (hc.mono (by dsimp [op]; omega)) next1
  have cost : 7*cfg.regularOpCost+(28*op+rest)=35*cfg.regularOpCost+rest := by dsimp [op]; omega
  rw [cost] at result
  simpa only [WNear.Binary.Allocate.splitArithmetic,WNear.Binary.Allocate.splitBase,Nat.add_assoc,Nat.reduceAdd,List.append_assoc] using result
end WNear.Proofs.Allocate
