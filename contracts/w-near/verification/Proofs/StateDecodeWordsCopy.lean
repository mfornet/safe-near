import Proofs.StateDecodeWordsState
import NearVM.MeteredControlRules

/-! Both actual accepted copy variants and their actual length guard. -/
namespace WNear.Proofs.StateDecodeWords
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode readI64 writeI64 lowStore highStore

private theorem mems_paid (s : Store NearState) (op n : Nat) : (paid s op n).mems=s.mems := by
  induction n with |zero=>rfl |succ n ih=>exact ih
private theorem modules_paid (s : Store NearState) (op n : Nat) : (paid s op n).modules=s.modules := by
  induction n with |zero=>rfl |succ n ih=>exact ih

theorem wp_guard (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (width : UInt32) (post : Post) (h2 : frame.locals[2]?=some (.i32 width))
    (hc : s.host.gas.Credits (4*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 4) limits stack frame callers code)) rest post) :
    WP cfg (fuel+4) (.next (atCode s limits stack frame callers (WNear.Binary.StateDecodeWords.guard width++code)))
      (4*cfg.regularOpCost+rest) post := by
  let op:=cfg.regularOpCost
  have br := wp_br_if_zero cfg fuel rest (paid s op 3) limits stack frame callers code 0 post
    (paid_credits s op 3 _ (hc.mono (by dsimp[op];omega))) hnext
  have rel := wp_i32_relop cfg (fuel+1) (op+rest) (paid s op 2) limits stack frame callers (.br_if 0::code) .ne width width post
    (paid_credits s op 2 _ (hc.mono (by dsimp[op];omega))) (by simpa [Numeric.irelop32,Numeric.bool,paid,op] using br)
  have cc := wp_i32_const cfg (fuel+2) (op+(op+rest)) (paid s op 1) limits (stack.push (.i32 width)) frame callers
    (.i32_relop .ne::.br_if 0::code) width post (paid_credits s op 1 _ (hc.mono (by dsimp[op];omega))) rel
  have gg := wp_local_get cfg (fuel+3) (op+(op+(op+rest))) s limits stack frame callers
    (.i32_const width::.i32_relop .ne::.br_if 0::code) 2 (.i32 width) post h2 (hc.mono (by dsimp[op];omega)) cc
  simpa only [WNear.Binary.StateDecodeWords.guard,List.cons_append,List.nil_append,
    show cfg.regularOpCost+(op+(op+(op+rest)))=4*cfg.regularOpCost+rest by dsimp[op];omega] using gg

theorem wp_copy (wide : Bool) (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame) (code : Expr)
    (out source : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (ho : frame.locals[0]?=some (.i32 out)) (hs : frame.locals[1]?=some (.i32 source))
    (hm : s.modules[frame.inst]?=some mi) (hi : mi.memAddrs[0]?=some index) (hmem : s.mems[index]?=some memory)
    (hwf : memory.wf) (hb : source.toNat+(if wide then 16 else 8)≤memory.byteSize) (hw : out.toNat+(if wide then 17 else 9)≤memory.byteSize)
    (ha : wide=true → (out+9).toNat=out.toNat+9) (hp : wide=true → (source+8).toNat=source.toNat+8)
    (hc : s.host.gas.Credits (copyCost wide*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (copyAfter wide s cfg.regularOpCost index memory out source)
      limits stack frame callers code)) rest post) :
    WP cfg (fuel+copyCost wide) (.next (atCode s limits stack frame callers
      (WNear.Binary.StateDecodeWords.low++(if wide then WNear.Binary.StateDecodeWords.high else [])++code)))
      (copyCost wide*cfg.regularOpCost+rest) post := by
  cases wide
  · simp only [Bool.false_eq_true,ite_false] at hb hw
    simpa only [copyCost,copyAfter,ite_false,Bool.false_eq_true,List.nil_append,List.append_nil] using
      wp_low cfg fuel rest s limits stack frame callers code out source mi index memory post ho hs hm hi hmem (by omega) (by omega) hc hnext
  · simp only [ite_true] at hb hw
    have hao := ha rfl
    have hpo := hp rfl
    let op:=cfg.regularOpCost
    let low:=lowStore s op index memory out source
    have ml : low.mems[index]?=some (lowMemory memory out source) := copyAfter_memory false s op index memory out source hmem
    have md : low.modules[frame.inst]?=some mi := by
      rw [show low.modules=s.modules from copyAfter_modules false s op index memory out source]
      exact hm
    have shape := writeI64_spec memory (out.toNat+1) (readI64 memory source.toNat) hwf (by omega)
    have size : (lowMemory memory out source).byteSize=memory.byteSize := shape.2.1
    have cr : low.host.gas.Credits (8*op+rest) := copyAfter_credits false s op index (8*op+rest) memory out source
      (hc.mono (by simp only [copyCost,ite_true];dsimp[op];omega))
    have hh : WP cfg fuel (.next (atCode (highStore low op index (lowMemory memory out source) out source)
      limits stack frame callers code)) rest post := hnext
    have high := wp_high cfg fuel rest low limits stack frame callers code out source mi index (lowMemory memory out source) post
      ho hs md hi ml (by rw [size,hao];omega) (by rw [size,hpo];omega) cr hh
    have first := wp_low cfg (fuel+8) (8*op+rest) s limits stack frame callers (WNear.Binary.StateDecodeWords.high++code)
      out source mi index memory post ho hs hm hi hmem (by omega) (by omega)
      (hc.mono (by simp only [copyCost,ite_true];dsimp[op];omega)) high
    simpa only [copyCost,ite_true,List.append_assoc,Nat.add_assoc,Nat.reduceAdd,
      show 4*cfg.regularOpCost+(8*op+rest)=12*cfg.regularOpCost+rest by dsimp[op];omega] using first
end WNear.Proofs.StateDecodeWords
