import Binary.StateDecodeWords
import Proofs.StorePairCallerState
import Proofs.ValueReturnBorrow
import NearVM.MeteredScalarRules
import NearVM.MeteredByteMemoryRules
import NearVM.MeteredLoopRules
import NearVM.MeteredNumericRules

/-! Fixed-width decoder scalar and sequential memory capsules. -/
namespace WNear.Proofs.StateDecodeWords
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode readI64 writeI64

def flagFrame (frame : CallFrame) (value : UInt32) := {frame with locals:=frame.locals.set! 3 (.i32 value)}
def lowMemory (memory : Memory) (out source : UInt32) := writeI64 memory (out.toNat+1) (readI64 memory source.toNat)
def lowStore (s : Store NearState) (op index : Nat) (memory : Memory) (out source : UInt32) :=
  storeI64 (paid s op 4) index (out.toNat+1) memory (readI64 memory source.toNat)
def statusStore (s : Store NearState) (op index : Nat) (memory : Memory) (out : UInt32) :=
  storeByte (paid s op 3) index out.toNat memory 0

theorem wp_set_flag (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame) (code : Expr)
    (value : UInt32) (post : Post) (hc : s.host.gas.Credits (2*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 2) limits stack (flagFrame frame value) callers code)) rest post) :
    WP cfg (fuel+2) (.next (atCode s limits stack frame callers (WNear.Binary.StateDecodeWords.setFlag value++code)))
      (2*cfg.regularOpCost+rest) post := by
  let op:=cfg.regularOpCost
  have sc := wp_local_set cfg fuel rest (paid s op 1) limits stack frame callers code 3 (.i32 value) post
    (paid_credits s op 1 _ (hc.mono (by dsimp[op];omega))) hnext
  have cc := wp_i32_const cfg (fuel+1) (op+rest) s limits stack frame callers (.local_set 3::code) value post
    (hc.mono (by dsimp[op];omega)) sc
  simpa only [WNear.Binary.StateDecodeWords.setFlag,List.cons_append,List.nil_append,
    show cfg.regularOpCost+(op+rest)=2*cfg.regularOpCost+rest by dsimp[op];omega] using cc

theorem wp_low (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame) (code : Expr)
    (out source : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (ho : frame.locals[0]?=some (.i32 out)) (hs : frame.locals[1]?=some (.i32 source))
    (hm : s.modules[frame.inst]?=some mi) (hi : mi.memAddrs[0]?=some index) (hmem : s.mems[index]?=some memory)
    (hb : source.toNat+8≤memory.byteSize) (hw : out.toNat+1+8≤memory.byteSize)
    (hc : s.host.gas.Credits (4*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (lowStore s cfg.regularOpCost index memory out source) limits stack frame callers code)) rest post) :
    WP cfg (fuel+4) (.next (atCode s limits stack frame callers (WNear.Binary.StateDecodeWords.low++code)))
      (4*cfg.regularOpCost+rest) post := by
  let op:=cfg.regularOpCost
  have md : (paid s op 3).modules[frame.inst]?=some mi := hm
  have mm : (paid s op 3).mems[index]?=some memory := hmem
  have st := wp_i64_store cfg fuel rest (paid s op 3) limits stack frame callers code {align:=0,offset:=1}
    out (readI64 memory source.toNat) mi index memory post md hi mm hw
    (paid_credits s op 3 _ (hc.mono (by dsimp[op];omega))) hnext
  have ld := wp_i64_load cfg (fuel+1) (op+rest) (paid s op 2) limits (stack.push (.i32 out)) frame callers
    (.store .i64 none {align:=0,offset:=1}::code) {align:=0,offset:=0} source mi index memory post hm hi hmem hb
    (paid_credits s op 2 _ (hc.mono (by dsimp[op];omega))) st
  have g1 := wp_local_get cfg (fuel+2) (op+(op+rest)) (paid s op 1) limits (stack.push (.i32 out)) frame callers
    (.load .i64 none {align:=0,offset:=0}::.store .i64 none {align:=0,offset:=1}::code) 1 (.i32 source) post hs
    (paid_credits s op 1 _ (hc.mono (by dsimp[op];omega))) ld
  have g0 := wp_local_get cfg (fuel+3) (op+(op+(op+rest))) s limits stack frame callers
    (.local_get 1::.load .i64 none {align:=0,offset:=0}::.store .i64 none {align:=0,offset:=1}::code) 0 (.i32 out) post ho
    (hc.mono (by dsimp[op];omega)) g1
  simpa only [WNear.Binary.StateDecodeWords.low,List.cons_append,List.nil_append,
    show cfg.regularOpCost+(op+(op+(op+rest)))=4*cfg.regularOpCost+rest by dsimp[op];omega] using g0

theorem wp_status (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame) (code : Expr)
    (out : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (ho : frame.locals[0]?=some (.i32 out)) (hz : frame.locals[3]?=some (.i32 0))
    (hm : s.modules[frame.inst]?=some mi) (hi : mi.memAddrs[0]?=some index) (hmem : s.mems[index]?=some memory)
    (hb : out.toNat+1≤memory.byteSize) (hc : s.host.gas.Credits (3*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (statusStore s cfg.regularOpCost index memory out) limits stack frame callers code)) rest post) :
    WP cfg (fuel+3) (.next (atCode s limits stack frame callers (WNear.Binary.StateDecodeWords.status++code)))
      (3*cfg.regularOpCost+rest) post := by
  let op:=cfg.regularOpCost
  have st := wp_i32_store8 cfg fuel rest (paid s op 2) limits stack frame callers code {align:=0,offset:=0}
    out 0 mi index memory post hm hi hmem hb
    (paid_credits s op 2 _ (hc.mono (by dsimp[op];omega))) hnext
  have g3 := wp_local_get cfg (fuel+1) (op+rest) (paid s op 1) limits (stack.push (.i32 out)) frame callers
    (.store .i32 (some 8) {align:=0,offset:=0}::code) 3 (.i32 0) post hz
    (paid_credits s op 1 _ (hc.mono (by dsimp[op];omega))) st
  have g0 := wp_local_get cfg (fuel+2) (op+(op+rest)) s limits stack frame callers
    (.local_get 3::.store .i32 (some 8) {align:=0,offset:=0}::code) 0 (.i32 out) post ho
    (hc.mono (by dsimp[op];omega)) g3
  simpa only [WNear.Binary.StateDecodeWords.status,List.cons_append,List.nil_append,
    show cfg.regularOpCost+(op+(op+rest))=3*cfg.regularOpCost+rest by dsimp[op];omega] using g0
def highStore (s : Store NearState) (op index : Nat) (memory : Memory) (out source : UInt32) :=
  storeI64 (paid s op 8) index (out+9).toNat memory (readI64 memory (source+8).toNat)

theorem wp_high_addresses (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (out source : UInt32) (post : Post)
    (ho : frame.locals[0]? = some (.i32 out)) (hs : frame.locals[1]? = some (.i32 source))
    (hc : s.host.gas.Credits (6 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 6) limits
      ((stack.push (.i32 (out + 9))).push (.i32 (source + 8))) frame callers code)) rest post) :
    WP cfg (fuel + 6) (.next (atCode s limits stack frame callers
      ([.local_get 0,.i32_const 9,.i32_binop .add,.local_get 1,.i32_const 8,.i32_binop .add] ++ code)))
      (6 * cfg.regularOpCost + rest) post := by
  rw [show 6 * cfg.regularOpCost + rest = cfg.regularOpCost + (5 * cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 5) _ s limits stack frame callers _ 0 (.i32 out) post ho (hc.mono (by omega))
  rw [show 5 * cfg.regularOpCost + rest = cfg.regularOpCost + (4 * cfg.regularOpCost + rest) by omega]
  apply wp_i32_const cfg (fuel + 4) _ (paid s cfg.regularOpCost 1) limits _ frame callers _ 9 post
  · exact paid_credits s cfg.regularOpCost 1 _ (hc.mono (by omega))
  rw [show 4 * cfg.regularOpCost + rest = cfg.regularOpCost + (3 * cfg.regularOpCost + rest) by omega]
  apply wp_i32_add cfg (fuel + 3) _ (paid s cfg.regularOpCost 2) limits stack frame callers _ out 9 post
  · exact paid_credits s cfg.regularOpCost 2 _ (hc.mono (by omega))
  rw [show 3 * cfg.regularOpCost + rest = cfg.regularOpCost + (2 * cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 2) _ (paid s cfg.regularOpCost 3) limits _ frame callers _ 1 (.i32 source) post hs
  · exact paid_credits s cfg.regularOpCost 3 _ (hc.mono (by omega))
  rw [show 2 * cfg.regularOpCost + rest = cfg.regularOpCost + (cfg.regularOpCost + rest) by omega]
  apply wp_i32_const cfg (fuel + 1) _ (paid s cfg.regularOpCost 4) limits _ frame callers _ 8 post
  · exact paid_credits s cfg.regularOpCost 4 _ (hc.mono (by omega))
  have r := wp_i32_add cfg fuel rest (paid s cfg.regularOpCost 5) limits (stack.push (.i32 (out + 9))) frame callers code source 8 post
    (paid_credits s cfg.regularOpCost 5 _ (hc.mono (by omega))) hnext
  simpa only [paid,List.append_eq,List.cons_append,List.nil_append] using r

def copy64Store (s : Store NearState) (op index : Nat) (memory : Memory) (out source : UInt32) :=
  storeI64 (paid s op 2) index out.toNat memory (readI64 memory source.toNat)

/-- The last read observes the memory after the preceding i64 write. -/
theorem wp_copy64 (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (out source : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.memAddrs[0]? = some index) (hmem : s.mems[index]? = some memory)
    (hob : out.toNat + 8 ≤ memory.byteSize) (hsb : source.toNat + 8 ≤ memory.byteSize)
    (hc : s.host.gas.Credits (2 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (copy64Store s cfg.regularOpCost index memory out source) limits stack frame callers code)) rest post) :
    WP cfg (fuel + 2) (.next (atCode s limits ((stack.push (.i32 out)).push (.i32 source)) frame callers
      ([.load .i64 none {align := 0,offset := 0},.store .i64 none {align := 0,offset := 0}] ++ code)))
      (2 * cfg.regularOpCost + rest) post := by
  rw [show 2 * cfg.regularOpCost + rest = cfg.regularOpCost + (cfg.regularOpCost + rest) by omega]
  apply wp_i64_load cfg (fuel + 1) _ s limits (stack.push (.i32 out)) frame callers _
    {align := 0,offset := 0} source mi index memory post hm hi hmem (by simpa using hsb) (hc.mono (by omega))
  have hm1 : (paid s cfg.regularOpCost 1).modules[frame.inst]? = some mi := by simpa only [paid,chargedStore] using hm
  have m1 : (paid s cfg.regularOpCost 1).mems[index]? = some memory := by simpa only [paid,chargedStore] using hmem
  have hn : WP cfg fuel (.next (atCode (storeI64 (chargedStore (paid s cfg.regularOpCost 1) cfg.regularOpCost) index
      (out.toNat + 0) memory (readI64 memory source.toNat)) limits stack frame callers code)) rest post := by
    simpa only [copy64Store,paid,Nat.add_zero] using hnext
  have r := wp_i64_store cfg fuel rest (paid s cfg.regularOpCost 1) limits stack frame callers code
    {align := 0,offset := 0} out (readI64 memory source.toNat) mi index memory post hm1 hi m1 (by simpa using hob)
    (paid_credits s cfg.regularOpCost 1 _ (hc.mono (by omega))) hn
  simpa only [paid,Nat.add_zero,List.append_eq,List.cons_append,List.nil_append] using r

/-- All eight actual high-word instructions, with no non-aliasing premise. -/
theorem wp_high (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (out source : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (ho : frame.locals[0]? = some (.i32 out)) (hs : frame.locals[1]? = some (.i32 source))
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.memAddrs[0]? = some index) (hmem : s.mems[index]? = some memory)
    (hob : (out + 9).toNat + 8 ≤ memory.byteSize) (hsb : (source + 8).toNat + 8 ≤ memory.byteSize)
    (hc : s.host.gas.Credits (8 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (highStore s cfg.regularOpCost index memory out source) limits stack frame callers code)) rest post) :
    WP cfg (fuel + 8) (.next (atCode s limits stack frame callers (WNear.Binary.StateDecodeWords.high ++ code)))
      (8 * cfg.regularOpCost + rest) post := by
  have hm6 : (paid s cfg.regularOpCost 6).modules[frame.inst]? = some mi := by simpa only [paid,chargedStore] using hm
  have m6 : (paid s cfg.regularOpCost 6).mems[index]? = some memory := by simpa only [paid,chargedStore] using hmem
  have hn : WP cfg fuel (.next (atCode (copy64Store (paid s cfg.regularOpCost 6) cfg.regularOpCost index memory (out + 9) (source + 8))
      limits stack frame callers code)) rest post := by
    simpa only [copy64Store,highStore,ValueReturnBorrow.paid_add] using hnext
  have tail := wp_copy64 cfg fuel rest (paid s cfg.regularOpCost 6) limits stack frame callers code (out + 9) (source + 8) mi index memory post hm6 hi m6 hob hsb
    (paid_credits s cfg.regularOpCost 6 _ (hc.mono (by omega))) hn
  have r := wp_high_addresses cfg (fuel + 2) (2 * cfg.regularOpCost + rest) s limits stack frame callers _ out source post ho hs (hc.mono (by omega)) tail
  simpa only [WNear.Binary.StateDecodeWords.high,List.append_eq,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd,
    show 6 * cfg.regularOpCost + (2 * cfg.regularOpCost + rest) = 8 * cfg.regularOpCost + rest by omega] using r

end WNear.Proofs.StateDecodeWords
