import Proofs.AllocateVectorOuterExit
import Proofs.AllocateVectorOuterOutputFrame

/-! Fourteen actual f687 instructions cache the returned record, copy twelve output
bytes, branch over the fallback, and restore SP. Source/output may overlap. -/
namespace WNear.Proofs.AllocateVectorOuter
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
open AllocateSearch (GasUnits gasUnits_paid)
set_option maxRecDepth 16384

def tailAfter (s : Store NearState) (op memoryIndex globalIndex : Nat) (memory : Memory)
    (out count scratch : UInt32) :=
  exitAfter (outputAfter (paid s op 3) op memoryIndex memory out count (readI64 memory (scratch.toNat+8)))
    op globalIndex scratch

def tailCode : Expr := WNear.Binary.AllocateVectorOuter.cache ++ WNear.Binary.AllocateVectorOuter.output ++ [.br 1]

attribute [local irreducible] WP atCode tailAfter outputAfter highStore

private theorem modules_paid (s : Store NearState) (op n : Nat) : (paid s op n).modules=s.modules := by
  induction n with | zero=>rfl | succ n ih=>exact ih
private theorem mems_paid (s : Store NearState) (op n : Nat) : (paid s op n).mems=s.mems := by
  induction n with | zero=>rfl | succ n ih=>exact ih
private theorem globals_paid (s : Store NearState) (op n : Nat) : (paid s op n).globals=s.globals := by
  induction n with | zero=>rfl | succ n ih=>exact ih

theorem tailAfter_gas (s : Store NearState) (op memoryIndex globalIndex : Nat) (memory : Memory)
    (out count scratch : UInt32) : GasUnits s (tailAfter s op memoryIndex globalIndex memory out count scratch) op 14 := by
  have a := (gasUnits_paid s op 3).trans (outputAfter_gas (paid s op 3) op memoryIndex memory out count (readI64 memory (scratch.toNat+8)))
  have b : GasUnits (outputAfter (paid s op 3) op memoryIndex memory out count (readI64 memory (scratch.toNat+8)))
      (tailAfter s op memoryIndex globalIndex memory out count scratch) op 5 :=
    (gasUnits_paid _ op 5).host_eq (by unfold tailAfter exitAfter;rfl)
  simpa only [Nat.reduceAdd] using a.trans b

theorem wp_tail (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (mi : ModuleInst) (memoryIndex globalIndex : Nat) (memory : Memory) (global : GlobalInst)
    (out count scratch : UInt32) (post : Post)
    (h0 : frame.locals[0]?=some (.i32 out)) (h2 : frame.locals[2]?=some (.i32 count))
    (h3 : frame.locals[3]?=some (.i32 scratch)) (hs : 5≤frame.locals.size)
    (hm : s.modules[frame.inst]?=some mi) (hi : mi.memAddrs[0]?=some memoryIndex)
    (hgIndex : mi.globalAddrs[0]?=some globalIndex)
    (hmem : s.mems[memoryIndex]?=some memory) (hg : s.globals[globalIndex]?=some global)
    (hw : memory.wf) (ho : out.toNat+12≤memory.byteSize) (hb : scratch.toNat+16≤memory.byteSize)
    (hc : s.host.gas.Credits (14*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (tailAfter s cfg.regularOpCost memoryIndex globalIndex memory out count scratch)
      limits stack (cachedFrame frame memory scratch) callers code)) rest post) :
    WP cfg (fuel+14) (.next (atCode s limits stack (nestedFrame frame stack.size code) callers tailCode))
      (14*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  let cache := readI64 memory (scratch.toNat+8)
  let cf := cachedFrame frame memory scratch
  let beforeOutput := paid s op 3
  let output := outputAfter beforeOutput op memoryIndex memory out count cache
  have fields := outputAfter_fields beforeOutput op memoryIndex memory out count cache
  have c3 : beforeOutput.host.gas.Credits (11*op+rest) := paid_credits s op 3 _ (hc.mono (by dsimp [op];omega))
  have cOut : output.host.gas.Credits (5*op+rest) :=
    (outputAfter_gas beforeOutput op memoryIndex memory out count cache _ (c3.mono (by omega))).2.2
  have moduleOut : output.modules[cf.inst]?=some mi := by
    rw [fields.2.1,modules_paid]
    exact hm
  have globalOut : output.globals[globalIndex]?=some global := by
    rw [fields.2.2.2,globals_paid]
    exact hg
  have f0 : cf.locals[0]?=some (.i32 out) := by simp [cf,cachedFrame,h0]
  have f2 : cf.locals[2]?=some (.i32 count) := by simp [cf,cachedFrame,h2]
  have f3 : cf.locals[3]?=some (.i32 scratch) := by simp [cf,cachedFrame,h3]
  have f4 : cf.locals[4]?=some (.i64 cache) := by simp [cf,cachedFrame,cache,show 4<frame.locals.size by omega]
  have exitNext : WP cfg fuel (.next (atCode (exitAfter output cfg.regularOpCost globalIndex scratch)
      limits stack cf callers code)) rest post := by simpa only [tailAfter,output,beforeOutput,cache,cf,op] using hnext
  have exit := wp_exit cfg fuel rest output limits stack cf callers code mi globalIndex global scratch post
    f3 moduleOut hgIndex globalOut cOut exitNext
  have om : beforeOutput.modules[(nestedFrame cf stack.size code).inst]?=some mi := by
    rw [modules_paid]
    exact hm
  have mm : beforeOutput.mems[memoryIndex]?=some memory := by rw [mems_paid];exact hmem
  have out := wp_output cfg (fuel+5) (5*op+rest) beforeOutput limits stack (nestedFrame cf stack.size code) callers [.br 1]
    mi memoryIndex memory out count cache post f0 f2 f4 om hi mm hw ho (c3.mono (by omega)) exit
  have cacheNext : WP cfg (fuel+11) (.next (atCode (paid s cfg.regularOpCost 3) limits stack
      (cachedFrame (nestedFrame frame stack.size code) memory scratch) callers
      (WNear.Binary.AllocateVectorOuter.output++[.br 1]))) (11*op+rest) post := by
    have ce : 6*cfg.regularOpCost+(5*op+rest)=11*op+rest := by dsimp [op];omega
    rw [ce] at out
    simpa only [beforeOutput,cf,cachedFrame,nestedFrame,outerFrame,emptyBlockFrame,cache,op,Nat.add_assoc,Nat.reduceAdd] using out
  have cacheStep := wp_cache cfg (fuel+11) (11*op+rest) s limits stack (nestedFrame frame stack.size code) callers
    (WNear.Binary.AllocateVectorOuter.output++[.br 1]) mi memoryIndex memory scratch post h3 hm hi hmem hb
    (hc.mono (by dsimp [op];omega)) cacheNext
  have ce : 3*cfg.regularOpCost+(11*op+rest)=14*cfg.regularOpCost+rest := by dsimp [op];omega
  rw [ce] at cacheStep
  simpa only [tailCode,List.append_assoc,Nat.add_assoc,Nat.reduceAdd] using cacheStep
end WNear.Proofs.AllocateVectorOuter
