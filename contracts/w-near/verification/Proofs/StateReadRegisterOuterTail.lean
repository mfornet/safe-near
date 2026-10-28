import Proofs.StateReadRegisterOuterCopyBody
import Proofs.InterfaceStack
import Proofs.AllocateFlaggedBranch

/-! Actual523 sequentialcopy, two-label exit and SP48 restoration. -/
namespace WNear.Proofs.StateReadRegisterOuter
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode copied copyHigh copyLow

def finished (s : Store NearState) (op index globalIndex : Nat) (memory : Memory) (out scratch : UInt32) :=
  setGlobal (paid (chargedStore (copied s op index memory out scratch) op) op 4) globalIndex (.i32 (scratch+48))

theorem wp_tail (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code alternate : Expr) (out scratch : UInt32) (mi : ModuleInst) (index globalIndex : Nat) (global : GlobalInst)
    (memory : Memory) (post : Post)
    (ho : frame.locals[0]?=some (.i32 out)) (hs : frame.locals[2]?=some (.i32 scratch))
    (hm : s.modules[frame.inst]?=some mi) (hi : mi.memAddrs[0]?=some index) (hmem : s.mems[index]?=some memory)
    (hgi : mi.globalAddrs[0]?=some globalIndex) (hg : s.globals[globalIndex]?=some global)
    (hwf : memory.wf) (hrh : (scratch+32+8).toNat+4≤memory.byteSize) (hwh : (out+8).toNat+4≤memory.byteSize)
    (hrl : scratch.toNat+32+8≤memory.byteSize) (hwl : out.toNat+8≤memory.byteSize)
    (hc : s.host.gas.Credits (19*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (finished s cfg.regularOpCost index globalIndex memory out scratch)
      limits stack frame callers code)) rest post) :
    WP cfg (fuel+19) (.next (atCode s limits stack
      (emptyBlockFrame (emptyBlockFrame frame stack.size (WNear.Binary.StateReadRegisterOuter.restore++code)) stack.size alternate)
      callers (WNear.Binary.StateReadRegisterOuter.copyHigh++WNear.Binary.StateReadRegisterOuter.copyLow++[.br 1])))
      (19*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  let cp := copied s op index memory out scratch
  let branched := chargedStore cp op
  have cc : cp.host.gas.Credits (5*op+rest) := by
    have c10 : (copyHigh s op index memory out scratch).host.gas.Credits (9*op+rest) := by
      simpa only [copyHigh,storeI32_host] using paid_credits s op 10 (9*op+rest) (hc.mono (by dsimp [op];omega))
    have c4 := paid_credits (copyHigh s op index memory out scratch) op 4 (5*op+rest) (c10.mono (by omega))
    simpa only [cp,copied,copyLow,storeI64_host] using c4
  have cb : branched.host.gas.Credits (4*op+rest) := StorePair.charged_credits cp op _ (cc.mono (by omega))
  have bm : branched.modules[frame.inst]?=some mi := by
    simpa only [branched,cp,copied,copyLow,copyHigh,storeI64_modules,storeI32_modules,paid,chargedStore] using hm
  have bg : branched.globals[globalIndex]?=some global := by
    simpa only [branched,cp,copied,copyLow,copyHigh,storeI64_globals,storeI32_globals,paid,chargedStore] using hg
  have rn : WP cfg fuel (.next (atCode (setGlobal (paid branched op 4) globalIndex (.i32 (scratch+48))) limits stack frame callers code)) rest post := hnext
  have restore := InterfaceStack.wp_restore cfg fuel rest branched limits stack frame callers code mi globalIndex global scratch 2 48 post hs bm hgi bg cb rn
  let exit := WNear.Binary.StateReadRegisterOuter.restore++code
  have br := AllocateFlagged.wp_br_label cfg (fuel+4) (4*op+rest) cp limits stack frame callers
    [{arity:=0,height:=stack.size,rest:=alternate,loop:=none}] exit [] post (cc.mono (by omega)) restore
  let nf := emptyBlockFrame (emptyBlockFrame frame stack.size exit) stack.size alternate
  have bn : WP cfg ((fuel+4)+1) (.next (atCode cp limits stack nf callers [.br 1])) (5*op+rest) post := by
    simpa only [nf,exit,emptyBlockFrame,labelPrefixFrame,List.cons_append,List.nil_append,List.length_cons,List.length_nil,
      show cfg.regularOpCost+(4*op+rest)=5*op+rest by dsimp [op];omega] using br
  have copy := wp_copy cfg ((fuel+4)+1) (5*op+rest) s limits stack nf callers [.br 1] out scratch mi index memory post
    ho hs hm hi hmem hwf hrh hwh hrl hwl (hc.mono (by dsimp [op];omega)) bn
  have ce : 14*cfg.regularOpCost+(5*op+rest)=19*cfg.regularOpCost+rest := by dsimp [op];omega
  rw [ce] at copy
  simpa only [nf,exit,List.append_assoc,Nat.add_assoc,Nat.reduceAdd] using copy
end WNear.Proofs.StateReadRegisterOuter
