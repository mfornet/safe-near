import Proofs.AllocateFlaggedCandidate
import Proofs.AllocateFlaggedSplit
import Proofs.AllocateSearchInspect

/-! Full successful candidate path through the real split, including all six
inner block entries and the actual thirteen-label branch. -/
namespace WNear.Proofs.AllocateFlagged
open Wasm Wasm.Near MeteredLogic
open AllocateSearch
open StorePairCaller (paid paid_credits)
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
attribute [local irreducible] WP atCode candidateAfter splitAfter
  WNear.Binary.AllocateSearch.inspect WNear.Binary.AllocateSearch.splitOuter

def searched (s : Store NearState) (op : Nat) (p : Layout) := splitAfter (candidateAfter s op) op p
def searchedFrame (frame : CallFrame) (p : Layout) := finalFrame (candidateFrame frame p) p

theorem wp_inspect_success (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (p : Layout) (post : Post) (hn : Native p) (hr : CandidateReady frame p)
    (hcode : SearchCode s p frame.inst) (hmem : s.mems[p.memoryIndex]? = some p.memory)
    (hd : callers.length+1 < limits.maxCallDepth) (hc : s.host.gas.Credits (240*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (searched s cfg.regularOpCost p) limits stack
      (outerFrame (searchedFrame frame p) stack.size code) callers [])) rest post) :
    WP cfg (fuel+209) (.next (atCode s limits stack (inspectFrame frame stack.size code) callers WNear.Binary.AllocateSearch.inspect))
      (240*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  let cf := candidateFrame frame p
  let current := candidateAfter s op
  let of := outerFrame cf stack.size code
  have v9 : 9<frame.locals.size := by have := hr.size; omega
  have v10 : 10<frame.locals.size := by have := hr.size; omega
  have fitReady : FitReady of p := by
    constructor <;> simp [of,outerFrame,cf,candidateFrame,unitsFrame,prepareFrame,emptyBlockFrame,
      hr.words,hr.headLocal,hr.context,hr.vtable,hr.mask,hr.flag,v9,v10]
    exact hr.size
  have res := candidateAfter_resources s op
  have cc : Code current p of.inst := by
    have inst : of.inst=frame.inst := rfl
    rw [inst]
    exact hcode.toCode.transport s current p frame.inst (congrArg (fun t=>t.funcs) res) (congrArg (fun t=>t.modules) res) (congrArg (fun t=>t.tables) res)
  have mc : current.mems[p.memoryIndex]?=some p.memory := by
    rw [show current.mems=s.mems from congrArg (fun t=>t.mems) res]
    exact hmem
  have c60 := candidateAfter_credits s op (180*op+rest) (hc.mono (by dsimp [op]; omega))
  have sn : WP cfg fuel (.next (atCode (splitAfter current op p) limits stack (finalFrame of p) callers [])) rest post := by
    simpa only [searched,searchedFrame,current,of,cf,finalFrame,mutateFrame,controlFrame,splitFrame,Allocate.resultFrame,Allocate.arithmeticFrame,
      Allocate.callbackFrame,Allocate.fitFrame,backlinkFrame,endReadFrame,AllocateSearch.endSelectedFrame,outerFrame,emptyBlockFrame,op] using hnext
  have split := wp_split_path cfg fuel rest current limits stack of callers (skippedLabels stack.size) [] p post rfl hn fitReady cc mc hd c60 sn
  have splitNext : WP cfg (fuel+158) (.next (atCode current limits stack
      (splitShell (inspectFrame cf stack.size code) stack.size) callers WNear.Binary.AllocateSearch.splitBody)) (180*op+rest) post := by
    simpa only [shell_labels,of,List.append_nil] using split
  have shell := wp_split_shell cfg (fuel+158) (180*op+rest) current limits stack (inspectFrame cf stack.size code) callers post c60 splitNext
  have cn : WP cfg (fuel+164) (.next (atCode current limits stack (candidateFrame (inspectFrame frame stack.size code) p) callers
      (.block .empty WNear.Binary.AllocateSearch.splitOuter::WNear.Binary.AllocateSearch.inspect.drop 19))) (180*op+rest) post := by
    simpa only [cf,candidateFrame,unitsFrame,prepareFrame,inspectFrame,scanFrame,outerFrame,emptyBlockFrame,emptyLoopFrame,
      Nat.add_assoc,Nat.reduceAdd] using shell
  have cInput : SearchCode s p (inspectFrame frame stack.size code).inst := hcode
  have hInput : (inspectFrame frame stack.size code).locals[1]?=some (.i32 (head p)) := hr.headLocal
  have wInput : (inspectFrame frame stack.size code).locals[0]?=some (.i32 p.words) := hr.words
  have sizeInput : 14≤(inspectFrame frame stack.size code).locals.size := hr.size
  have result := wp_candidate cfg (fuel+164) (180*op+rest) s limits stack (inspectFrame frame stack.size code) callers
    (.block .empty WNear.Binary.AllocateSearch.splitOuter::WNear.Binary.AllocateSearch.inspect.drop 19) p post hn cInput hInput wInput sizeInput hmem hd
    (hc.mono (by dsimp [op]; omega)) cn
  have cost : 60*cfg.regularOpCost+(180*op+rest)=240*cfg.regularOpCost+rest := by dsimp [op]; omega
  rw [cost] at result
  rw [WNear.Binary.AllocateSearch.inspect_eq]
  simpa only [Nat.add_assoc,Nat.reduceAdd,List.append_assoc,List.append_eq,List.cons_append,List.nil_append] using result
end
end WNear.Proofs.AllocateFlagged
