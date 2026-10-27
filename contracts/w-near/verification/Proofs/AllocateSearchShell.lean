import Binary.AllocateLoop
import NearVM.MeteredLabelRules
import NearVM.MeteredLoopRules

/-! The actual nested labels of580, with their real loop/rest code. -/
namespace WNear.Proofs.AllocateSearch
open Wasm Wasm.Near MeteredLogic
open WNear.Binary.AllocateSearch
noncomputable section
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode outer exhausted scan candidateOuter candidateMiddle candidateInner candidateLoop inspect splitOuter split1 split2 split3 split4 splitBody

def outerFrame (frame : CallFrame) (height : Nat) (code : Expr) := emptyBlockFrame frame height (.local_get 5::code)
def scanFrame (frame : CallFrame) (height : Nat) (code : Expr) :=
  emptyLoopFrame (emptyBlockFrame (outerFrame frame height code) height WNear.Binary.Allocate.commit) height scan (exhausted.drop 1)
def inspectFrame (frame : CallFrame) (height : Nat) (code : Expr) :=
  let co := emptyBlockFrame (scanFrame frame height code) height []
  let cm := emptyBlockFrame co height (candidateOuter.drop 1)
  let ci := emptyBlockFrame cm height (candidateMiddle.drop 1)
  let cl := emptyLoopFrame ci height candidateLoop (candidateInner.drop 1)
  emptyBlockFrame cl height (candidateLoop.drop 1)
def splitShell (frame : CallFrame) (height : Nat) :=
  let a := emptyBlockFrame frame height (inspect.drop 19)
  let b := emptyBlockFrame a height (splitOuter.drop 1)
  let c := emptyBlockFrame b height (split1.drop 1)
  let d := emptyBlockFrame c height (split2.drop 1)
  let e := emptyBlockFrame d height (split3.drop 1)
  emptyBlockFrame e height (split4.drop 1)
def skippedLabels (height : Nat) : List Label :=
  [⟨0,height,split4.drop 1,none⟩,⟨0,height,split3.drop 1,none⟩,
   ⟨0,height,split2.drop 1,none⟩,⟨0,height,split1.drop 1,none⟩,
   ⟨0,height,splitOuter.drop 1,none⟩,⟨0,height,inspect.drop 19,none⟩,
   ⟨0,height,candidateLoop.drop 1,none⟩,⟨0,height,candidateInner.drop 1,some candidateLoop⟩,
   ⟨0,height,candidateMiddle.drop 1,none⟩,⟨0,height,candidateOuter.drop 1,none⟩,
   ⟨0,height,[],none⟩,⟨0,height,exhausted.drop 1,some scan⟩]

theorem shell_labels (frame : CallFrame) (height : Nat) (code : Expr) :
    splitShell (inspectFrame frame height code) height =
      labelPrefixFrame (outerFrame frame height code) height (skippedLabels height) WNear.Binary.Allocate.commit := by
  simp only [splitShell,inspectFrame,scanFrame,outerFrame,emptyBlockFrame,emptyLoopFrame,labelPrefixFrame,skippedLabels,List.cons_append,List.nil_append]

/-- Six real free block entries expose the exact innermost split body. -/
theorem wp_split_shell (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (post : Post) (hc : s.host.gas.Credits rest)
    (hnext : WP cfg fuel (.next (atCode s limits stack (splitShell frame stack.size) callers splitBody)) rest post) :
    WP cfg (fuel+6) (.next (atCode s limits stack frame callers (.block .empty splitOuter::inspect.drop 19))) rest post := by
  apply wp_block_empty cfg (fuel+5) rest s limits stack frame callers splitOuter (inspect.drop 19) post hc
  rw [splitOuter_eq]
  apply wp_block_empty cfg (fuel+4) rest s limits stack _ callers split1 _ post hc
  rw [split1_eq]
  apply wp_block_empty cfg (fuel+3) rest s limits stack _ callers split2 _ post hc
  rw [split2_eq]
  apply wp_block_empty cfg (fuel+2) rest s limits stack _ callers split3 _ post hc
  rw [split3_eq]
  apply wp_block_empty cfg (fuel+1) rest s limits stack _ callers split4 _ post hc
  rw [split4_eq]
  apply wp_block_empty cfg fuel rest s limits stack _ callers splitBody _ post hc
  simpa only [splitShell,List.append_eq,List.nil_append] using hnext
end
end WNear.Proofs.AllocateSearch
