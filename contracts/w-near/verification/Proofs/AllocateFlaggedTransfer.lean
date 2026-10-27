import Proofs.AllocateFlaggedWords
import Proofs.AllocateFlaggedMemory

/-! Actual flags-two fall-through and transfer to the new split header. -/
namespace WNear.Proofs.AllocateFlagged
open Wasm Wasm.Near MeteredLogic
open AllocateSearch (Layout)
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode readI32 writeI32

def clearedStore (s : Store NearState) (op : Nat) (p : Layout) := clearStore s op p.memoryIndex (linkedMemory p) (head p) (linkedWord p)
def flaggedStore (s : Store NearState) (op : Nat) (p : Layout) := flagStore (clearedStore s op p) op p.memoryIndex (clearedFlagMemory p) (header p)
def transferred (s : Store NearState) (op : Nat) (p : Layout) := paid (flaggedStore s op p) op 1

theorem wp_flag_fallthrough (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (word : UInt32) (post : Post)
    (h2 : frame.locals[2]?=some (.i32 word)) (hf : word &&& 2=2)
    (hc : s.host.gas.Credits (5*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 5) limits stack frame callers code)) rest post) :
    WP cfg (fuel+5) (.next (atCode s limits stack frame callers (WNear.Binary.AllocateSearch.flagExit++code)))
      (5*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  rw [show 5*cfg.regularOpCost+rest=cfg.regularOpCost+(4*op+rest) by dsimp [op]; omega]
  apply wp_local_get cfg (fuel+4) _ s limits stack frame callers _ 2 (.i32 word) post h2 (hc.mono (by dsimp [op]; omega))
  rw [show 4*op+rest=cfg.regularOpCost+(3*op+rest) by dsimp [op]; omega]
  apply wp_i32_const cfg (fuel+3) _ (paid s op 1) limits _ frame callers _ 2 post
  · exact paid_credits s op 1 _ (hc.mono (by dsimp [op]; omega))
  rw [show 3*op+rest=cfg.regularOpCost+(2*op+rest) by dsimp [op]; omega]
  apply wp_i32_and cfg (fuel+2) _ (paid s op 2) limits stack frame callers _ word 2 post
  · exact paid_credits s op 2 _ (hc.mono (by dsimp [op]; omega))
  rw [hf]
  rw [show 2*op+rest=cfg.regularOpCost+(op+rest) by dsimp [op]; omega]
  apply wp_i32_eqz cfg (fuel+1) _ (paid s op 3) limits stack frame callers _ 2 post
  · exact paid_credits s op 3 _ (hc.mono (by dsimp [op]; omega))
  simp only [show Numeric.bool ((2:UInt32)==0)=0 by decide]
  apply wp_br_if_zero cfg fuel rest (paid s op 4) limits stack frame callers code 12 post
  · exact paid_credits s op 4 _ (hc.mono (by dsimp [op]; omega))
  · simpa only [paid,op] using hnext

theorem wp_transfer (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (skipped : List Label) (code discarded : Expr) (p : Layout) (post : Post)
    (hskip : skipped.length=12) (hn : Native p)
    (h1 : frame.locals[1]?=some (.i32 (head p))) (h2 : frame.locals[2]?=some (.i32 (linkedWord p)))
    (h9 : frame.locals[9]?=some (.i32 (header p)))
    (hm : s.modules[frame.inst]?=some p.mi) (hi : p.mi.memAddrs[0]?=some p.memoryIndex)
    (hmem : s.mems[p.memoryIndex]?=some (linkedMemory p))
    (hc : s.host.gas.Credits (12*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (transferred s cfg.regularOpCost p) limits stack frame callers code)) rest post) :
    WP cfg (fuel+12) (.next (atCode s limits stack (labelPrefixFrame frame stack.size skipped code) callers
      (WNear.Binary.AllocateFlagged.transfer++discarded))) (12*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  let cleared := clearedStore s op p
  let flagged := flaggedStore s op p
  let nested := labelPrefixFrame frame stack.size skipped code
  have bounds := intervals p hn
  have ls := linked_shape p hn
  have cs := clearedFlag_shape p hn
  have c5 : cleared.host.gas.Credits (6*op+(op+rest)) := by
    unfold cleared clearedStore clearStore
    rw [storeI32_host]
    exact paid_credits s op 5 _ (hc.mono (by dsimp [op]; omega))
  have c11 : flagged.host.gas.Credits (op+rest) := by
    unfold flagged flaggedStore flagStore
    rw [storeI32_host]
    exact paid_credits cleared op 6 _ c5
  have mc : cleared.mems[p.memoryIndex]?=some (clearedFlagMemory p) := by
    exact storeI32_memory (paid s op 5) p.memoryIndex (head p).toNat (linkedMemory p) (linkedWord p &&& 4294967293)
      (by simpa only [paid,chargedStore] using hmem)
  have moduleC : cleared.modules[nested.inst]?=some p.mi := by
    simpa only [cleared,clearedStore,clearStore,storeI32_modules,paid,chargedStore,nested,labelPrefixFrame] using hm
  have bn : WP cfg fuel (.next (atCode (chargedStore flagged cfg.regularOpCost) limits stack frame callers code)) rest post := by
    simpa only [transferred,flagged,paid,op] using hnext
  have branch := wp_br_label cfg fuel rest flagged limits stack frame callers skipped code discarded post c11 bn
  have mn : WP cfg (fuel+1) (.next (atCode (flagStore cleared cfg.regularOpCost p.memoryIndex (clearedFlagMemory p) (header p)) limits stack
      nested callers (.br 12::discarded))) (op+rest) post := by
    simpa only [hskip,flagged,flaggedStore,nested] using branch
  have mark := wp_mark_new cfg (fuel+1) (op+rest) cleared limits stack nested callers (.br 12::discarded) (header p) p.mi p.memoryIndex
    (clearedFlagMemory p) post h9 moduleC hi mc (by rw [cs.size]; omega) c5 mn
  have cn : WP cfg (fuel+7) (.next (atCode (clearStore s cfg.regularOpCost p.memoryIndex (linkedMemory p) (head p) (linkedWord p)) limits stack
      nested callers (WNear.Binary.AllocateFlagged.markNew++.br 12::discarded))) (7*op+rest) post := by
    have cost : 6*cfg.regularOpCost+(op+rest)=7*op+rest := by dsimp [op]; omega
    rw [cost] at mark
    simpa only [cleared,clearedStore,Nat.add_assoc,Nat.reduceAdd] using mark
  have clear := wp_clear_old cfg (fuel+7) (7*op+rest) s limits stack nested callers
    (WNear.Binary.AllocateFlagged.markNew++.br 12::discarded) (head p) (linkedWord p) p.mi p.memoryIndex (linkedMemory p) post
    h1 h2 hm hi hmem (by rw [ls.size]; omega) (hc.mono (by dsimp [op]; omega)) cn
  have cost : 5*cfg.regularOpCost+(7*op+rest)=12*cfg.regularOpCost+rest := by dsimp [op]; omega
  rw [cost] at clear
  simpa only [WNear.Binary.AllocateFlagged.transfer,Nat.add_assoc,Nat.reduceAdd,List.append_assoc,List.append_eq,List.cons_append,List.nil_append] using clear
end WNear.Proofs.AllocateFlagged
