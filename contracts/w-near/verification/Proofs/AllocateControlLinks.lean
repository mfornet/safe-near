import Proofs.AllocateControlWords
import Proofs.AllocateSearchMemory
import Binary.AllocateControl

/-! The actual three sequential pointer writes after the split backlink block. -/
namespace WNear.Proofs.AllocateSearch
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
set_option maxHeartbeats 700000
attribute [local irreducible] WP atCode readI32 writeI32

def previousStore (s : Store NearState) (op : Nat) (p : Layout) :=
  Allocate.taggedStore s op p.memoryIndex 4 4 (backlinkedMemory p) (header p) (header p) (head p)
def unflaggedStore (s : Store NearState) (op : Nat) (p : Layout) :=
  maskStore (previousStore s op p) op p.memoryIndex 8 8 (previousMemory p) (head p) 4294967294
def linkedStore (s : Store NearState) (op : Nat) (p : Layout) :=
  taggedTeeStore (unflaggedStore s op p) op p.memoryIndex 0 0 (unflaggedMemory p) (head p) (head p) (header p)

/-- Original native facts derive the tagged value saved in local2, rather than
assuming any future header read or post-write pointer. -/
theorem linked_tag (p : Layout) (hn : Native p) :
    Allocate.taggedValue (unflaggedMemory p) (head p) 0 (header p) = header p := by
  simp only [Allocate.taggedValue,Nat.add_zero,unflagged_head p hn,hn.headFlags,UInt32.zero_or]

theorem wp_link_writes (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (p : Layout) (post : Post) (hn : Native p)
    (hhead : frame.locals[1]? = some (.i32 (head p))) (hheader : frame.locals[9]? = some (.i32 (header p)))
    (hm : s.modules[frame.inst]? = some p.mi) (hi : p.mi.memAddrs[0]? = some p.memoryIndex)
    (hmem : s.mems[p.memoryIndex]? = some (backlinkedMemory p))
    (hc : s.host.gas.Credits (23*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (linkedStore s cfg.regularOpCost p) limits stack
      {frame with locals:=frame.locals.set! 2 (.i32 (header p))} callers code)) rest post) :
    WP cfg (fuel+23) (.next (atCode s limits stack frame callers
      (WNear.Binary.AllocateSearch.previousWrite++WNear.Binary.AllocateSearch.unflagWrite++WNear.Binary.AllocateSearch.headWrite++code)))
      (23*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  let first := previousStore s op p
  let second := unflaggedStore s op p
  have intervals := intervals p hn
  have bs := backlinked_shape p hn
  have ps := previous_shape p hn
  have us := unflagged_shape p hn
  have hmem8 : (paid s op 8).mems[p.memoryIndex]? = some (backlinkedMemory p) := by simpa only [paid,chargedStore] using hmem
  have firstMem : first.mems[p.memoryIndex]? = some (previousMemory p) := by
    exact storeI32_memory (paid s op 8) p.memoryIndex ((header p).toNat+4) (backlinkedMemory p)
      (Allocate.taggedValue (backlinkedMemory p) (header p) 4 (head p)) hmem8
  have firstModule : first.modules[frame.inst]? = some p.mi := by
    simpa only [first,previousStore,Allocate.taggedStore,paid,chargedStore,storeI32_modules] using hm
  have mem6 : (paid first op 6).mems[p.memoryIndex]? = some (previousMemory p) := by simpa only [paid,chargedStore] using firstMem
  have secondMem : second.mems[p.memoryIndex]? = some (unflaggedMemory p) := by
    exact storeI32_memory (paid first op 6) p.memoryIndex ((head p).toNat+8) (previousMemory p)
      (readI32 (previousMemory p) ((head p).toNat+8) &&& 4294967294) mem6
  have secondModule : second.modules[frame.inst]? = some p.mi := by
    simpa only [second,unflaggedStore,maskStore,first,paid,chargedStore,storeI32_modules] using firstModule
  have c1 : first.host.gas.Credits (15*op+rest) := by
    dsimp only [first,previousStore,Allocate.taggedStore]
    rw [storeI32_host]
    exact paid_credits s op 8 _ (hc.mono (by dsimp [op]; omega))
  have c2 : second.host.gas.Credits (9*op+rest) := by
    dsimp only [second,unflaggedStore,maskStore]
    rw [storeI32_host]
    exact paid_credits first op 6 _ (c1.mono (by omega))
  have next : WP cfg fuel (.next (atCode (linkedStore s op p) limits stack
      {frame with locals:=frame.locals.set! 2 (.i32 (Allocate.taggedValue (unflaggedMemory p) (head p) 0 (header p)))} callers code)) rest post := by
    rw [linked_tag p hn]
    exact hnext
  have last := wp_tagged_tee_store cfg fuel rest second limits stack frame callers code 1 1 9 2 0 0
    (head p) (head p) (header p) p.mi p.memoryIndex (unflaggedMemory p) post hhead hhead hheader secondModule hi secondMem
    (by rw [us.size]; omega) (by rw [us.size]; omega) c2 next
  have maskNext : WP cfg (fuel+9) (.next (atCode second limits stack frame callers
      (WNear.Binary.AllocateSearch.headWrite++code))) (9*op+rest) post := by
    simpa only [Allocate.taggedPrefix,WNear.Binary.AllocateSearch.headWrite,List.cons_append,List.nil_append,List.append_assoc] using last
  have mask := wp_mask_word cfg (fuel+9) (9*op+rest) first limits stack frame callers
    (WNear.Binary.AllocateSearch.headWrite++code) 1 8 8 (head p) 4294967294 p.mi p.memoryIndex (previousMemory p) post
    hhead firstModule hi firstMem (by rw [ps.size]; omega) (by rw [ps.size]; omega)
    (c1.mono (by dsimp [op]; omega)) maskNext
  have firstNext : WP cfg (fuel+15) (.next (atCode first limits stack frame callers
      (WNear.Binary.AllocateSearch.unflagWrite++WNear.Binary.AllocateSearch.headWrite++code))) (15*op+rest) post := by
    have cost : 6*cfg.regularOpCost+(9*op+rest)=15*op+rest := by dsimp [op]; omega
    rw [cost] at mask
    simpa only [WNear.Binary.AllocateSearch.unflagWrite,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd,List.append_assoc] using mask
  have result := Allocate.wp_tagged_store cfg (fuel+15) (15*op+rest) s limits stack frame callers
    (WNear.Binary.AllocateSearch.unflagWrite++WNear.Binary.AllocateSearch.headWrite++code) 9 9 1 4 4
    (header p) (header p) (head p) p.mi p.memoryIndex (backlinkedMemory p) post hheader hheader hhead hm hi hmem
    (by rw [bs.size]; omega) (by rw [bs.size]; omega) (hc.mono (by dsimp [op]; omega)) firstNext
  have cost : 8*cfg.regularOpCost+(15*op+rest)=23*cfg.regularOpCost+rest := by dsimp [op]; omega
  rw [cost] at result
  simpa only [Allocate.taggedPrefix,WNear.Binary.AllocateSearch.previousWrite,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd,List.append_assoc] using result
end WNear.Proofs.AllocateSearch
