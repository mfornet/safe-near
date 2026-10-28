import Proofs.AllocateRetryPayload
import Proofs.AllocateRetryFrame
import Proofs.AllocatePositiveHead
import Proofs.AllocateRetryGas

/-! Actual final SP restoration and result local of581. -/
namespace WNear.Proofs.AllocateRetry
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode

def restoreFrom (s : Store NearState) (op index : Nat) (sp : UInt32) := paid (setGlobal (paid s op 4) index (.i32 sp)) op 1

theorem wp_restore_result (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (p : Layout) (global : GlobalInst) (post : Post)
    (h3 : frame.locals[3]?=some (.i32 (scratch p))) (h1 : frame.locals[1]?=some (.i32 (result p)))
    (hm : s.modules[frame.inst]?=some p.mi) (hi : p.mi.globalAddrs[0]?=some p.globalIndex)
    (hg : s.globals[p.globalIndex]?=some global) (hs : scratch p+16=p.sp)
    (hc : s.host.gas.Credits (5*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (restoreFrom s cfg.regularOpCost p.globalIndex p.sp) limits
      (stack.push (.i32 (result p))) frame callers code)) rest post) :
    WP cfg (fuel+5) (.next (atCode s limits stack frame callers (WNear.Binary.AllocatePositive.restore++code)))
      (5*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  let restored := setGlobal (paid s op 4) p.globalIndex (.i32 p.sp)
  have c4 : restored.host.gas.Credits (op+rest) := paid_credits s op 4 _ (hc.mono (by dsimp [op]; omega))
  have next : WP cfg fuel (.next (atCode (chargedStore restored cfg.regularOpCost) limits
      (stack.push (.i32 (result p))) frame callers code)) rest post := by simpa only [restoreFrom,restored,paid,op] using hnext
  have get := wp_local_get cfg fuel rest restored limits stack frame callers code 1 (.i32 (result p)) post h1 c4 next
  have restoreNext : WP cfg (fuel+1) (.next (atCode (setGlobal (paid s cfg.regularOpCost 4) p.globalIndex (.i32 (scratch p+16))) limits stack
      frame callers (.local_get 1::code))) (op+rest) post := by simpa only [restored,hs,op] using get
  have restore := ValueReturnBorrow.wp_restore cfg (fuel+1) (op+rest) s limits stack frame callers (.local_get 1::code)
    p.mi p.globalIndex global (scratch p) 3 post h3 hm hi hg (hc.mono (by dsimp [op]; omega)) restoreNext
  have cost : 4*cfg.regularOpCost+(op+rest)=5*cfg.regularOpCost+rest := by dsimp [op]; omega
  rw [cost] at restore
  simpa only [WNear.Binary.AllocatePositive.restore,List.append_eq,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd] using restore


/-- Actual final head write, one free block exit and SP/result suffix. Every
array/read bound is derived from original resources and the sequential memory. -/
theorem wp_suffix (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (p : Layout) (post : Post) (hn : Native p) (hcode : Code s frame.inst p)
    (h0 : frame.locals[0]?=some (.i32 p.allocator)) (h1 : frame.locals[1]?=some (.i32 (result p)))
    (h3 : frame.locals[3]?=some (.i32 (scratch p)))
    (hm : s.mems[p.memoryIndex]?=some p.memory)
    (hg : s.globals[p.globalIndex]?=some p.global) (_hv : p.global.value=.i32 p.sp)
    (hc : (found cfg s p).host.gas.Credits (9*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (after cfg s p) limits
      (base.toArray.push (.i32 (result p))) frame callers code)) rest post) :
    WP cfg (fuel+10) (.next (atCode (found cfg s p) limits base.toArray
      (emptyBlockFrame frame base.toArray.size (WNear.Binary.AllocatePositive.restore++code)) callers
      WNear.Binary.AllocatePositive.updateHead)) (9*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  let f := found cfg s p
  let u := updated cfg s p
  let tail := WNear.Binary.AllocatePositive.restore++code
  have sc := scratch_numbers p hn
  have sizeFinal := (searchedMemory_spec p hn).2.1
  have larger : p.memory.byteSize≤(searchedMemory p).byteSize := by rw [sizeFinal];omega
  have cu : u.host.gas.Credits (5*op+rest) := by
    change (storeI32 (paid f op 4) p.memoryIndex p.allocator.toNat (searchedMemory p) _).host.gas.Credits _
    rw [storeI32_host]
    exact paid_credits f op 4 _ (hc.mono (by dsimp [f,op];omega))
  have moduleU : u.modules[frame.inst]?=some p.mi := by
    rw [(updated_fields cfg s p).2.1]
    exact hcode.originalCode.search.module
  have globalU : u.globals[p.globalIndex]?=some {p.global with value:=.i32 (scratch p)} := by
    rw [updated_globals]
    simp only [setGlobal,Array.getElem?_modify,hg,Option.map_some,ite_true]
  have rn : WP cfg fuel (.next (atCode (restoreFrom u cfg.regularOpCost p.globalIndex p.sp) limits
      (base.toArray.push (.i32 (result p))) frame callers code)) rest post := by
    simpa only [restoreFrom,after,u,op] using hnext
  have restore := wp_restore_result cfg fuel rest u limits base.toArray frame callers code p
    {p.global with value:=.i32 (scratch p)} post h3 h1 moduleU hcode.originalCode.globalIndex globalU sc.2.2.2 cu rn
  let label : Label := ⟨0,base.toArray.size,tail,none⟩
  have en : WP cfg (fuel+5) (.next (atCode u limits base.toArray frame callers label.rest)) (5*op+rest) post := restore
  have ending := wp_end_label cfg (fuel+5) (5*op+rest) u limits base.toArray frame callers label post cu en
  have moduleF : f.modules[(emptyBlockFrame frame base.toArray.size tail).inst]?=some p.mi := by
    rw [(found_fields cfg s p).2.1]
    exact hcode.originalCode.search.module
  have hnxt : WP cfg (fuel+6) (.next (atCode (AllocatePositive.updateFrom f cfg.regularOpCost p.memoryIndex
      (searchedMemory p) p.allocator (scratch p)) limits base.toArray
      (emptyBlockFrame frame base.toArray.size tail) callers [])) (5*op+rest) post := by
    simpa only [AllocatePositive.updateFrom,updated,f,u,label,emptyBlockFrame,op,Nat.add_assoc,Nat.reduceAdd] using ending
  have head := AllocatePositive.wp_update_head cfg (fuel+6) (5*op+rest) f limits base.toArray
    (emptyBlockFrame frame base.toArray.size tail) callers [] p.mi p.memoryIndex (searchedMemory p)
    p.allocator (scratch p) post h0 h3 moduleF hcode.originalCode.search.memoryIndex
    (found_memory cfg s p hm) (by have := hn.allocatorBound;omega) (by have := sc.2.2.1;omega)
    (hc.mono (by dsimp [f,op];omega)) hnxt
  have ce : 4*cfg.regularOpCost+(5*op+rest)=9*cfg.regularOpCost+rest := by dsimp [op];omega
  simpa only [ce,Nat.add_assoc,Nat.reduceAdd,List.append_nil,f,tail] using head
end WNear.Proofs.AllocateRetry
