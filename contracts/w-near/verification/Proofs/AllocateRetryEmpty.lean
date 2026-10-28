import Proofs.AllocateRetryArguments
import Proofs.AllocateRetryDomain

/-! Actual first search on the original empty allocator head. -/
namespace WNear.Proofs.AllocateRetry
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode AllocateEmpty.callAfter

def emptyFrom (s : Store NearState) (op : Nat) := AllocateEmpty.callAfter (paid s op 7) op

theorem wp_empty_attempt (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (p : Layout) (post : Post) (hn : Native p)
    (h4 : frame.locals[4]?=some (.i32 (words p))) (h2 : frame.locals[2]?=some (.i32 1))
    (h3 : frame.locals[3]?=some (.i32 (scratch p)))
    (hcode : Code s frame.inst p) (hmem : s.mems[p.memoryIndex]?=some (savedMemory p))
    (hd : callers.length+2<limits.maxCallDepth) (hc : s.host.gas.Credits (44*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (emptyFrom s cfg.regularOpCost) limits
      (base.toArray.push (.i32 0)) frame callers code)) rest post) :
    WP cfg (fuel+32) (.next (atCode s limits base.toArray frame callers (WNear.Binary.Allocate.attempt++code)))
      (44*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  let q := AllocatePositive.searchLayout p.toLayout
  have hc7 := paid_credits s op 7 (37*op+rest) (hc.mono (by dsimp [op];omega))
  have hm7 : (paid s op 7).modules[frame.inst]?=some p.mi := by simpa only [paid,chargedStore,AllocatePositive.searchLayout] using hcode.originalCode.search.module
  have mf7 : (paid s op 7).funcs[p.searchAddress]?=some (.wasm WNear.Binary.AllocateSearch.signature frame.inst WNear.Binary.Allocate.searchFunction) := by
    simpa only [paid,chargedStore] using hcode.originalCode.searchFunction
  have mem7 : (paid s op 7).mems[p.memoryIndex]?=some (savedMemory p) := by simpa only [paid,chargedStore] using hmem
  have zero : AllocateSearch.head q=0 := by
    change readI32 (savedMemory p) (scratch p+12).toNat=0
    rw [(scratch_numbers p hn).2.1]
    exact saved_root p hn
  have rootBound : q.root.toNat+4≤q.memory.byteSize := by
    change (scratch p+12).toNat+4≤(savedMemory p).byteSize
    rw [(scratch_numbers p hn).2.1,(saved_shape p hn).2.1]
    have h:=(scratch_numbers p hn).2.2.1
    omega
  have next : WP cfg fuel (.next (atCode (AllocateEmpty.callAfter (paid s op 7) op) limits
      (base++[Value.i32 0]).toArray frame callers code)) rest post := by
    have arr : (base++[Value.i32 0]).toArray=base.toArray.push (.i32 0) := by apply Array.toList_inj.mp;simp
    simpa only [emptyFrom,op,arr] using hnext
  have call := AllocateEmpty.wp_call cfg fuel rest (paid s op 7) limits base frame callers code q p.searchAddress post
    zero hm7 hcode.originalCode.search.memoryIndex rootBound mem7 hcode.originalCode.searchIndex mf7 hd hc7 next
  have args := AllocatePositive.wp_arguments cfg (fuel+25) (37*op+rest) s limits base frame callers code p.toLayout post
    h4 h2 h3 (hc.mono (by dsimp [op];omega)) call
  have cost : 7*cfg.regularOpCost+(37*op+rest)=44*cfg.regularOpCost+rest := by dsimp [op];omega
  simpa only [cost,Nat.add_assoc,Nat.reduceAdd] using args
end WNear.Proofs.AllocateRetry
