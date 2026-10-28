import Proofs.AllocateRetryArguments
import Proofs.AllocateRetryCode

/-! The actual four growth arguments and complete577 call over an arbitrary prestore. -/
namespace WNear.Proofs.AllocateRetry.Grow
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode AllocateGrowth.callAfter memoryGrowCost

def after (cfg : WasmConfig) (s : Store NearState) (p : AllocateRetry.Layout) :=
  AllocateGrowth.callAfter cfg (paid s cfg.regularOpCost 4) (AllocateRetry.growthLayout p)

theorem wp_grow (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (p : AllocateRetry.Layout) (post : Post)
    (hn : AllocateRetry.Native p) (hcode : AllocateRetry.Code s frame.inst p)
    (h2 : frame.locals[2]?=some (.i32 1))
    (h3 : frame.locals[3]?=some (.i32 (AllocateRetry.scratch p)))
    (h4 : frame.locals[4]?=some (.i32 (AllocateRetry.words p)))
    (hm : s.mems[p.memoryIndex]?=some (AllocateRetry.savedMemory p))
    (hd : callers.length+3<limits.maxCallDepth)
    (hc : s.host.gas.Credits (182*cfg.regularOpCost+memoryGrowCost cfg (AllocateGrowth.delta (AllocateRetry.growthLayout p))+rest))
    (hnext : WP cfg fuel (.next (atCode (after cfg s p) limits base.toArray frame callers code)) rest post) :
    WP cfg (fuel+141) (.next (atCode s limits base.toArray frame callers
      (WNear.Binary.AllocateRetry.growthArguments++(.call 577::code))))
      (182*cfg.regularOpCost+memoryGrowCost cfg (AllocateGrowth.delta (AllocateRetry.growthLayout p))+rest) post := by
  let op := cfg.regularOpCost
  let fee := memoryGrowCost cfg (AllocateGrowth.delta (AllocateRetry.growthLayout p))
  have paidCode := hcode.paid s op 4 frame.inst p
  have growthCode := paidCode.growth (paid s op 4) frame.inst p
  have mem : (paid s op 4).mems[p.memoryIndex]?=some (AllocateRetry.savedMemory p) := by
    simpa only [paid,chargedStore] using hm
  have credits := paid_credits s op 4 (178*op+fee+rest) (hc.mono (by dsimp [op,fee];omega))
  have callNext : WP cfg fuel (.next (atCode (AllocateGrowth.callAfter cfg (paid s op 4) (AllocateRetry.growthLayout p)) limits
      base.toArray frame callers code)) rest post := by simpa only [after,op] using hnext
  have call := AllocateGrowth.wp_call cfg fuel rest (paid s op 4) limits base frame callers code
    (AllocateRetry.growthLayout p) 1057464 p.growthAddress post hn.growth growthCode mem
    hcode.growthIndex paidCode.growthFunction hd credits callNext
  have arr : (base++[Value.i32 (AllocateRetry.scratch p),.i32 1057464,.i32 (AllocateRetry.words p),.i32 1]).toArray=
      ((((base.toArray.push (.i32 (AllocateRetry.scratch p))).push (.i32 1057464)).push (.i32 (AllocateRetry.words p))).push (.i32 1)) := by
    apply Array.toList_inj.mp
    simp
  have callCast : WP cfg (fuel+137) (.next (atCode (paid s op 4) limits
      ((((base.toArray.push (.i32 (AllocateRetry.scratch p))).push (.i32 1057464)).push (.i32 (AllocateRetry.words p))).push (.i32 1))
      frame callers (.call 577::code))) (178*op+fee+rest) post := by
    simpa only [AllocateRetry.growthLayout,arr,op,fee] using call
  have args := AllocateRetry.wp_growth_arguments cfg (fuel+137) (178*op+fee+rest) s limits base.toArray frame callers
    (.call 577::code) (AllocateRetry.scratch p) (AllocateRetry.words p) post h3 h4 h2
    (hc.mono (by dsimp [op,fee];omega)) callCast
  have cost : 4*cfg.regularOpCost+(178*op+fee+rest)=182*cfg.regularOpCost+memoryGrowCost cfg (AllocateGrowth.delta (AllocateRetry.growthLayout p))+rest := by
    dsimp [op,fee]
    omega
  rw [cost] at args
  simpa only [Nat.add_assoc,Nat.reduceAdd] using args
end WNear.Proofs.AllocateRetry.Grow
