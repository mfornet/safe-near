import Binary.AllocateGrowth
import Proofs.AllocateUnitsCall

/-! Actual f577 requested-word scaling and local assignment. -/
namespace WNear.Proofs.AllocateGrowth
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
attribute [local irreducible] WP atCode
set_option maxRecDepth 16384

def prepared (s : Store NearState) (op : Nat) := paid (AllocateUnits.unitsAfter (paid s op 1) op) op 1
def preparedFrame (frame : CallFrame) (words : UInt32) := {frame with locals:=frame.locals.set! 4 (.i32 (words <<< (2 : UInt32)))}

theorem wp_preparation (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (words : UInt32) (mi : ModuleInst) (address : Nat) (post : Post)
    (h2 : frame.locals[2]?=some (.i32 words)) (hm : s.modules[frame.inst]?=some mi)
    (hi : mi.funcAddrs[572]?=some address)
    (hf : s.funcs[address]?=some (.wasm WNear.Binary.AllocateUnits.unitsSignature frame.inst WNear.Binary.AllocateUnits.unitsFunction))
    (hwords : words.toNat<2^30) (hd : callers.length+1<limits.maxCallDepth)
    (hc : s.host.gas.Credits (21*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (prepared s cfg.regularOpCost) limits base.toArray (preparedFrame frame words) callers code)) rest post) :
    WP cfg (fuel+14) (.next (atCode s limits base.toArray frame callers (WNear.Binary.AllocateGrowth.preparation++code)))
      (21*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  let units := AllocateUnits.unitsAfter (paid s op 1) op
  have c1 := paid_credits s op 1 (19*op+(op+rest)) (hc.mono (by dsimp [op];omega))
  have cu := AllocateUnits.unitsAfter_credits (paid s op 1) op (op+rest) c1
  have set := wp_local_set cfg fuel rest units limits base.toArray frame callers code 4 (.i32 (words <<< (2 : UInt32))) post cu
    (by simpa only [prepared,preparedFrame,units,paid,op] using hnext)
  have hm1 : (paid s op 1).modules[frame.inst]?=some mi := by simpa only [paid,chargedStore] using hm
  have hf1 : (paid s op 1).funcs[address]?=some (.wasm WNear.Binary.AllocateUnits.unitsSignature frame.inst WNear.Binary.AllocateUnits.unitsFunction) := by simpa only [paid,chargedStore] using hf
  have arr : (base++[Value.i32 (words <<< (2 : UInt32))]).toArray=base.toArray.push (.i32 (words <<< (2 : UInt32))) := by apply Array.toList_inj.mp;simp
  have call := AllocateUnits.wp_units_call cfg (fuel+1) (op+rest) (paid s op 1) limits base frame callers (.local_set 4::code) words mi address post
    hm1 hi hf1 hwords hd c1 (by simpa only [units,arr,op] using set)
  have arrIn : (base++[Value.i32 words]).toArray=base.toArray.push (.i32 words) := by apply Array.toList_inj.mp;simp
  have first := wp_local_get cfg (fuel+13) (19*op+(op+rest)) s limits base.toArray frame callers (.call 572::.local_set 4::code) 2 (.i32 words) post h2
    (hc.mono (by dsimp [op];omega)) (by simpa only [arrIn,paid,op,Nat.add_assoc,Nat.reduceAdd] using call)
  have cost : cfg.regularOpCost+(19*op+(op+rest))=21*cfg.regularOpCost+rest := by dsimp [op];omega
  simpa only [WNear.Binary.AllocateGrowth.preparation,List.cons_append,List.nil_append,cost,Nat.add_assoc,Nat.reduceAdd] using first
end WNear.Proofs.AllocateGrowth
