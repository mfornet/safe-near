import Binary.AllocateCallback
import Proofs.AllocateUnitsCall
import NearVM.MeteredI32MemoryRules

/-! The real indirect578 callback and572 byte scaling in f580. Metadata and
vtable memory are original structural resources, never execution callbacks. -/
namespace WNear.Proofs.Allocate
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
open WNear.Binary.AllocateUnits
set_option maxRecDepth 16384
set_option maxHeartbeats 500000
attribute [local irreducible] WP atCode readI32

def callbackAfter (s : Store NearState) (op : Nat) :=
  paid (AllocateUnits.unitsAfter (AllocateUnits.quantumAfter (paid s op 4) op) op) op 1

def callbackFrame (frame : CallFrame) := {frame with locals := frame.locals.set! 13 (.i32 64)}

/-- The callback really executes f578, returns16, then really executes f572 and
stores64 in local13. Both typed activations and all return steps are included. -/
theorem wp_callback (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (context words vtable : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory)
    (tableAddress functionAddress inst address572 : Nat) (table : TableInst) (post : Post)
    (hcxt : frame.locals[3]? = some (.i32 context)) (hw : frame.locals[0]? = some (.i32 words))
    (hvt : frame.locals[4]? = some (.i32 vtable))
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.memAddrs[0]? = some index)
    (hmem : s.mems[index]? = some memory) (hb : vtable.toNat+20 ≤ memory.byteSize)
    (hti : mi.tableAddrs[0]? = some tableAddress) (ht : s.tables[tableAddress]? = some table)
    (he : table.elems[(readI32 memory (vtable.toNat+16)).toNat]? = some (.func functionAddress))
    (hft : mi.types[13]? = some quantumSignature)
    (hf : s.funcs[functionAddress]? = some (.wasm quantumSignature inst quantumFunction))
    (hi572 : mi.funcAddrs[572]? = some address572)
    (hf572 : s.funcs[address572]? = some (.wasm unitsSignature frame.inst unitsFunction))
    (hd : callers.length+1 < limits.maxCallDepth) (hc : s.host.gas.Credits (35*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (callbackAfter s cfg.regularOpCost) limits base.toArray
      (callbackFrame frame) callers code)) rest post) :
    WP cfg (fuel+20) (.next (atCode s limits base.toArray frame callers (WNear.Binary.Allocate.callbackCode++code)))
      (35*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  let selected := AllocateUnits.quantumAfter (paid s op 4) op
  let converted := AllocateUnits.unitsAfter selected op
  have cm := paid_credits s op 4 (11*op+(19*op+(op+rest))) (hc.mono (by dsimp [op]; omega))
  have cq := AllocateUnits.quantumAfter_credits (paid s op 4) op (19*op+(op+rest)) cm
  have cu := AllocateUnits.unitsAfter_credits selected op (op+rest) cq
  have push (value : Value) : base.toArray.push value = (base++[value]).toArray := by
    apply Array.toList_inj.mp
    simp
  have lastNext : WP cfg fuel (.next (atCode (chargedStore converted op) limits base.toArray
      {frame with locals:=frame.locals.set! 13 (.i32 64)} callers code)) rest post := by
    simpa only [converted,selected,callbackAfter,callbackFrame,paid,op] using hnext
  have last := wp_local_set cfg fuel rest converted limits base.toArray frame callers code 13 (.i32 64) post cu lastNext
  have shift : (16 : UInt32) <<< (2 : UInt32) = 64 := by decide
  have last' : WP cfg (fuel+1) (.next (atCode converted limits (base++[Value.i32 (16 <<< (2 : UInt32))]).toArray frame callers
      (.local_set 13::code))) (op+rest) post := by simpa only [push,shift,op] using last
  have hmQ : selected.modules[frame.inst]? = some mi := by
    simpa only [selected,AllocateUnits.quantumAfter,AllocateUnits.entered9,paid,chargedStore] using hm
  have hfQ : selected.funcs[address572]? = some (.wasm unitsSignature frame.inst unitsFunction) := by
    simpa only [selected,AllocateUnits.quantumAfter,AllocateUnits.entered9,paid,chargedStore] using hf572
  have sixteen : (16 : UInt32).toNat < 2^30 := by decide
  have units := AllocateUnits.wp_units_call cfg (fuel+1) (op+rest) selected limits base frame callers (.local_set 13::code)
    16 mi address572 post hmQ hi572 hfQ sixteen hd cq last'
  have hm4 : (paid s op 4).modules[frame.inst]? = some mi := by simpa only [paid,chargedStore] using hm
  have ht4 : (paid s op 4).tables[tableAddress]? = some table := by simpa only [paid,chargedStore] using ht
  have hf4 : (paid s op 4).funcs[functionAddress]? = some (.wasm quantumSignature inst quantumFunction) := by simpa only [paid,chargedStore] using hf
  have quantum := AllocateUnits.wp_quantum_indirect cfg (fuel+13) (19*op+(op+rest)) (paid s op 4) limits base frame callers
    (.call 572::.local_set 13::code) context words (readI32 memory (vtable.toNat+16)) mi tableAddress functionAddress inst table post
    hm4 hti ht4 he hft hf4 hd cm (by simpa only [selected,Nat.add_assoc,Nat.reduceAdd] using units)
  have args : ((base.toArray.push (.i32 context)).push (.i32 words)) = (base++[Value.i32 context,.i32 words]).toArray := by
    apply Array.toList_inj.mp
    simp
  have quantum' : WP cfg (fuel+16) (.next (atCode (paid s op 4) limits
      (((base.toArray.push (.i32 context)).push (.i32 words)).push (.i32 (readI32 memory (vtable.toNat+16)))) frame callers
      (.call_indirect 13 0::.call 572::.local_set 13::code))) (31*op+rest) post := by
    have cost : 11*cfg.regularOpCost+(19*op+(op+rest))=31*op+rest := by dsimp [op]; omega
    rw [cost] at quantum
    simpa only [args,Nat.add_assoc,Nat.reduceAdd] using quantum
  have hm3 : (paid s op 3).modules[frame.inst]? = some mi := by simpa only [paid,chargedStore] using hm
  have hmem3 : (paid s op 3).mems[index]? = some memory := by simpa only [paid,chargedStore] using hmem
  rw [show 35*cfg.regularOpCost+rest=cfg.regularOpCost+(34*op+rest) by dsimp [op]; omega]
  apply wp_local_get cfg (fuel+19) _ s limits base.toArray frame callers _ 3 (.i32 context) post hcxt (hc.mono (by dsimp [op]; omega))
  rw [show 34*op+rest=cfg.regularOpCost+(33*op+rest) by dsimp [op]; omega]
  apply wp_local_get cfg (fuel+18) _ (paid s op 1) limits _ frame callers _ 0 (.i32 words) post hw
  · exact paid_credits s op 1 _ (hc.mono (by dsimp [op]; omega))
  rw [show 33*op+rest=cfg.regularOpCost+(32*op+rest) by dsimp [op]; omega]
  apply wp_local_get cfg (fuel+17) _ (paid s op 2) limits _ frame callers _ 4 (.i32 vtable) post hvt
  · exact paid_credits s op 2 _ (hc.mono (by dsimp [op]; omega))
  rw [show 32*op+rest=cfg.regularOpCost+(31*op+rest) by dsimp [op]; omega]
  apply wp_i32_load cfg (fuel+16) (31*op+rest) (paid s op 3) limits _ frame callers _
    {align:=2,offset:=16} vtable mi index memory post hm3 hi hmem3 (by omega)
  · exact paid_credits s op 3 _ (hc.mono (by dsimp [op]; omega))
  · exact quantum'

theorem callbackAfter_resources (s : Store NearState) (op : Nat) :
    {callbackAfter s op with host := s.host} = s := by
  simp only [callbackAfter,AllocateUnits.unitsAfter,AllocateUnits.quantumAfter,
    AllocateUnits.entered9,paid,chargedStore]

theorem callbackAfter_credits (s : Store NearState) (op rest : Nat)
    (hc : s.host.gas.Credits (35*op+rest)) : (callbackAfter s op).host.gas.Credits rest := by
  have before := paid_credits s op 4 (11*op+(19*op+(op+rest))) (hc.mono (by omega))
  have selected := AllocateUnits.quantumAfter_credits (paid s op 4) op (19*op+(op+rest)) before
  have converted := AllocateUnits.unitsAfter_credits (AllocateUnits.quantumAfter (paid s op 4) op) op (op+rest) selected
  exact paid_credits _ op 1 rest (by simpa only [Nat.one_mul] using converted)
end WNear.Proofs.Allocate
