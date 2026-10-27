import Proofs.AllocateGrowthPhaseFrame
import Proofs.AllocateGrowthFinish

/-! Successful-growth suffix over an arbitrary original prestore. -/
namespace WNear.Proofs.AllocateGrowth.Success
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
open AllocateSearch (gasUnits_paid)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode growthAfter grownPhase pageChecked converted committed after beforeGrowth rounded growthStore after569 bytesAfter freshStore recordStore finishStore memoryGrowCost growPages chargedStore grownStore

def grownPhase (cfg : WasmConfig) (s : Store NearState) (p : Layout) := growthAfter cfg s p.memoryIndex p.grown (requested p)
def pageChecked (cfg : WasmConfig) (s : Store NearState) (p : Layout) := paid (grownPhase cfg s p) cfg.regularOpCost 6
def converted (cfg : WasmConfig) (s : Store NearState) (p : Layout) := bytesAfter (pageChecked cfg s p) cfg.regularOpCost
def committed (cfg : WasmConfig) (s : Store NearState) (p : Layout) := freshStore (converted cfg s p) cfg.regularOpCost p.memoryIndex p.grown (header p) (blockBytes p)
def after (cfg : WasmConfig) (s : Store NearState) (p : Layout) := recordStore (committed cfg s p) cfg.regularOpCost p.memoryIndex (committedMemory p) p.record (header p)

attribute [local irreducible] grownPhase pageChecked converted committed after

private theorem grownPhase_gas (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    GasCost s (grownPhase cfg s p) (47*cfg.regularOpCost+memoryGrowCost cfg (delta p)) := by
  simpa only [grownPhase,delta] using growthAfter_gas cfg s p.memoryIndex p.grown (requested p)
private theorem pageChecked_gas (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    GasCost s (pageChecked cfg s p) (53*cfg.regularOpCost+memoryGrowCost cfg (delta p)) := by
  have h := (grownPhase_gas cfg s p).trans (GasCost.of_units (gasUnits_paid (grownPhase cfg s p) cfg.regularOpCost 6))
  have c : (47*cfg.regularOpCost+memoryGrowCost cfg (delta p))+6*cfg.regularOpCost=53*cfg.regularOpCost+memoryGrowCost cfg (delta p) := by omega
  simpa only [c,pageChecked] using h
private theorem converted_gas (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    GasCost s (converted cfg s p) (91*cfg.regularOpCost+memoryGrowCost cfg (delta p)) := by
  have h := (pageChecked_gas cfg s p).trans (GasCost.of_units (bytesAfter_gas (pageChecked cfg s p) cfg.regularOpCost))
  have c : (53*cfg.regularOpCost+memoryGrowCost cfg (delta p))+38*cfg.regularOpCost=91*cfg.regularOpCost+memoryGrowCost cfg (delta p) := by omega
  simpa only [c,converted] using h
private theorem grownPhase_fields (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    (grownPhase cfg s p).funcs=s.funcs ∧ (grownPhase cfg s p).modules=s.modules ∧
    (grownPhase cfg s p).mems=s.mems.set! p.memoryIndex p.grown := by
  have h := growthAfter_fields cfg s p.memoryIndex p.grown (requested p)
  simpa only [grownPhase] using (show (growthAfter cfg s p.memoryIndex p.grown (requested p)).funcs=s.funcs ∧ (growthAfter cfg s p.memoryIndex p.grown (requested p)).modules=s.modules ∧ (growthAfter cfg s p.memoryIndex p.grown (requested p)).mems=s.mems.set! p.memoryIndex p.grown from ⟨h.1,h.2.1,h.2.2.1⟩)
private def view (s : Store NearState) := (s.funcs,s.modules,s.mems)
private theorem view_paid (s : Store NearState) (op n : Nat) : view (paid s op n)=view s := by
  induction n with | zero => rfl | succ n ih => simpa only [paid,view,chargedStore] using ih
private theorem view_charge (s : Store NearState) (cost : Nat) : view (chargedStore s cost)=view s := by simp only [view,chargedStore]
private theorem view_bytes (s : Store NearState) (op : Nat) : view (bytesAfter s op)=view s := by
  simp only [bytesAfter,after573,AllocateUnits.minimumAfter,AllocateUnits.entered9,view_paid,view_charge]
private theorem converted_fields (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    (converted cfg s p).funcs=s.funcs ∧ (converted cfg s p).modules=s.modules ∧
    (converted cfg s p).mems=s.mems.set! p.memoryIndex p.grown := by
  have h : view (converted cfg s p)=view (grownPhase cfg s p)  := by
    simpa only [converted,pageChecked] using (view_bytes (paid (grownPhase cfg s p) cfg.regularOpCost 6) cfg.regularOpCost).trans (view_paid (grownPhase cfg s p) cfg.regularOpCost 6)
  simp only [view,Prod.mk.injEq] at h
  have g := grownPhase_fields cfg s p
  exact ⟨h.1.trans g.1,h.2.1.trans g.2.1,h.2.2.trans g.2.2⟩
private theorem converted_memory (cfg : WasmConfig) (s : Store NearState) (p : Layout) (hm : s.mems[p.memoryIndex]?=some p.memory) :
    (converted cfg s p).mems[p.memoryIndex]?=some p.grown := by
  rw [(converted_fields cfg s p).2.2]
  have hi := (Array.getElem?_eq_some_iff.mp hm).1
  simp [hi]

theorem wp_success (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame caller : CallFrame) (callers : List CallFrame)
    (p : Layout) (post : Post) (hn : Native p) (hcode : Code s frame.inst p)
    (h0 : frame.locals[0]?=some (.i32 p.record))
    (h3 : frame.locals[3]?=some (.i32 (requested p))) (hs : 5≤frame.locals.size)
    (ha : frame.arity=0) (hh : frame.height=base.length) (hm : s.mems[p.memoryIndex]?=some p.memory)
    (hd : callers.length+3<limits.maxCallDepth)
    (hc : s.host.gas.Credits (116*cfg.regularOpCost+memoryGrowCost cfg (delta p)+rest))
    (hnext : WP cfg fuel (.next (atCode (after cfg s p) limits base.toArray caller callers caller.code)) rest post) :
    WP cfg (fuel+89) (.next (atCode s limits base.toArray frame (caller::callers) (WNear.Binary.AllocateGrowth.growthBlock++WNear.Binary.AllocateGrowth.recordReturn)))
      (116*cfg.regularOpCost+memoryGrowCost cfg (delta p)+rest) post := by
  let op := cfg.regularOpCost
  let fee := memoryGrowCost cfg (delta p)
  let sf := frame
  let bf := emptyBlockFrame sf base.length WNear.Binary.AllocateGrowth.recordReturn
  let gf := growthFrame bf (requested p) p.memory
  let cf := bytesFrame gf (delta p)
  let af := bytesFrame (growthFrame sf (requested p) p.memory) (delta p)
  have htwo : 2<frame.locals.size := by omega
  have hthree : 3<frame.locals.size := by omega
  have hfour : 4<frame.locals.size := by omega
  have grownSpec := hn.grown_spec p
  have freshSpec := freshMemory_spec p.grown (header p) (blockBytes p) grownSpec.1 grownSpec.2.2.1
  have cs := hc
  have cg : (grownPhase cfg s p).host.gas.Credits (69*op+rest) :=
    (grownPhase_gas cfg s p).credits (hc.mono (by dsimp [op,fee];omega))
  have cp : (pageChecked cfg s p).host.gas.Credits (63*op+rest) :=
    (pageChecked_gas cfg s p).credits (hc.mono (by dsimp [op,fee];omega))
  have cc : (converted cfg s p).host.gas.Credits (25*op+rest) :=
    (converted_gas cfg s p).credits (hc.mono (by dsimp [op,fee];omega))
  have scode := hcode
  have gcode := hcode.transport s (grownPhase cfg s p) frame.inst p (grownPhase_fields cfg s p).1 (grownPhase_fields cfg s p).2.1
  have ccode := hcode.transport s (converted cfg s p) frame.inst p (converted_fields cfg s p).1 (converted_fields cfg s p).2.1
  have memS := hm
  have memC := converted_memory cfg s p hm
  have cf2 : cf.locals[2]?=some (.i32 (oldPages p)) := by simp [cf,gf,bytesFrame,growthFrame,pagesFrame,bf,sf,emptyBlockFrame,htwo,oldPages]
  have cf4 : cf.locals[4]?=some (.i32 (blockBytes p)) := by simp [cf,bytesFrame,gf,growthFrame,pagesFrame,bf,sf,emptyBlockFrame,hfour,blockBytes]
  have cfs : 5≤cf.locals.size := by simpa [cf,bytesFrame,gf,growthFrame,pagesFrame,bf,sf,emptyBlockFrame] using hs
  have cfInst : cf.inst=frame.inst := by simp only [cf,bytesFrame,gf,growthFrame,pagesFrame,bf,sf,emptyBlockFrame]
  have freshModule : (converted cfg s p).modules[cf.inst]?=some p.mi := by rw [cfInst];exact ccode.module
  have af0 : af.locals[0]?=some (.i32 p.record) := by simpa [af,bytesFrame,growthFrame,pagesFrame,sf] using h0
  have af2 : af.locals[2]?=some (.i32 (oldPages p)) := by simpa only [cf,af,gf,bf,bytesFrame,growthFrame,pagesFrame,emptyBlockFrame] using cf2
  have af4 : af.locals[4]?=some (.i32 (blockBytes p)) := by simpa only [cf,af,gf,bf,bytesFrame,growthFrame,pagesFrame,emptyBlockFrame] using cf4
  have afs : 5≤af.locals.size := by simpa only [cf,af,gf,bf,bytesFrame,growthFrame,pagesFrame,emptyBlockFrame] using cfs
  have afInst : af.inst=frame.inst := by simp only [af,bytesFrame,growthFrame,pagesFrame,sf]
  have afArity : af.arity=0 := by simpa only [af,bytesFrame,growthFrame,pagesFrame,sf] using ha
  have afHeight : af.height=base.length := by simpa only [af,bytesFrame,growthFrame,pagesFrame,sf] using hh
  have moduleAf : (converted cfg s p).modules[af.inst]?=some p.mi := by rw [afInst];exact ccode.module
  have finishNext : WP cfg fuel (.next (atCode (finishStore (converted cfg s p) op p.memoryIndex p.grown p.record (oldPages p) (blockBytes p)) limits base.toArray caller callers caller.code)) rest post := by
    simpa only [finishStore,after,committed,committedMemory,header,op] using hnext
  have finish := wp_finish cfg fuel rest (converted cfg s p) limits base af caller callers p.record (oldPages p) (blockBytes p) p.mi p.memoryIndex p.grown post
    af0 af2 af4 afs afArity afHeight moduleAf ccode.memoryIndex memC grownSpec.1 grownSpec.2.2.1 grownSpec.2.2.2 cc finishNext
  have bytesNext : WP cfg (fuel+26) (.next (atCode (bytesAfter (pageChecked cfg s p) op) limits base.toArray (bytesFrame gf (delta p)) (caller::callers) WNear.Binary.AllocateGrowth.freshHeader)) (25*op+rest) post := by
    simpa only [converted,cf,af,gf,bf,bytesFrame,growthFrame,pagesFrame,emptyBlockFrame,op] using finish
  have gf3 : gf.locals[3]?=some (.i32 (delta p)) := by simp [gf,growthFrame,pagesFrame,bf,sf,emptyBlockFrame,hthree,delta]
  have codeP : Code (pageChecked cfg s p) frame.inst p := by
    exact gcode.transport _ _ frame.inst p (by simp only [pageChecked,paid,chargedStore]) (by simp only [pageChecked,paid,chargedStore])
  have gfInst : gf.inst=frame.inst := by simp only [gf,growthFrame,pagesFrame,bf,sf,emptyBlockFrame]
  have pc : Code (pageChecked cfg s p) gf.inst p := by rw [gfInst];exact codeP
  have bytes := wp_bytes_minimum cfg (fuel+26) (25*op+rest) (pageChecked cfg s p) limits base gf (caller::callers) WNear.Binary.AllocateGrowth.freshHeader
    (delta p) p.mi p.address573 p.address574 post gf3 pc.module pc.index573 pc.function573 pc.index574 pc.function574
    hn.pagesBound hn.pagesPositive (by simp only [List.length_cons];omega) (cp.mono (by dsimp [op];omega)) bytesNext
  have guardNext : WP cfg (fuel+49) (.next (atCode (paid (grownPhase cfg s p) op 6) limits base.toArray gf (caller::callers)
      (WNear.Binary.AllocateGrowth.bytesAndMinimum++WNear.Binary.AllocateGrowth.freshHeader))) (63*op+rest) post := by
    have cost : 38*cfg.regularOpCost+(25*op+rest)=63*op+rest := by dsimp [op];omega
    simpa only [pageChecked,cost,Nat.add_assoc,Nat.reduceAdd] using bytes
  have gf2 : gf.locals[2]?=some (.i32 (oldPages p)) := by simp [gf,growthFrame,pagesFrame,bf,sf,emptyBlockFrame,htwo,oldPages]
  have oldNat : (oldPages p).toNat=p.memory.size := by simp only [oldPages];apply Nat.mod_eq_of_lt;have:=hn.oldPagesBound;omega
  have oldBound : (oldPages p).toNat<65536 := by rw [oldNat];exact hn.oldPagesBound
  have guard := wp_old_pages_guard cfg (fuel+49) (63*op+rest) (grownPhase cfg s p) limits base.toArray gf (caller::callers)
    (WNear.Binary.AllocateGrowth.bytesAndMinimum++WNear.Binary.AllocateGrowth.freshHeader) (oldPages p) post gf2 oldBound (cg.mono (by dsimp [op];omega)) guardNext
  have attemptNext : WP cfg (fuel+55) (.next (atCode (growthAfter cfg s p.memoryIndex p.grown (requested p)) limits base.toArray gf (caller::callers)
      (WNear.Binary.AllocateGrowth.oldPagesGuard++WNear.Binary.AllocateGrowth.bytesAndMinimum++WNear.Binary.AllocateGrowth.freshHeader))) (69*op+rest) post := by
    have cost : 6*cfg.regularOpCost+(63*op+rest)=69*op+rest := by dsimp [op];omega
    simpa only [grownPhase,cost,List.append_assoc,Nat.add_assoc,Nat.reduceAdd] using guard
  have sf3 : sf.locals[3]?=some (.i32 (requested p)) := h3
  have sfs : 4≤sf.locals.size := by dsimp only [sf];omega
  have hold : UInt32.ofNat p.memory.size≠4294967295 := by intro h;have q:=congrArg UInt32.toNat h;change (oldPages p).toNat=4294967295 at q;omega
  have bfInst : bf.inst=frame.inst := by simp only [bf,sf,emptyBlockFrame]
  have bc : Code s bf.inst p := by rw [bfInst];exact scode
  have bf3 : bf.locals[3]?=some (.i32 (requested p)) := by simpa only [bf,emptyBlockFrame] using sf3
  have bfs : 4≤bf.locals.size := by simpa only [bf,emptyBlockFrame] using sfs
  have attempt := wp_grow_attempt cfg (fuel+55) (69*op+rest) s limits base bf (caller::callers)
    (WNear.Binary.AllocateGrowth.oldPagesGuard++WNear.Binary.AllocateGrowth.bytesAndMinimum++WNear.Binary.AllocateGrowth.freshHeader) (requested p) p.mi p.address568 p.address569 p.memoryIndex p.memory p.grown post
    bf3 bfs bc.module bc.memoryIndex memS bc.index568 bc.function568 bc.index569 bc.function569 hn.roundBound hold hn.grow
    (by simp only [List.length_cons];omega) (cs.mono (by dsimp [op,fee,delta];omega)) attemptNext
  have growthNext : WP cfg (fuel+88) (.next (atCode s limits base.toArray bf (caller::callers)
      ([.block .empty (WNear.Binary.AllocateGrowth.growAttempt++WNear.Binary.AllocateGrowth.growFailed)]++WNear.Binary.AllocateGrowth.oldPagesGuard++WNear.Binary.AllocateGrowth.bytesAndMinimum++WNear.Binary.AllocateGrowth.freshHeader)))
      (116*op+fee+rest) post := by
    have cost : 47*cfg.regularOpCost+memoryGrowCost cfg (growPages (requested p))+(69*op+rest)=116*op+fee+rest := by dsimp [op,fee,delta];omega
    simpa only [cost,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd] using attempt
  have growth := wp_block_empty cfg (fuel+88) (116*op+fee+rest) s limits base.toArray sf (caller::callers) _ WNear.Binary.AllocateGrowth.recordReturn post cs
    (by simpa only [bf,List.size_toArray] using growthNext)
  simpa only [WNear.Binary.AllocateGrowth.growthBlock,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd,op,fee] using growth
end WNear.Proofs.AllocateGrowth.Success
