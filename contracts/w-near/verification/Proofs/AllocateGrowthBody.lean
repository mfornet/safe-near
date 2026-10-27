import Proofs.AllocateGrowthSuccess
import Proofs.AllocateGrowthBlocks

/-! Full actual successful f577 body: original scalar preparation and sizing,
then the separately verified growth and sequential commit suffix. -/
namespace WNear.Proofs.AllocateGrowth
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] WP atCode prepared sized after Success.after memoryGrowCost growPages
set_option maxRecDepth 16384

theorem wp_body (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame caller : CallFrame) (callers : List CallFrame)
    (code : Expr) (p : Layout) (post : Post) (hn : Native p) (hcode : Code s frame.inst p)
    (h0 : frame.locals[0]?=some (.i32 p.record)) (h2 : frame.locals[2]?=some (.i32 p.words))
    (h3 : frame.locals[3]?=some (.i32 p.alignment)) (hs : 5≤frame.locals.size)
    (ha : frame.arity=0) (hh : frame.height=base.length) (hm : s.mems[p.memoryIndex]?=some p.memory)
    (hd : callers.length+3<limits.maxCallDepth)
    (hc : s.host.gas.Credits (166*cfg.regularOpCost+memoryGrowCost cfg (delta p)+rest))
    (hnext : WP cfg fuel (.next (atCode (after cfg s p) limits base.toArray caller callers caller.code)) rest post) :
    WP cfg (fuel+136) (.next (atCode s limits base.toArray frame (caller::callers) (WNear.Binary.AllocateGrowth.body++code)))
      (166*cfg.regularOpCost+memoryGrowCost cfg (delta p)+rest) post := by
  let op := cfg.regularOpCost
  let fee := memoryGrowCost cfg (delta p)
  let pf := preparedFrame frame p.words
  let ef := errorFrame pf base.length code
  let sf := sizingFrame ef (units p) p.alignment
  have hthree : 3<frame.locals.size := by omega
  have hfour : 4<frame.locals.size := by omega
  have cs : (sized s op).host.gas.Credits (116*op+fee+rest) :=
    (sized_gas s op) (116*op+fee+rest) (hc.mono (by dsimp [op,fee];omega)) |>.2.2
  have fields := sized_fields s op
  have scode := hcode.transport s (sized s op) frame.inst p fields.1 fields.2.1
  have sfInst : sf.inst=frame.inst := by simp only [sf,sizingFrame,chosenFrame,scaledFrame,alignFrame,ef,errorFrame,pf,preparedFrame,emptyBlockFrame]
  have codeSf : Code (sized s op) sf.inst p := by rw [sfInst];exact scode
  have memS : (sized s op).mems[p.memoryIndex]?=some p.memory := by rw [fields.2.2.1];exact hm
  have sf0 : sf.locals[0]?=some (.i32 p.record) := by simpa [sf,sizingFrame,chosenFrame,scaledFrame,alignFrame,ef,errorFrame,pf,preparedFrame,emptyBlockFrame] using h0
  have sf3 : sf.locals[3]?=some (.i32 (requested p)) := by simp [sf,sizingFrame,chosenFrame,scaledFrame,alignFrame,ef,errorFrame,pf,preparedFrame,emptyBlockFrame,hthree,requested]
  have sfs : 5≤sf.locals.size := by simpa [sf,sizingFrame,chosenFrame,scaledFrame,alignFrame,ef,errorFrame,pf,preparedFrame,emptyBlockFrame] using hs
  have sfArity : sf.arity=0 := by simpa only [sf,sizingFrame,chosenFrame,scaledFrame,alignFrame,ef,errorFrame,pf,preparedFrame,emptyBlockFrame] using ha
  have sfHeight : sf.height=base.length := by simpa only [sf,sizingFrame,chosenFrame,scaledFrame,alignFrame,ef,errorFrame,pf,preparedFrame,emptyBlockFrame] using hh
  have successNext : WP cfg fuel (.next (atCode (Success.after cfg (sized s op) p) limits base.toArray caller callers caller.code)) rest post := by
    simpa only [Success.after,Success.committed,Success.converted,Success.pageChecked,Success.grownPhase,
      after,committed,converted,pageChecked,grownPhase,op] using hnext
  have success := Success.wp_success cfg fuel rest (sized s op) limits base sf caller callers p post hn codeSf sf0 sf3 sfs sfArity sfHeight memS hd cs successNext
  have sizingNext : WP cfg (fuel+89) (.next (atCode (StorePairCaller.paid (prepared s op) op 29) limits base.toArray sf (caller::callers)
      (WNear.Binary.AllocateGrowth.growthBlock++WNear.Binary.AllocateGrowth.recordReturn))) (116*op+fee+rest) post := by
    simpa only [sized,op,fee] using success
  have pcredit := (prepared_gas s op) (145*op+fee+rest) (hc.mono (by dsimp [op,fee];omega)) |>.2.2
  have ef3 : ef.locals[3]?=some (.i32 p.alignment) := by simpa [ef,errorFrame,pf,preparedFrame,emptyBlockFrame] using h3
  have ef4 : ef.locals[4]?=some (.i32 (units p)) := by simp [ef,errorFrame,pf,preparedFrame,emptyBlockFrame,hfour,units]
  have efs : 5≤ef.locals.size := by simpa [ef,errorFrame,pf,preparedFrame,emptyBlockFrame] using hs
  have sizeProof := wp_sizing cfg (fuel+89) (116*op+fee+rest) (prepared s op) limits base.toArray ef (caller::callers)
    (WNear.Binary.AllocateGrowth.growthBlock++WNear.Binary.AllocateGrowth.recordReturn) (units p) p.alignment post ef3 ef4 efs hn.alignAdd hn.alignMask hn.padAdd
    (pcredit.mono (by dsimp [op];omega)) sizingNext
  have errorNext : WP cfg (fuel+118) (.next (atCode (prepared s op) limits base.toArray ef (caller::callers) WNear.Binary.AllocateGrowth.accepted)) (145*op+fee+rest) post := by
    have cost : 29*cfg.regularOpCost+(116*op+fee+rest)=145*op+fee+rest := by dsimp [op];omega
    rw [cost] at sizeProof
    simpa only [WNear.Binary.AllocateGrowth.accepted,List.append_assoc,Nat.add_assoc,Nat.reduceAdd] using sizeProof
  have blocks := wp_error_blocks cfg (fuel+118) (145*op+fee+rest) (prepared s op) limits base.toArray pf (caller::callers) code post pcredit
    (by simpa only [ef,List.size_toArray] using errorNext)
  have prepNext : WP cfg (fuel+122) (.next (atCode (prepared s op) limits base.toArray pf (caller::callers) (errorBlocks++code))) (145*op+fee+rest) post := by
    simpa only [Nat.add_assoc,Nat.reduceAdd] using blocks
  have prep := wp_preparation cfg (fuel+122) (145*op+fee+rest) s limits base frame (caller::callers) (errorBlocks++code) p.words p.mi p.address572 post
    h2 hcode.module hcode.index572 hcode.function572 hn.wordsBound (by simp only [List.length_cons];omega) (hc.mono (by dsimp [op,fee];omega)) prepNext
  have cost : 21*cfg.regularOpCost+(145*op+fee+rest)=166*cfg.regularOpCost+memoryGrowCost cfg (delta p)+rest := by dsimp [op,fee];omega
  rw [cost] at prep
  simpa only [WNear.Binary.AllocateGrowth.body,errorBlocks,List.append_assoc,Nat.add_assoc,Nat.reduceAdd] using prep
end WNear.Proofs.AllocateGrowth
