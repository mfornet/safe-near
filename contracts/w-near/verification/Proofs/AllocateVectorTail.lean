import Proofs.AllocateVectorSteps
import Proofs.InterfaceStack
import Proofs.ValueReturnLazyReturn

/-! The686 cached-word output and explicit return use no output alias premise. -/
namespace WNear.Proofs.AllocateVector
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode recordStore

def finished (s : Store NearState) (op index globalIndex : Nat) (memory : Memory)
    (out pointer size scratch : UInt32) :=
  chargedStore (setGlobal (paid (recordStore s op index memory out pointer size) op 4) globalIndex (.i32 (scratch+32))) op

theorem wp_tail (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame caller : CallFrame) (callers : List CallFrame)
    (code : Expr) (mi : ModuleInst) (index globalIndex : Nat) (global : GlobalInst)
    (memory : Memory) (out pointer size scratch : UInt32) (post : Post)
    (h0 : frame.locals[0]?=some (.i32 out)) (h2 : frame.locals[2]?=some (.i32 pointer))
    (h5 : frame.locals[5]?=some (.i32 size)) (h3 : frame.locals[3]?=some (.i32 scratch))
    (hm : s.modules[frame.inst]?=some mi) (hi : mi.memAddrs[0]?=some index)
    (hmem : s.mems[index]?=some memory) (hgi : mi.globalAddrs[0]?=some globalIndex)
    (hg : s.globals[globalIndex]?=some global) (hw : memory.wf) (hb : out.toNat+8≤memory.byteSize)
    (ha : frame.arity=0) (hh : frame.height=base.length)
    (hc : s.host.gas.Credits (11*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (finished s cfg.regularOpCost index globalIndex memory out pointer size scratch)
      limits base.toArray caller callers caller.code)) rest post) :
    WP cfg (fuel+11) (.next (atCode s limits base.toArray frame (caller::callers)
      (WNear.Binary.AllocateVector.record++WNear.Binary.AllocateVector.restore++(.return::code))))
      (11*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  let written := recordStore s op index memory out pointer size
  let rs := setGlobal (paid written op 4) globalIndex (.i32 (scratch+32))
  have cr : written.host.gas.Credits (5*op+rest) := by
    simpa only [written,recordStore,storeI32_host] using paid_credits (storeI32 (paid s op 3) index out.toNat memory pointer) op 3 (5*op+rest)
      (paid_credits s op 3 _ (hc.mono (by dsimp [op];omega)))
  have ret := ValueReturnLazyLookup.wp_return_wasm cfg fuel rest rs limits base [] frame caller callers code post
    (by simpa only [List.length_nil] using ha.symm) hh
    (paid_credits written op 4 _ (cr.mono (by dsimp [op];omega))) (by simpa only [finished,rs,written,op,List.append_nil] using hnext)
  have mr : written.modules[frame.inst]?=some mi := by simpa only [written,recordStore,storeI32_modules,paid,chargedStore] using hm
  have gr : written.globals[globalIndex]?=some global := by simpa only [written,recordStore,storeI32_globals,paid,chargedStore] using hg
  have rn : WP cfg (fuel+1) (.next (atCode (setGlobal (paid written op 4) globalIndex (.i32 (scratch+32))) limits
      base.toArray frame (caller::callers) (.return::code))) (op+rest) post := by
    simpa only [rs,List.append_nil] using ret
  have restore := InterfaceStack.wp_restore cfg (fuel+1) (op+rest) written limits base.toArray frame (caller::callers)
    (.return::code) mi globalIndex global scratch 3 32 post h3 mr hgi gr (cr.mono (by dsimp [op];omega)) rn
  have restoreN : WP cfg ((fuel+1)+4) (.next (atCode written limits base.toArray frame (caller::callers)
      (WNear.Binary.AllocateVector.restore++(.return::code)))) (5*op+rest) post := by
    simpa only [WNear.Binary.AllocateVector.restore,show 4*cfg.regularOpCost+(op+rest)=5*op+rest by dsimp [op];omega] using restore
  have record := wp_record cfg ((fuel+1)+4) (5*op+rest) s limits base.toArray frame (caller::callers)
    (WNear.Binary.AllocateVector.restore++(.return::code)) mi index memory out pointer size post h0 h2 h5 hm hi hmem hw hb
    (hc.mono (by dsimp [op];omega)) restoreN
  have ce : 6*cfg.regularOpCost+(5*op+rest)=11*cfg.regularOpCost+rest := by dsimp [op];omega
  rw [ce] at record
  simpa only [List.append_assoc,Nat.add_assoc,Nat.reduceAdd] using record
end WNear.Proofs.AllocateVector
