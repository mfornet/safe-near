import Proofs.StateDecodeScalarLocals
import Proofs.StateDecodeScalarPrefix
import Proofs.StateDecodeScalarOutputFrame
import Proofs.StateDecodeScalarFinalMemory
import Proofs.ValueReturnLazyReturn

/-! The actual accepted output tail includes the normal middle-block exit and
an explicit Wasm return; output and source descriptors may alias. -/
namespace WNear.Proofs.StateDecodeScalar
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode values updated restored after dropCached dropped valuesMemory updatedMemory finalMemory
private theorem modules_paid (s : Store NearState) (op n : Nat) : (paid s op n).modules=s.modules := by
  induction n with |zero=>rfl|succ n ih=>exact ih
private theorem mems_paid (s : Store NearState) (op n : Nat) : (paid s op n).mems=s.mems := by
  induction n with |zero=>rfl|succ n ih=>exact ih

/-- From already cached words, execute the two output writes (one for u64),
update the original slice, leave the middle block, restore SP and return. -/
theorem wp_output_tail (wide : Bool) (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame caller : CallFrame) (callers : List CallFrame)
    (p : Layout) (post : Post) (hn : Native wide p) (hcode : Code wide s frame.inst p)
    (hm : s.mems[p.memoryIndex]?=some p.memory) (hg : s.globals[p.globalIndex]?=some p.global)
    (h0 : frame.locals[0]?=some (.i32 p.out)) (h1 : frame.locals[1]?=some (.i32 p.slice))
    (h2 : frame.locals[2]?=some (.i32 (scratch p)))
    (h4 : frame.locals[4]?=some (.i64 (if wide then highValue p else lowValue wide p)))
    (h5 : wide=true→frame.locals[5]?=some (.i64 (lowValue wide p)))
    (hp : frame.locals[if wide then 6 else 5]?=some (.i64 (dropValue wide p)))
    (hs : 3≤frame.locals.size) (ha : frame.arity=0) (hh : frame.height=base.length)
    (hc : s.host.gas.Credits (bodyCost wide*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (after wide cfg s p) limits base.toArray caller callers caller.code)) rest post) :
    WP cfg (fuel+(if wide then 24 else 19)) (.next (atCode (dropCached wide cfg s p) limits base.toArray
      (emptyBlockFrame frame base.length WNear.Binary.StateDecodeScalar.finish) (caller::callers)
      (WNear.Binary.StateDecodeScalar.outputValues wide++WNear.Binary.StateDecodeScalar.updateSlice wide)))
      ((if wide then 23 else 18)*cfg.regularOpCost+rest) post := by
  let op:=cfg.regularOpCost
  let f:=emptyBlockFrame frame base.length WNear.Binary.StateDecodeScalar.finish
  let z:=zeroFrame frame
  have dc:=Code.dropped wide cfg s frame.inst p hcode
  have dm : (dropCached wide cfg s p).modules[frame.inst]?=some p.mi := by
    rw [dropCached,modules_paid];exact dc.module
  have mem : (dropCached wide cfg s p).mems[p.memoryIndex]?=some (droppedMemory wide p) := by
    rw [dropCached,mems_paid];exact dropped_memory wide cfg s p hm
  have vm : (values wide cfg s p).modules[frame.inst]?=some p.mi := by
    rw [(values_stage_fields wide cfg s p).2.1];exact dm
  have um : (updated wide cfg s p).modules[frame.inst]?=some p.mi := by
    rw [(updated_stage_fields wide cfg s p).2.1];exact vm
  have zl:=zero_locals frame p.out (scratch p) hs h0 h2
  have cr:=restored_credits wide cfg s p (op+rest) (hc.mono (by cases wide <;> simp only [bodyCost,ite_true,Bool.false_eq_true,ite_false] <;> dsimp[op] <;> omega))
  have ret:=ValueReturnLazyLookup.wp_return_wasm cfg fuel rest (restored wide cfg s p) limits base [] z caller callers [] post
    (by simpa only [z,zeroFrame,List.length_nil] using ha.symm) (by simpa only [z,zeroFrame] using hh) cr
    (by simpa only [after,List.append_nil] using hnext)
  have finish:=wp_finish_prefix cfg (fuel+1) (op+rest) (updated wide cfg s p) limits base.toArray z (caller::callers) []
    p.out (scratch p) p.mi p.memoryIndex p.globalIndex (updatedMemory wide p)
    {p.global with value:=.i32 (scratch p)} post zl.1 zl.2.1 zl.2.2.1 um hcode.memoryIndex hcode.globalIndex
    (updated_memory wide cfg s p hm) (updated_global wide cfg s p hg)
    (by rw [(updatedMemory_spec wide p hn).2.1];have hb:=hn.outBound;cases wide <;> simp only [ite_true,Bool.false_eq_true,ite_false] at hb <;> omega)
    (updated_credits wide cfg s p (7*op+(op+rest)) (hc.mono (by cases wide <;> simp only [bodyCost,ite_true,Bool.false_eq_true,ite_false] <;> dsimp[op] <;> omega)))
    (by simpa only [restored,z,op,List.nil_append,List.append_nil] using ret)
  have endLabel:=wp_end_label cfg (fuel+8) (8*op+rest) (updated wide cfg s p) limits base.toArray z (caller::callers)
    {arity:=0,height:=base.length,rest:=WNear.Binary.StateDecodeScalar.finish,loop:=none} post
    (updated_credits wide cfg s p _ (hc.mono (by cases wide <;> simp only [bodyCost,ite_true,Bool.false_eq_true,ite_false] <;> dsimp[op] <;> omega)))
    (by simpa only [List.append_nil,Nat.add_assoc,Nat.reduceAdd,show 7*cfg.regularOpCost+(op+rest)=8*op+rest by dsimp[op];omega] using finish)
  have upd:=wp_update_slice cfg (fuel+9) (8*op+rest) (values wide cfg s p) limits base.toArray f (caller::callers) [] wide
    p.slice (dropValue wide p) p.mi p.memoryIndex (valuesMemory wide p) post h1 hp vm hcode.memoryIndex
    (values_memory wide cfg s p hm) (by rw [(valuesMemory_spec wide p hn).2.1];exact hn.sliceBound)
    (values_credits wide cfg s p _ (hc.mono (by cases wide <;> simp only [bodyCost,ite_true,Bool.false_eq_true,ite_false] <;> dsimp[op] <;> omega)))
    (by simpa only [updated,z,f,zeroFrame,emptyBlockFrame] using endLabel)
  have upd' : WP cfg (fuel+14) (.next (atCode (values wide cfg s p) limits base.toArray f (caller::callers)
      (WNear.Binary.StateDecodeScalar.updateSlice wide))) (13*op+rest) post := by
    simpa only [List.append_nil,Nat.add_assoc,Nat.reduceAdd,show 5*cfg.regularOpCost+(8*op+rest)=13*op+rest by dsimp[op];omega] using upd
  have shape:=droppedMemory_spec wide p hn
  have address:=output_addresses wide p hn
  have hb:=hn.outBound
  cases wide with
  | true=>
    have output:=wp_output_wide cfg (fuel+14) (13*op+rest) (dropCached true cfg s p) limits base.toArray f (caller::callers)
      (WNear.Binary.StateDecodeScalar.updateSlice true) p.out (highValue p) (lowValue true p) p.mi p.memoryIndex (droppedMemory true p) post
      h0 h4 (h5 rfl) dm hcode.memoryIndex mem shape.1
      (by rw [shape.2.1,address.2 rfl];simp only [ite_true] at hb;omega)
      (by rw [shape.2.1,address.1];simp only [ite_true] at hb;omega)
      (dropCached_credits true cfg s p _ (hc.mono (by simp only [bodyCost,ite_true];dsimp[op];omega)))
      (by simpa only [values,ite_true] using upd')
    simpa only [ite_true,Nat.add_assoc,Nat.reduceAdd,show 10*cfg.regularOpCost+(13*op+rest)=23*cfg.regularOpCost+rest by dsimp[op];omega] using output
  | false=>
    have output:=wp_output_narrow cfg (fuel+14) (13*op+rest) (dropCached false cfg s p) limits base.toArray f (caller::callers)
      (WNear.Binary.StateDecodeScalar.updateSlice false) p.out (lowValue false p) (lowValue false p) p.mi p.memoryIndex (droppedMemory false p) post
      h0 h4 dm hcode.memoryIndex mem
      (by rw [shape.2.1,address.1];simp only [Bool.false_eq_true,ite_false] at hb;omega)
      (dropCached_credits false cfg s p _ (hc.mono (by simp only [bodyCost,Bool.false_eq_true,ite_false];dsimp[op];omega)))
      (by simpa only [values,Bool.false_eq_true,ite_false] using upd')
    simpa only [Bool.false_eq_true,ite_false,Nat.add_assoc,Nat.reduceAdd,show 5*cfg.regularOpCost+(13*op+rest)=18*cfg.regularOpCost+rest by dsimp[op];omega] using output
end WNear.Proofs.StateDecodeScalar
