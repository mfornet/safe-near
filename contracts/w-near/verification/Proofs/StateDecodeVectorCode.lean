import Proofs.StateDecodeVectorState
import Proofs.StateDecodeRawCode

/-! Original installed code for373, transported only through its real scalar prefix. -/
namespace WNear.Proofs.StateDecodeVector
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)

structure Code (s:Store NearState) (inst:Nat) (p:Layout) (address581 address236:Nat) : Prop where
  raw : StateDecodeRaw.Code s inst p.toRaw address581 address236
  index767 : p.mi.funcAddrs[767]?=some p.address767
  function767 : s.funcs[p.address767]?=some (.wasm WNear.Binary.StateDecodeRaw.signature inst WNear.Binary.StateDecodeRaw.function767)

private theorem raw_transport (s t:Store NearState) (inst:Nat) (p:StateDecodeRaw.Layout) (a b:Nat)
    (hc:StateDecodeRaw.Code s inst p a b) (hf:t.funcs=s.funcs) (hm:t.modules=s.modules) (ht:t.tables=s.tables) :
    StateDecodeRaw.Code t inst p a b := by
  refine {hc with record:=?_,function751:=?_,function752:=?_,function769:=?_,function770:=?_}
  · have allocation:=hc.record.allocation.transport s t inst p.toPositive hf hm ht
    refine {hc.record with allocation:=allocation,function581:=?_,function236:=?_,function310:=?_}
    · rw[hf];exact hc.record.function581
    · rw[hf];exact hc.record.function236
    · rw[hf];exact hc.record.function310
  · rw[hf];exact hc.function751
  · rw[hf];exact hc.function752
  · rw[hf];exact hc.function769
  · rw[hf];exact hc.function770

private theorem paid_funcs (s:Store NearState) (op n:Nat) : (paid s op n).funcs=s.funcs:=by
  induction n with |zero=>rfl|succ n ih=>exact ih
private theorem paid_modules (s:Store NearState) (op n:Nat) : (paid s op n).modules=s.modules:=by
  induction n with |zero=>rfl|succ n ih=>exact ih
private theorem paid_tables (s:Store NearState) (op n:Nat) : (paid s op n).tables=s.tables:=by
  induction n with |zero=>rfl|succ n ih=>exact ih
private theorem global_funcs (s:Store NearState) (i:Nat) (v:Value) : (setGlobal s i v).funcs=s.funcs:=rfl
private theorem global_modules (s:Store NearState) (i:Nat) (v:Value) : (setGlobal s i v).modules=s.modules:=rfl
private theorem global_tables (s:Store NearState) (i:Nat) (v:Value) : (setGlobal s i v).tables=s.tables:=rfl

theorem arguments_raw_code (s:Store NearState) (op inst:Nat) (p:Layout) (a b:Nat) (hc:Code s inst p a b) :
    StateDecodeRaw.Code (arguments s op p) inst p.toRaw a b := by
  apply raw_transport s _ inst p.toRaw a b hc.raw
  · simp only[arguments,reserved,paid_funcs,global_funcs]
  · simp only[arguments,reserved,paid_modules,global_modules]
  · simp only[arguments,reserved,paid_tables,global_tables]
end WNear.Proofs.StateDecodeVector
