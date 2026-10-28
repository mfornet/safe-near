import Proofs.StateDecodeVectorCopyState

namespace WNear.Proofs.StateDecodeVectorCopy
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
private theorem paid_funcs (s:Store NearState)(op n:Nat):(paid s op n).funcs=s.funcs:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem paid_modules (s:Store NearState)(op n:Nat):(paid s op n).modules=s.modules:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem paid_tables (s:Store NearState)(op n:Nat):(paid s op n).tables=s.tables:=by
  induction n with|zero=>rfl|succ n ih=>exact ih

theorem vector_code (s:Store NearState)(op inst:Nat)(p:Layout)(a b:Nat)(hc:Code s inst p a b):
    StateDecodeVector.Code (vectorBefore s op) inst p.toVector a b:=by
  have hf:(vectorBefore s op).funcs=s.funcs:=paid_funcs s op 2
  have hm:(vectorBefore s op).modules=s.modules:=paid_modules s op 2
  have ht:(vectorBefore s op).tables=s.tables:=paid_tables s op 2
  have raw:=hc.vector.raw
  have allocation:=raw.record.allocation.transport s (vectorBefore s op) inst p.toPositive hf hm ht
  have record:StateDecodeRaw.Code (vectorBefore s op) inst p.toRaw a b:=by
    refine {raw with record:=?_,function751:=?_,function752:=?_,function769:=?_,function770:=?_}
    · refine {raw.record with allocation:=allocation,function581:=?_,function236:=?_,function310:=?_}
      · rw[hf];exact raw.record.function581
      · rw[hf];exact raw.record.function236
      · rw[hf];exact raw.record.function310
    · rw[hf];exact raw.function751
    · rw[hf];exact raw.function752
    · rw[hf];exact raw.function769
    · rw[hf];exact raw.function770
  refine {hc.vector with raw:=record,function767:=?_}
  rw[hf];exact hc.vector.function767
end WNear.Proofs.StateDecodeVectorCopy
