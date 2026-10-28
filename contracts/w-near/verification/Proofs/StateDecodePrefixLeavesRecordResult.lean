import Proofs.StateDecodePrefixLeavesRecordCall

/-! Full actual764 result, footprint and exact metering. -/
namespace WNear.Proofs.StateDecodePrefixLeaves
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_gas)
attribute [local irreducible] readI32 writeI32

theorem recordMemory_spec (m : Memory) (out len : UInt32) (hw:m.wf) (hb:out.toNat+8≤m.byteSize) :
    (recordMemory m out len).wf ∧(recordMemory m out len).byteSize=m.byteSize ∧(recordMemory m out len).max=m.max ∧
    ∀j,(recordMemory m out len).read8 j=
      if out.toNat≤j ∧j<out.toNat+4 then 0
      else if out.toNat+4≤j ∧j<out.toNat+8 then UInt8.ofNat (len.toNat >>> (8*(j-(out.toNat+4))))
      else m.read8 j := by
  simpa only[recordMemory,StateDecodeSlices.finalMemory,StateDecodeSlices.firstMemory,StateDecodeSlices.highWord,
    StateDecodeSlices.lowWord,Bool.false_eq_true,ite_false,UInt32.toNat_zero,Nat.zero_shiftRight,show UInt8.ofNat 0=0 from rfl] using
    StateDecodeSlices.finalMemory_spec false m out 0 len len hw hb

theorem recordMemory_words (m : Memory) (out len : UInt32) (hw:m.wf) (hb:out.toNat+8≤m.byteSize) :
    readI32 (recordMemory m out len) out.toNat=0 ∧readI32 (recordMemory m out len) (out.toNat+4)=len :=
  StateDecodeSlices.finalMemory_words false m out 0 len len hw hb

private theorem mems_paid (s : Store NearState) (op n : Nat) : (paid s op n).mems=s.mems := by
  induction n with |zero=>rfl|succ n ih=>exact ih

theorem recordAfter_memory (s : Store NearState) (op i : Nat) (m : Memory) (out len : UInt32)
    (hm:s.mems[i]?=some m) : (recordAfter s op i m out len).mems[i]?=some (recordMemory m out len) := by
  have mp:(paid s op 3).mems[i]?=some m:=by rw[mems_paid];exact hm
  have one:=storeI32_memory (paid s op 3) i (out.toNat+4) m len mp
  have hp:(paid (recordHigh s op i m out len) op 3).mems[i]?=some (writeI32 m (out.toNat+4) len):=by
    rw[mems_paid];exact one
  exact storeI32_memory _ i out.toNat _ 0 hp

theorem recordCallAfter_memory (cfg : WasmConfig) (s : Store NearState) (i : Nat) (m : Memory) (out len : UInt32)
    (hm:s.mems[i]?=some m) : (recordCallAfter cfg s i m out len).mems[i]?=some (recordMemory m out len) :=
  recordAfter_memory (recordEntered s cfg.regularOpCost) cfg.regularOpCost i m out len hm

private def fields (s:Store NearState):=(s.funcs,s.modules,s.tables,s.globals)
private theorem fields_paid (s : Store NearState) (op n : Nat) : fields (paid s op n)=fields s:=by
  induction n with |zero=>rfl|succ n ih=>exact ih
private theorem fields_store (s : Store NearState) (i a : Nat) (m : Memory) (v : UInt32) : fields (storeI32 s i a m v)=fields s:=rfl
private theorem fields_project (s t : Store NearState) (h:fields t=fields s) :
    t.funcs=s.funcs ∧t.modules=s.modules ∧t.tables=s.tables ∧t.globals=s.globals:=
  ⟨congrArg (fun x=>x.1) h,congrArg (fun x=>x.2.1) h,congrArg (fun x=>x.2.2.1) h,congrArg (fun x=>x.2.2.2) h⟩

theorem recordAfter_fields (s : Store NearState) (op i : Nat) (m : Memory) (out len : UInt32) :
    (recordAfter s op i m out len).funcs=s.funcs ∧(recordAfter s op i m out len).modules=s.modules ∧
    (recordAfter s op i m out len).tables=s.tables ∧(recordAfter s op i m out len).globals=s.globals := by
  apply fields_project
  simp only[recordAfter,recordHigh,fields_store,fields_paid]

theorem recordCallAfter_fields (cfg : WasmConfig) (s : Store NearState) (i : Nat) (m : Memory) (out len : UInt32) :
    (recordCallAfter cfg s i m out len).funcs=s.funcs ∧(recordCallAfter cfg s i m out len).modules=s.modules ∧
    (recordCallAfter cfg s i m out len).tables=s.tables ∧(recordCallAfter cfg s i m out len).globals=s.globals :=
  recordAfter_fields (recordEntered s cfg.regularOpCost) cfg.regularOpCost i m out len

private def view (seed host:NearState):={host with gas:=seed.gas,gasProfile:=seed.gasProfile}
private theorem view_paid (seed:NearState)(s:Store NearState)(op n:Nat):view seed (paid s op n).host=view seed s.host:=by
  induction n with |zero=>rfl|succ n ih=>exact ih
private theorem view_store (seed:NearState)(s:Store NearState)(i a:Nat)(m:Memory)(v:UInt32):view seed (storeI32 s i a m v).host=view seed s.host:=rfl

theorem recordCallAfter_host (cfg : WasmConfig) (s : Store NearState) (i : Nat) (m : Memory) (out len : UInt32) :
    {(recordCallAfter cfg s i m out len).host with gas:=s.host.gas,gasProfile:=s.host.gasProfile}=s.host := by
  change view s.host (recordCallAfter cfg s i m out len).host=s.host
  simp only[recordCallAfter,recordAfter,recordHigh,view_store,view_paid]
  rfl

theorem recordAfter_gas (s : Store NearState) (op i rest : Nat) (m : Memory) (out len : UInt32)
    (hc:s.host.gas.Credits (6*op+rest)) :
    (recordAfter s op i m out len).host.gas.burnt=s.host.gas.burnt+6*op ∧
    (recordAfter s op i m out len).host.gas.promises=s.host.gas.promises := by
  simpa only[recordAfter,recordHigh,storeI32_host,paid,chargedStore] using paid_gas s op 6 rest hc

theorem recordCallAfter_gas (cfg : WasmConfig) (s : Store NearState) (i rest : Nat) (m : Memory) (out len : UInt32)
    (hc:s.host.gas.Credits (16*cfg.regularOpCost+rest)) :
    (recordCallAfter cfg s i m out len).host.gas.burnt=s.host.gas.burnt+16*cfg.regularOpCost ∧
    (recordCallAfter cfg s i m out len).host.gas.promises=s.host.gas.promises ∧
    (recordCallAfter cfg s i m out len).host.gas.Credits rest := by
  let op:=cfg.regularOpCost
  have c0:=StorePair.charged_credits s op (9*op+(6*op+rest)) (hc.mono (by dsimp[op];omega))
  have c1:=StorePair.charged_credits (chargedStore s op) (9*op) (6*op+rest) c0
  have b0:=GasCounter.burn_credits s.host.gas op (9*op+(6*op+rest)) (hc.mono (by dsimp[op];omega))
  have b1:=GasCounter.burn_credits (chargedStore s op).host.gas (9*op) (6*op+rest) c0
  have e0:(chargedStore s op).host.gas.burnt=s.host.gas.burnt+op:=b0.2.1
  have e1:(recordEntered s op).host.gas.burnt=(chargedStore s op).host.gas.burnt+9*op:=b1.2.1
  have ep:(recordEntered s op).host.gas.promises=s.host.gas.promises:=b1.2.2.1.trans b0.2.2.1
  have hg:=recordAfter_gas (recordEntered s op) op i rest m out len c1
  have cr:=recordCallAfter_credits cfg s i rest m out len hc
  refine ⟨?_,?_,cr⟩
  · change (recordAfter (recordEntered s op) op i m out len).host.gas.burnt=s.host.gas.burnt+16*op
    rw[hg.1]
    rw[e1,e0]
    omega
  · exact hg.2.trans ep
end WNear.Proofs.StateDecodePrefixLeaves
