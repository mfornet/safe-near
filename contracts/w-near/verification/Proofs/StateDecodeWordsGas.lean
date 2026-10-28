import Proofs.StateDecodeWordsCall

/-! Exact successful opcode, activation, and residual gas of the accepted readers. -/
namespace WNear.Proofs.StateDecodeWords
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits paid_gas)
set_option maxRecDepth 16384

private theorem copy_gas (wide : Bool) (s : Store NearState) (op index rest : Nat) (memory : Memory) (out source : UInt32)
    (hc : s.host.gas.Credits (copyCost wide*op+rest)) :
    (copyAfter wide s op index memory out source).host.gas.burnt=s.host.gas.burnt+copyCost wide*op ∧
    (copyAfter wide s op index memory out source).host.gas.promises=s.host.gas.promises := by
  cases wide
  · exact paid_gas s op 4 rest hc
  · have budget : s.host.gas.Credits (4*op+(8*op+rest)) := hc.mono (by simp only [copyCost,ite_true];omega)
    have low := paid_gas s op 4 (8*op+rest) budget
    have credit := paid_credits s op 4 (8*op+rest) budget
    have high := paid_gas (lowStore s op index memory out source) op 8 rest credit
    change (paid (lowStore s op index memory out source) op 8).host.gas.burnt=s.host.gas.burnt+12*op ∧
      (paid (lowStore s op index memory out source) op 8).host.gas.promises=s.host.gas.promises
    rw [high.1,high.2]
    change (paid s op 4).host.gas.burnt+8*op=s.host.gas.burnt+12*op ∧ (paid s op 4).host.gas.promises=s.host.gas.promises
    rw [low.1,low.2]
    constructor <;> omega

theorem after_gas (wide : Bool) (s : Store NearState) (op index rest : Nat) (memory : Memory) (out source : UInt32)
    (hc : s.host.gas.Credits (bodyCost wide*op+rest)) :
    (after wide s op index memory out source).host.gas.burnt=s.host.gas.burnt+bodyCost wide*op ∧
    (after wide s op index memory out source).host.gas.promises=s.host.gas.promises ∧
    (after wide s op index memory out source).host.gas.Credits rest := by
  have cut : 6*op+(copyCost wide*op+(5*op+rest))≤bodyCost wide*op+rest := by simp only[bodyCost,Nat.add_mul];omega
  have budget := hc.mono cut
  have pre := paid_gas s op 6 (copyCost wide*op+(5*op+rest)) budget
  have cr := paid_credits s op 6 _ budget
  have cg := copy_gas wide (paid s op 6) op index (5*op+rest) memory out source cr
  have cc := copyAfter_credits wide (paid s op 6) op index (5*op+rest) memory out source cr
  have tail := paid_gas (copyAfter wide (paid s op 6) op index memory out source) op 5 rest cc
  have hb : (after wide s op index memory out source).host.gas.burnt=
      (paid (copyAfter wide (paid s op 6) op index memory out source) op 5).host.gas.burnt := by
    simp only [after,statusStore,storeByte_host,ValueReturnBorrow.paid_add]
  have hp : (after wide s op index memory out source).host.gas.promises=
      (paid (copyAfter wide (paid s op 6) op index memory out source) op 5).host.gas.promises := by
    simp only [after,statusStore,storeByte_host,ValueReturnBorrow.paid_add]
  refine ⟨?_,?_,after_credits wide s op index rest memory out source hc⟩
  · rw [hb,tail.1,cg.1,pre.1]
    simp only [bodyCost,Nat.add_mul]
    omega
  · rw [hp,tail.2,cg.2,pre.2]

theorem callAfter_gas (wide : Bool) (cfg : WasmConfig) (s : Store NearState) (index rest : Nat) (memory : Memory) (out source : UInt32)
    (hc : s.host.gas.Credits ((bodyCost wide+11)*cfg.regularOpCost+rest)) :
    (callAfter wide cfg s index memory out source).host.gas.burnt=s.host.gas.burnt+(bodyCost wide+11)*cfg.regularOpCost ∧
    (callAfter wide cfg s index memory out source).host.gas.promises=s.host.gas.promises ∧
    (callAfter wide cfg s index memory out source).host.gas.Credits rest := by
  let op:=cfg.regularOpCost
  have budget : s.host.gas.Credits (op+(10*op+(bodyCost wide*op+rest))) := hc.mono (by simp only[Nat.add_mul];dsimp[op];omega)
  have first := GasCounter.burn_credits s.host.gas op (10*op+(bodyCost wide*op+rest)) budget
  have second := GasCounter.burn_credits (chargedStore s op).host.gas (10*op) (bodyCost wide*op+rest) first.2.2.2
  have ag := after_gas wide (entered s op) op index rest memory out source second.2.2.2
  have gb : (entered s op).host.gas.burnt=s.host.gas.burnt+11*op := by
    change (chargedStore (chargedStore s op) (10*op)).host.gas.burnt=_
    rw [show (chargedStore (chargedStore s op) (10*op)).host.gas.burnt=(chargedStore s op).host.gas.burnt+10*op from second.2.1,
      show (chargedStore s op).host.gas.burnt=s.host.gas.burnt+op from first.2.1]
    omega
  have gp : (entered s op).host.gas.promises=s.host.gas.promises := second.2.2.1.trans first.2.2.1
  refine ⟨?_,ag.2.1.trans gp,ag.2.2⟩
  change (after wide (entered s op) op index memory out source).host.gas.burnt=_
  rw [ag.1,gb]
  simp only [Nat.add_mul]
  dsimp[op]
  omega
end WNear.Proofs.StateDecodeWords
