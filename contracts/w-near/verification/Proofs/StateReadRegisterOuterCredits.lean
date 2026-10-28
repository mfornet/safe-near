import Proofs.StateReadRegisterOuterHost

/-! Residual credits through actual523 calls, paying each host fee once. -/
namespace WNear.Proofs.StateReadRegisterOuter
open Wasm Wasm.Near MeteredLogic MeteredHosts
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
attribute [local irreducible] looked guarded vectorArguments allocated readArguments readDone copyDone after readFinalMemory actualVector StateDispatchRead.finalStore StateDispatchLengthOuter.finalStore copied copyHigh copyLow readLayout readOutputMemory actualLength lengthMemory vectorGrown lengthArguments StateDispatchRead.callAfter StateDispatchLengthOuter.callAfter AllocateVectorOuter.callAfter fee

theorem looked_credits (cfg : WasmConfig) (s : Store NearState) (p : Layout) (rest : Nat)
    (hc : s.host.gas.Credits (302*cfg.regularOpCost+s.host.extCosts.cost "base"+rest)) :
    (looked cfg s p).host.gas.Credits rest := by
  let op := cfg.regularOpCost
  let a := lengthArguments s op p
  have ca : a.host.gas.Credits (290*op+s.host.extCosts.cost "base"+rest) :=
    lengthArguments_credits s op _ p (hc.mono (by dsimp [op];omega))
  have c0 := StorePair.charged_credits a op (10*op+(279*op+s.host.extCosts.cost "base"+rest)) (ca.mono (by omega))
  have c1 := StorePair.charged_credits (chargedStore a op) (10*op) (279*op+s.host.extCosts.cost "base"+rest) c0
  have cb : (StateDispatchLengthOuter.entered a op).host.gas.Credits
      (279*cfg.regularOpCost+(StateDispatchLengthOuter.entered a op).host.extCosts.cost "base"+rest) := by
    simpa only [StateDispatchLengthOuter.entered,chargedStore,chargeHost,a,lengthArguments_costs,op] using c1
  have h := StateDispatchLengthOuter.final_credits cfg (StateDispatchLengthOuter.entered a op) (actualLength p) rest cb
  simpa only [looked,StateDispatchLengthOuter.callAfter,a,op] using h

theorem guarded_credits (cfg : WasmConfig) (s : Store NearState) (p : Layout) (rest : Nat)
    (hc : s.host.gas.Credits (307*cfg.regularOpCost+s.host.extCosts.cost "base"+rest)) :
    (guarded cfg s p).host.gas.Credits rest := by
  unfold guarded
  exact paid_credits (looked cfg s p) cfg.regularOpCost 5 rest (looked_credits cfg s p _ (hc.mono (by omega)))

theorem vectorArguments_credits (cfg : WasmConfig) (s : Store NearState) (p : Layout) (rest : Nat)
    (hc : s.host.gas.Credits (314*cfg.regularOpCost+s.host.extCosts.cost "base"+rest)) :
    (vectorArguments cfg s p).host.gas.Credits rest := by
  unfold vectorArguments
  exact paid_credits (guarded cfg s p) cfg.regularOpCost 7 rest (guarded_credits cfg s p _ (hc.mono (by omega)))

theorem allocated_credits (cfg : WasmConfig) (s : Store NearState) (p : Layout) (rest : Nat)
    (hc : s.host.gas.Credits ((AllocateVectorOuter.bodyCost (actualVector p)+326)*cfg.regularOpCost+
      AllocateVectorOuter.fee cfg (actualVector p)+s.host.extCosts.cost "base"+rest)) :
    (allocated cfg s p).host.gas.Credits rest := by
  unfold allocated
  exact AllocateVectorOuter.callAfter_credits cfg (vectorArguments cfg s p) (actualVector p) rest
    (vectorArguments_credits cfg s p _ (hc.mono (by simp only [Nat.add_mul];omega)))

theorem readArguments_credits (cfg : WasmConfig) (s : Store NearState) (p : Layout) (rest : Nat)
    (hc : s.host.gas.Credits ((AllocateVectorOuter.bodyCost (actualVector p)+333)*cfg.regularOpCost+
      AllocateVectorOuter.fee cfg (actualVector p)+s.host.extCosts.cost "base"+rest)) :
    (readArguments cfg s p).host.gas.Credits rest := by
  unfold readArguments
  exact paid_credits (allocated cfg s p) cfg.regularOpCost 7 rest (allocated_credits cfg s p _ (hc.mono (by simp only [Nat.add_mul];omega)))

private theorem read_call_credits (cfg : WasmConfig) (s : Store NearState) (q : StateDispatchRead.Layout)
    (bytes : List UInt8) (rest : Nat) (hc : s.host.gas.Credits (249*cfg.regularOpCost+RegisterRead.readCost s.host bytes.length+rest)) :
    (StateDispatchRead.callAfter cfg s q bytes).host.gas.Credits rest := by
  let op := cfg.regularOpCost
  let a := s
  have ca : a.host.gas.Credits (249*op+RegisterRead.readCost a.host bytes.length+rest) := hc
  have c0 := StorePair.charged_credits a op (11*op+(237*op+RegisterRead.readCost a.host bytes.length+rest)) (ca.mono (by omega))
  have c1 := StorePair.charged_credits (chargedStore a op) (11*op) (237*op+RegisterRead.readCost a.host bytes.length+rest) c0
  have cb : (StateDispatchRead.entered a op).host.gas.Credits
      (237*cfg.regularOpCost+RegisterRead.readCost (StateDispatchRead.entered a op).host bytes.length+rest) := by
    simpa only [StateDispatchRead.entered,RegisterRead.readCost,chargedStore,chargeHost,op] using c1
  have h := StateDispatchRead.final_credits cfg (StateDispatchRead.entered a op) q bytes rest cb
  simpa only [StateDispatchRead.callAfter,a,op] using h

theorem readDone_credits (cfg : WasmConfig) (s : Store NearState) (p : Layout) (rest : Nat)
    (hc : s.host.gas.Credits ((AllocateVectorOuter.bodyCost (actualVector p)+582)*cfg.regularOpCost+fee cfg s p+rest)) :
    (readDone cfg s p).host.gas.Credits rest := by
  have cr := readArguments_credits cfg s p (249*cfg.regularOpCost+RegisterRead.readCost s.host p.bytes.length+rest)
    (hc.mono (by simp only [fee,Nat.add_mul];omega))
  have ca : (readArguments cfg s p).host.gas.Credits (249*cfg.regularOpCost+RegisterRead.readCost (readArguments cfg s p).host p.bytes.length+rest) := by
    simpa only [RegisterRead.readCost,readArguments_costs] using cr
  unfold readDone
  exact read_call_credits cfg (readArguments cfg s p) (readLayout p) p.bytes rest ca

private theorem copy_credits (s : Store NearState) (op index : Nat) (memory : Memory) (out scratch : UInt32) (rest : Nat)
    (hc : s.host.gas.Credits (14*op+rest)) : (copied s op index memory out scratch).host.gas.Credits rest := by
  have c10 : (copyHigh s op index memory out scratch).host.gas.Credits (4*op+rest) := by
    simpa only [copyHigh,storeI32_host] using paid_credits s op 10 (4*op+rest) (hc.mono (by omega))
  have c4 := paid_credits (copyHigh s op index memory out scratch) op 4 rest c10
  simpa only [copied,copyLow,storeI64_host] using c4

theorem copyDone_credits (cfg : WasmConfig) (s : Store NearState) (p : Layout) (rest : Nat)
    (hc : s.host.gas.Credits ((AllocateVectorOuter.bodyCost (actualVector p)+596)*cfg.regularOpCost+fee cfg s p+rest)) :
    (copyDone cfg s p).host.gas.Credits rest := by
  have cr := readDone_credits cfg s p (14*cfg.regularOpCost+rest) (hc.mono (by simp only [Nat.add_mul];omega))
  unfold copyDone
  exact copy_credits (readDone cfg s p) cfg.regularOpCost p.memoryIndex (readFinalMemory p) p.out523 (scratch p) rest cr

theorem after_credits (cfg : WasmConfig) (s : Store NearState) (p : Layout) (rest : Nat)
    (hc : s.host.gas.Credits (bodyCost p*cfg.regularOpCost+fee cfg s p+rest)) :
    (after cfg s p).host.gas.Credits rest := by
  have cc := copyDone_credits cfg s p (5*cfg.regularOpCost+rest) (hc.mono (by simp only [bodyCost,Nat.add_mul];omega))
  have cb := StorePair.charged_credits (copyDone cfg s p) cfg.regularOpCost (4*cfg.regularOpCost+rest) (cc.mono (by omega))
  simpa only [after,branched,setGlobal] using paid_credits (branched cfg s p) cfg.regularOpCost 4 rest cb
end WNear.Proofs.StateReadRegisterOuter
