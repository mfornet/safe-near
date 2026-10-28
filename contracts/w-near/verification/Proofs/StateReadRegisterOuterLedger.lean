import Proofs.StateReadRegisterOuterPhases
import Proofs.StateReadRegisterOuterNative

/-! Closed instruction and step ledgers of the actual accepted f523 body. -/
namespace WNear.Proofs.StateReadRegisterOuter
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384

theorem bodyCost_eq (p : Layout) (hp : p.size≠0) : bodyCost p=13*p.size.toNat+1500 := by
  simp only [bodyCost,AllocateVectorOuter.bodyCost,AllocateVector.bodyCost,
    AllocateRecordCopy.bodyCost,AllocateRecord.bodyCost,AllocateZeroedRetry.bodyCost,ZeroFill.bodyCost,
    actualVector,vectorMemoryTemplate,AllocateVector.layout690,AllocateVector.actualRecord,hp,ite_false]
  omega

theorem bodySteps_eq (p : Layout) (hp : p.size≠0) : bodySteps p=12*p.size.toNat+1125 := by
  simp only [bodySteps,AllocateVectorOuter.bodySteps,AllocateVector.bodySteps,
    AllocateRecordCopy.bodySteps,AllocateRecord.bodySteps,AllocateZeroedRetry.bodySteps,ZeroFill.bodySteps,
    actualVector,vectorMemoryTemplate,AllocateVector.layout690,AllocateVector.actualRecord,hp,ite_false]
  omega
theorem size_toNat (p : Layout) (hn : Native p) : p.size.toNat=p.bytes.length := by
  rw [hn.size]
  change p.bytes.length%2^32=p.bytes.length
  apply Nat.mod_eq_of_lt
  have h := hn.sizeBound
  omega

theorem bodyCost_eq_bytes (p : Layout) (hn : Native p) : bodyCost p=13*p.bytes.length+1500 := by
  rw [bodyCost_eq p hn.allocation.positive,size_toNat p hn]

theorem bodySteps_eq_bytes (p : Layout) (hn : Native p) : bodySteps p=12*p.bytes.length+1125 := by
  rw [bodySteps_eq p hn.allocation.positive,size_toNat p hn]
end WNear.Proofs.StateReadRegisterOuter
