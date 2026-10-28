import Proofs.StateDecodeRawRecordState
import Proofs.StateDecodeRawAllocationCode

/-! Original installed descriptors for the complete767/769/770 raw path.
Function addresses remain arbitrary resolved module addresses. -/
namespace WNear.Proofs.StateDecodeRaw
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384

structure Code (s : Store NearState) (inst : Nat) (p : Layout) (address581 address236 : Nat) : Prop where
  record : RecordCode s inst p.toPositive address581 address236 p.address310
  index751 : p.mi.funcAddrs[751]?=some p.address751
  function751 : s.funcs[p.address751]?=some (.wasm WNear.Binary.AllocateLayout.signature inst WNear.Binary.AllocateLayout.function751)
  index752 : p.mi.funcAddrs[752]?=some p.address752
  function752 : s.funcs[p.address752]?=some (.wasm WNear.Binary.AllocateLayout.signature inst WNear.Binary.AllocateLayout.function752)
  index769 : p.mi.funcAddrs[769]?=some p.address769
  function769 : s.funcs[p.address769]?=some (.wasm WNear.Binary.StateDecodeRaw.signature inst WNear.Binary.StateDecodeRaw.function769)
  index770 : p.mi.funcAddrs[770]?=some p.address770
  function770 : s.funcs[p.address770]?=some (.wasm WNear.Binary.StateDecodeRaw.recordSignature inst WNear.Binary.StateDecodeRaw.function770)

/-- The actual post752 record allocator code is derived from its original
selector and descriptors, rather than supplied as a future installation fact. -/
theorem Code.recordActual (s : Store NearState) (inst : Nat) (p : Layout) (a581 a236 : Nat)
    (hn : Native p) (hc : Code s inst p a581 a236) :
    RecordCode s inst (actualPositive p) a581 a236 p.address310 := by
  exact ⟨actual_positive_code s inst p hn hc.record.allocation,
    hc.record.index581,hc.record.function581,
    hc.record.index236,hc.record.function236,
    hc.record.index310,hc.record.function310⟩
end WNear.Proofs.StateDecodeRaw
