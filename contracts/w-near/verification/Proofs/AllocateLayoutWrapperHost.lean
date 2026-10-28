import Proofs.AllocateLayoutWrapperResult

/-! Alignment-one layout setup preserves every functional host field. -/
namespace WNear.Proofs.AllocateLayoutWrapper
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
set_option maxRecDepth 16384
private def view (seed host : NearState) := {host with gas:=seed.gas,gasProfile:=seed.gasProfile}
private theorem view_paid (seed : NearState) (s : Store NearState) (op n : Nat) : view seed (paid s op n).host=view seed s.host := by
  induction n with | zero=>rfl | succ n ih=>exact ih
private theorem view_charge (seed : NearState) (s : Store NearState) (n : Nat) : view seed (chargedStore s n).host=view seed s.host := rfl
private theorem view_global (seed : NearState) (s : Store NearState) (i : Nat) (v : Value) : view seed (setGlobal s i v).host=view seed s.host := rfl
private theorem view32 (seed : NearState) (s : Store NearState) (i a : Nat) (m : Memory) (v : UInt32) : view seed (storeI32 s i a m v).host=view seed s.host := rfl
private theorem view64 (seed : NearState) (s : Store NearState) (i a : Nat) (m : Memory) (v : UInt64) : view seed (storeI64 s i a m v).host=view seed s.host := rfl
private theorem view_leaf (seed : NearState) (s : Store NearState) (op : Nat) (p : AllocateLayout.Layout) :
    view seed (AllocateLayout.called s op p).host=view seed s.host := by
  simp only [AllocateLayout.called,AllocateLayout.entered,AllocateLayout.after,view_global,view_paid,
    AllocateLayout.low,AllocateLayout.roundedStore,view32,AllocateLayout.high,AllocateLayout.loaded,
    AllocateLayout.guarded,AllocateLayout.reserved,view_charge]
private theorem view_called (seed : NearState) (s : Store NearState) (op : Nat) (p : Layout) :
    view seed (called s op p).host=view seed s.host := by
  simp only [called,entered,after,view_global,view_paid,copied,copyStore,view64,laidOut,view_leaf,
    arguments,setupStore,InterfaceSetBody.storeWord,view32,alignmentStore,constantStore,reserved,view_charge]
theorem called_functional_host (s : Store NearState) (op : Nat) (p : Layout) :
    {(called s op p).host with gas:=s.host.gas,gasProfile:=s.host.gasProfile}=s.host := by
  change view s.host (called s op p).host=s.host
  rw [view_called]
  rfl
end WNear.Proofs.AllocateLayoutWrapper
