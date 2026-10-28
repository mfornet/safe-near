import Proofs.StateDecodeScalarOutputReadback
import Proofs.StateDecodeScalarReadback
import Proofs.StateDecodeScalarFinalFrame
import Proofs.TotalSupply

/-! Accepted scalar results represent original input words, without assuming a decoded state. -/
namespace WNear.Proofs.StateDecodeScalar
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384
attribute [local irreducible] readI64

theorem finalMemory_low_original (wide : Bool) (p : Layout) (hn : Native wide p)
    (hs : p.slice.toNat+8≤p.out.toNat+8 ∨ p.out.toNat+16≤p.slice.toNat) :
    readI64 (finalMemory wide p) (p.out.toNat+8)=readI64 p.memory p.pointer.toNat :=
  (finalMemory_low wide p hn hs).trans (lowValue_eq wide p hn)

theorem finalMemory_high_original (p : Layout) (hn : Native true p)
    (hs : p.slice.toNat+8≤p.out.toNat+16 ∨ p.out.toNat+24≤p.slice.toNat) :
    readI64 (finalMemory true p) (p.out.toNat+16)=readI64 p.memory (p.pointer.toNat+8) :=
  (finalMemory_high p hn hs).trans (highValue_eq p hn)

theorem finalMemory_u128 (p : Layout) (hn : Native true p) (value : Nat)
    (hs : p.slice.toNat+8≤p.out.toNat+8 ∨ p.out.toNat+24≤p.slice.toNat)
    (hv : TotalSupply.U128At p.memory p.pointer.toNat value) :
    TotalSupply.U128At (finalMemory true p) (p.out.toNat+8) value := by
  unfold TotalSupply.U128At
  rw [finalMemory_low_original true p hn (by omega)]
  have high:=finalMemory_high_original p hn (by omega)
  rw [show p.out.toNat+8+8=p.out.toNat+16 by omega,high]
  exact hv

theorem after_u128 (cfg : WasmConfig) (s : Store NearState) (p : Layout) (hn : Native true p)
    (hm : s.mems[p.memoryIndex]?=some p.memory) (value : Nat)
    (hs : p.slice.toNat+8≤p.out.toNat+8 ∨ p.out.toNat+24≤p.slice.toNat)
    (hv : TotalSupply.U128At p.memory p.pointer.toNat value) :
    (after true cfg s p).mems[p.memoryIndex]?=some (finalMemory true p) ∧
    readI32 (finalMemory true p) p.out.toNat=0 ∧
    TotalSupply.U128At (finalMemory true p) (p.out.toNat+8) value :=
  ⟨after_memory true cfg s p hm,finalMemory_tag true p hn,finalMemory_u128 p hn value hs hv⟩
end WNear.Proofs.StateDecodeScalar
