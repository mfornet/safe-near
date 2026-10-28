import Proofs.StateReadOuterNative

/-! Original stack-template equalities transfer through the actual memory
preparation without any decoder or allocator Native premise. -/
namespace WNear.Proofs.StateReadOuter
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] packedMemory preparedStorageMemory readI32 writeI32

theorem actualDecoder_geometry(p:Layout)(hn:Native p):DecoderGeometry (actualDecoder p):=by
  exact ⟨hn.decoderGeometry.slice,hn.decoderGeometry.wrapperSP,hn.decoderGeometry.wrapperOut,hn.decoderGeometry.wrapperGlobal,hn.decoderGeometry.borshSP,hn.decoderGeometry.borshOut,hn.decoderGeometry.borshGlobal,hn.decoderGeometry.prefixSP,hn.decoderGeometry.prefixOut,hn.decoderGeometry.prefixGlobal,hn.decoderGeometry.childSP,hn.decoderGeometry.childOut,hn.decoderGeometry.childGlobal⟩

theorem actualAllocation_geometry(p:Layout)(hn:Native p):AllocationGeometry (actualDecoder p) (actualAllocation p):=by
  exact ⟨hn.allocationGeometry.vectorSP,hn.allocationGeometry.vectorOut,hn.allocationGeometry.vectorGlobal,hn.allocationGeometry.rawSP,hn.allocationGeometry.rawOut,hn.allocationGeometry.rawGlobal,hn.allocationGeometry.allocationSP,hn.allocationGeometry.allocationGlobal,hn.allocationGeometry.flagZero⟩

private theorem sub_nat(x:UInt32)(n:Nat)(h:n≤x.toNat)(hn:n<2^32):
    (x-UInt32.ofNat n).toNat=x.toNat-n:=by
  rw[UInt32.toNat_sub,UInt32.toNat_ofNat',Nat.mod_eq_of_lt hn]
  have lt:=x.toNat_lt
  omega

theorem decoder_stack_numbers(d:StateDecodeBorshRead.Layout)(geometry:DecoderGeometry d)(lower:496≤d.sp161.toNat):
    d.sp162.toNat+144=d.sp161.toNat ∧d.sp425.toNat+240=d.sp161.toNat ∧
    d.wrapperSP.toNat+336=d.sp161.toNat ∧d.sp.toNat+352=d.sp161.toNat:=by
  have first:d.sp162.toNat=d.sp161.toNat-144:=by
    rw[geometry.wrapperSP,StateDecodeBorshRead.scratch]
    exact sub_nat d.sp161 144 (by omega) (by omega)
  have second:d.sp425.toNat=d.sp162.toNat-96:=by
    rw[geometry.borshSP,StateDecodeBorshWrapper.scratch]
    exact sub_nat d.sp162 96 (by omega) (by omega)
  have third:d.wrapperSP.toNat=d.sp425.toNat-96:=by
    rw[geometry.prefixSP,StateDecodeBorsh.scratch]
    exact sub_nat d.sp425 96 (by omega) (by omega)
  have fourth:d.sp.toNat=d.wrapperSP.toNat-16:=by
    rw[geometry.childSP,StateDecodePrefixWrapper.scratch]
    exact sub_nat d.wrapperSP 16 (by omega) (by omega)
  exact ⟨by omega,by omega,by omega,by omega⟩

theorem allocation_stack_numbers(p:Layout)(hn:Native p):
    (actualAllocation p).spVector.toNat+416=(scratch p).toNat ∧
    (actualAllocation p).spRaw.toNat+432=(scratch p).toNat ∧
    (actualAllocation p).sp.toNat+480=(scratch p).toNat ∧
    80≤(actualAllocation p).spVector.toNat ∧64≤(actualAllocation p).spRaw.toNat ∧
    (actualAllocation p).outRaw.toNat+8≤(scratch p).toNat ∧
    (actualAllocation p).outVector.toNat+12≤(scratch p).toNat:=by
  have n:=scratch_numbers p hn
  have lo:=hn.spLower
  have d:=(decoder_stack_numbers p.decoderTemplate hn.decoderGeometry (by rw[hn.decoderSP];omega))
  rw[hn.decoderSP] at d
  have vector:p.allocationTemplate.spVector.toNat=(scratch p).toNat-416:=by
    rw[hn.allocationGeometry.vectorSP,StateDecodePrefix.scratch]
    have sub: (p.decoderTemplate.sp-64).toNat=p.decoderTemplate.sp.toNat-64:=
      sub_nat p.decoderTemplate.sp 64 (by omega) (by omega)
    omega
  have raw:p.allocationTemplate.spRaw.toNat=(scratch p).toNat-432:=by
    rw[hn.allocationGeometry.rawSP]
    have sub: (p.allocationTemplate.spVector-16).toNat=p.allocationTemplate.spVector.toNat-16:=
      sub_nat p.allocationTemplate.spVector 16 (by omega) (by omega)
    omega
  have positive:p.allocationTemplate.sp.toNat=(scratch p).toNat-480:=by
    rw[hn.allocationGeometry.allocationSP]
    have sub:(p.allocationTemplate.spRaw-48).toNat=p.allocationTemplate.spRaw.toNat-48:=
      sub_nat p.allocationTemplate.spRaw 48 (by omega) (by omega)
    omega
  have lt:=p.sp219.toNat_lt
  have rawOut:p.allocationTemplate.outRaw.toNat=p.allocationTemplate.spRaw.toNat+8:=by
    rw[hn.allocationGeometry.rawOut,UInt32.toNat_add]
    simp only[UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod]
    exact Nat.mod_eq_of_lt (by omega)
  have vectorOut:p.allocationTemplate.outVector.toNat=(scratch p).toNat-368:=by
    rw[hn.allocationGeometry.vectorOut,StateDecodePrefix.allocatedOut]
    have low:(StateDecodePrefix.scratch p.decoderTemplate.toPrefix).toNat=(scratch p).toNat-416:=by
      rw[←hn.allocationGeometry.vectorSP];exact vector
    rw[UInt32.toNat_add]
    simp only[UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod]
    rw[Nat.mod_eq_of_lt (by omega : (StateDecodePrefix.scratch p.decoderTemplate.toPrefix).toNat+48<4294967296)]
    omega
  change p.allocationTemplate.spVector.toNat+416=(scratch p).toNat ∧
    p.allocationTemplate.spRaw.toNat+432=(scratch p).toNat ∧p.allocationTemplate.sp.toNat+480=(scratch p).toNat ∧
    80≤p.allocationTemplate.spVector.toNat ∧64≤p.allocationTemplate.spRaw.toNat ∧
    p.allocationTemplate.outRaw.toNat+8≤(scratch p).toNat ∧p.allocationTemplate.outVector.toNat+12≤(scratch p).toNat
  exact ⟨by omega,by omega,by omega,by omega,by omega,by omega,by omega⟩
end WNear.Proofs.StateReadOuter
