import Proofs.StateDecodeBorshReadSetup

/-! Original161 geometry and its constructed descriptor derive the complete
future162/425/315/316 accepted domains. No prepared-memory domain is assumed. -/
namespace WNear.Proofs.StateDecodeBorshRead
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] readI32 readI64 writeI32 writeI64

private theorem sub_nat(x:UInt32)(n:Nat)(h:n≤x.toNat)(hn:n<2^32):
    (x-UInt32.ofNat n).toNat=x.toNat-n:=by
  rw[UInt32.toNat_sub,UInt32.toNat_ofNat',Nat.mod_eq_of_lt hn]
  have lt:=x.toNat_lt
  omega

theorem stack_geometry(p:Layout)(hn:Native p):
    p.sp162.toNat=(scratch p).toNat ∧
    p.sp425.toNat+96=(scratch p).toNat ∧
    p.wrapperSP.toNat+192=(scratch p).toNat ∧
    p.sp.toNat+208=(scratch p).toNat ∧p.out.toNat=p.sp.toNat ∧
    p.wrapperOut.toNat+136=(scratch p).toNat ∧
    p.out425.toNat+48=(scratch p).toNat ∧
    p.out162.toNat=(scratch p).toNat+96 ∧p.slice.toNat=(scratch p).toNat+8:=by
  have n:=scratch_numbers p hn
  have lo:=hn.spLower
  have sp162:p.sp162.toNat=(scratch p).toNat:=congrArg UInt32.toNat hn.wrapperSP
  have sp425:p.sp425.toNat+96=(scratch p).toNat:=by
    rw[hn.borshSP,StateDecodeBorshWrapper.scratch]
    have eq:(p.sp162-96).toNat=p.sp162.toNat-96:=(sub_nat p.sp162 96 (by omega) (by omega))
    omega
  have sp315:p.wrapperSP.toNat+192=(scratch p).toNat:=by
    rw[hn.prefixSP,StateDecodeBorsh.scratch]
    have eq:(p.sp425-96).toNat=p.sp425.toNat-96:=(sub_nat p.sp425 96 (by omega) (by omega))
    omega
  have sp316:p.sp.toNat+208=(scratch p).toNat:=by
    rw[hn.childSP,StateDecodePrefixWrapper.scratch]
    have eq:(p.wrapperSP-16).toNat=p.wrapperSP.toNat-16:=(sub_nat p.wrapperSP 16 (by omega) (by omega))
    omega
  have same:p.out=p.sp:=hn.childOut.trans hn.childSP.symm
  have add(x:UInt32)(offset:Nat)(ho:offset<144)(hx:x.toNat+offset<p.sp161.toNat):
      (x+UInt32.ofNat offset).toNat=x.toNat+offset:=by
    rw[UInt32.toNat_add,UInt32.toNat_ofNat',Nat.mod_eq_of_lt (show offset<2^32 by omega)]
    have lt:=p.sp161.toNat_lt
    exact Nat.mod_eq_of_lt (by omega)
  have out315:p.wrapperOut.toNat+136=(scratch p).toNat:=by
    rw[hn.prefixOut,StateDecodeBorsh.scratch]
    have sub:(p.sp425-96).toNat=p.sp425.toNat-96:=(sub_nat p.sp425 96 (by omega) (by omega))
    have plus:(p.sp425-96+56).toNat=(p.sp425-96).toNat+56:=add (p.sp425-96) 56 (by omega) (by omega)
    rw[plus];omega
  have out425:p.out425.toNat+48=(scratch p).toNat:=by
    rw[hn.borshOut,StateDecodeBorshWrapper.scratch]
    have sub:(p.sp162-96).toNat=p.sp162.toNat-96:=(sub_nat p.sp162 96 (by omega) (by omega))
    have plus:(p.sp162-96+48).toNat=(p.sp162-96).toNat+48:=add (p.sp162-96) 48 (by omega) (by omega)
    rw[plus];omega
  exact ⟨sp162,sp425,sp315,sp316,congrArg UInt32.toNat same,out315,out425,
    by rw[hn.wrapperOut];exact scratch_add p hn 96 (by omega),
    by rw[hn.slice];exact scratch_add p hn 8 (by omega)⟩

theorem prefix_native(p:Layout)(hn:Native p):StateDecodePrefix.Native (actualWrapper p).toPrefix:=by
  have shape:=setupMemory_spec p hn
  have geo:=stack_geometry p hn
  have n:=scratch_numbers p hn
  have lo:=hn.spLower
  have ptr:=setup_descriptor p hn
  have source:=hn.sourceAbove
  have bound:=hn.headerBound
  have len:=hn.headerLength
  have nc:StateDecodePrefix.count (actualWrapper p).toPrefix=count p:=actual_count p hn
  refine ⟨shape.1,?_,?_,?_,?_,?_,?_,?_,ptr.1,ptr.2,?_,?_,?_,?_,?_,?_⟩
  · change (setupMemory p).byteSize≤2^32;rw[shape.2.1];exact hn.width
  · change 64≤p.sp.toNat;omega
  · change p.sp.toNat≤(setupMemory p).byteSize;rw[shape.2.1];omega
  · change p.sp.toNat≤p.out.toNat;omega
  · change p.out.toNat+16≤(setupMemory p).byteSize;rw[shape.2.1];omega
  · change p.sp.toNat≤p.slice.toNat;omega
  · change p.slice.toNat+8≤(setupMemory p).byteSize;rw[shape.2.1];omega
  · change p.sp.toNat≤p.pointer.toNat;omega
  · change p.pointer.toNat+4+(StateDecodePrefix.count (actualWrapper p).toPrefix).toNat≤(setupMemory p).byteSize;rw[nc,shape.2.1];omega
  · change 4+(StateDecodePrefix.count (actualWrapper p).toPrefix).toNat≤p.length.toNat;rw[nc];omega
  · rw[nc];exact hn.countPositive
  · rw[nc];exact hn.countSigned
  · change p.slice.toNat+8≤p.pointer.toNat ∨p.pointer.toNat+4+(StateDecodePrefix.count (actualWrapper p).toPrefix).toNat≤p.slice.toNat
    left;omega

theorem borsh_native(p:Layout)(hn:Native p):StateDecodeBorsh.Native (actualWrapper p).toBorsh:=by
  have shape:=setupMemory_spec p hn
  have geo:=stack_geometry p hn
  have n:=scratch_numbers p hn
  have lo:=hn.spLower
  have source:=hn.sourceAbove
  have bound:=hn.headerBound
  have len:=hn.headerLength
  have nc:StateDecodeBorsh.count (actualWrapper p).toBorsh=count p:=actual_count p hn
  have pre:StateDecodePrefixWrapper.Native (actualWrapper p).toPrefixWrapper:=by
    refine ⟨prefix_native p hn,hn.childSP,hn.childOut,hn.childGlobal,?_⟩
    change p.wrapperOut.toNat+16≤(setupMemory p).byteSize;rw[shape.2.1];omega
  refine ⟨pre,hn.prefixSP,hn.prefixOut,hn.prefixGlobal,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · change 256≤p.sp425.toNat;omega
  · change p.sp425.toNat≤(setupMemory p).byteSize;rw[shape.2.1];omega
  · change p.sp425.toNat≤p.slice.toNat;omega
  · change p.sp425.toNat≤p.pointer.toNat;omega
  · change p.sp425.toNat≤p.out425.toNat;omega
  · change p.out425.toNat+44≤(setupMemory p).byteSize;rw[shape.2.1];omega
  · change p.pointer.toNat+4+(StateDecodeBorsh.count (actualWrapper p).toBorsh).toNat+24≤(setupMemory p).byteSize;rw[nc,shape.2.1];exact bound
  · change 4+(StateDecodeBorsh.count (actualWrapper p).toBorsh).toNat+24≤p.length.toNat;rw[nc];exact len
  · change p.slice.toNat+8≤p.pointer.toNat ∨p.pointer.toNat+4+(StateDecodeBorsh.count (actualWrapper p).toBorsh).toNat+24≤p.slice.toNat
    left;omega

theorem wrapper_native(p:Layout)(hn:Native p):StateDecodeBorshWrapper.Native (actualWrapper p):=by
  have shape:=setupMemory_spec p hn
  have geo:=stack_geometry p hn
  have n:=scratch_numbers p hn
  have lo:=hn.spLower
  refine ⟨borsh_native p hn,hn.borshSP,hn.borshOut,hn.borshGlobal,?_,?_,?_⟩
  · change 352≤p.sp162.toNat;omega
  · change p.sp162.toNat≤(setupMemory p).byteSize;rw[shape.2.1];omega
  · change p.out162.toNat+48≤(setupMemory p).byteSize;rw[shape.2.1];omega
end WNear.Proofs.StateDecodeBorshRead
