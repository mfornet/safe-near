import Proofs.StateDecodePrefixOutputSteps

/-! The actual316 output snapshots only the remainder descriptor. The vector
packed word is read from highMemory, after the first caller-output write. -/
namespace WNear.Proofs.StateDecodePrefix.Output
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
structure Layout where
  memory:Memory
  index:Nat
  out:UInt32
  scratch:UInt32
  slice:UInt32
structure Native(p:Layout):Prop where
  wf:p.memory.wf
  width:p.memory.byteSize≤2^32
  outBound:p.out.toNat+16≤p.memory.byteSize
  scratchBound:p.scratch.toNat+64≤p.memory.byteSize
  sliceBound:p.slice.toNat+8≤p.memory.byteSize

def remainder(p:Layout):=readI64 p.memory (p.scratch.toNat+8)
def highMemory(p:Layout):=writeI32 p.memory (p.out+12).toNat (readI32 p.memory (p.scratch.toNat+56))
def lowMemory(p:Layout):=writeI64 (highMemory p) (p.out.toNat+4) (readI64 (highMemory p) (p.scratch.toNat+48))
def tagMemory(p:Layout):=writeI32 (lowMemory p) p.out.toNat 0
def finalMemory(p:Layout):=writeI64 (tagMemory p) p.slice.toNat (remainder p)
def cachedFrame(frame:CallFrame)(p:Layout):=StateDecodeScalar.loaded64Frame frame 4 (remainder p)
def cached(s:Store NearState)(op:Nat):=paid s op 3
def high(s:Store NearState)(op:Nat)(p:Layout):=outputHighStore (cached s op) op p.index p.memory p.out p.scratch
def low(s:Store NearState)(op:Nat)(p:Layout):=outputLowStore (high s op p) op p.index (highMemory p) p.out p.scratch
def tagged(s:Store NearState)(op:Nat)(p:Layout):=outputTagStore (low s op p) op p.index (lowMemory p) p.out
def described(s:Store NearState)(op:Nat)(p:Layout):=StateDecodeScalar.store64Local (tagged s op p) op p.index (tagMemory p) p.slice (remainder p)
def after(s:Store NearState)(op:Nat)(p:Layout):=chargedStore (described s op p) op

theorem out_address(p:Layout)(hn:Native p):(p.out+12).toNat=p.out.toNat+12:=by
  have o:=hn.outBound;have w:=hn.width
  rw[UInt32.toNat_add]
  simp only[UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod]
  omega

theorem memory_specs(p:Layout)(hn:Native p):
    (highMemory p).wf ∧(highMemory p).byteSize=p.memory.byteSize ∧
    (lowMemory p).wf ∧(lowMemory p).byteSize=p.memory.byteSize ∧
    (tagMemory p).wf ∧(tagMemory p).byteSize=p.memory.byteSize:=by
  have hb:(p.out+12).toNat+4≤p.memory.byteSize:=by rw[out_address p hn];exact hn.outBound
  have h:=writeI32_spec p.memory (p.out+12).toNat (readI32 p.memory (p.scratch.toNat+56)) hn.wf hb
  have lb:p.out.toNat+4+8≤(highMemory p).byteSize:=by change _≤(writeI32 _ _ _).byteSize;rw[h.2.1];have o:=hn.outBound;omega
  have l:=writeI64_spec (highMemory p) (p.out.toNat+4) (readI64 (highMemory p) (p.scratch.toNat+48)) h.1 lb
  have tb:p.out.toNat+4≤(lowMemory p).byteSize:=by change _≤(writeI64 _ _ _).byteSize;rw[l.2.1];change _≤(writeI32 _ _ _).byteSize;rw[h.2.1];have o:=hn.outBound;omega
  have t:=writeI32_spec (lowMemory p) p.out.toNat 0 l.1 tb
  exact ⟨h.1,h.2.1,l.1,l.2.1.trans h.2.1,t.1,t.2.1.trans (l.2.1.trans h.2.1)⟩

theorem cached_credits(s:Store NearState)(op rest:Nat)(hc:s.host.gas.Credits (20*op+rest)):
    (cached s op).host.gas.Credits (17*op+rest):=paid_credits s op 3 _ (hc.mono (by omega))
theorem high_credits(s:Store NearState)(op rest:Nat)(p:Layout)(hc:s.host.gas.Credits (20*op+rest)):
    (high s op p).host.gas.Credits (11*op+rest):=by
  have h:=paid_credits (cached s op) op 6 (11*op+rest) ((cached_credits s op rest hc).mono (by omega))
  simpa only[high,outputHighStore,storeI32_host] using h
theorem low_credits(s:Store NearState)(op rest:Nat)(p:Layout)(hc:s.host.gas.Credits (20*op+rest)):
    (low s op p).host.gas.Credits (7*op+rest):=by
  have h:=paid_credits (high s op p) op 4 (7*op+rest) ((high_credits s op rest p hc).mono (by omega))
  simpa only[low,outputLowStore,storeI64_host] using h
theorem tagged_credits(s:Store NearState)(op rest:Nat)(p:Layout)(hc:s.host.gas.Credits (20*op+rest)):
    (tagged s op p).host.gas.Credits (4*op+rest):=by
  have h:=paid_credits (low s op p) op 3 (4*op+rest) ((low_credits s op rest p hc).mono (by omega))
  simpa only[tagged,outputTagStore,storeI32_host] using h
theorem described_credits(s:Store NearState)(op rest:Nat)(p:Layout)(hc:s.host.gas.Credits (20*op+rest)):
    (described s op p).host.gas.Credits (op+rest):=by
  have h:=paid_credits (tagged s op p) op 3 (op+rest) ((tagged_credits s op rest p hc).mono (by omega))
  simpa only[described,StateDecodeScalar.store64Local,storeI64_host] using h
end WNear.Proofs.StateDecodePrefix.Output
