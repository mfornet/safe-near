import Bridge.Functions.SerdeStructObjPhaseReaders
import Bridge.Functions.SerdeObjectPrefix
import Bridge.Functions.SerdeObjectLedgerRoom

set_option maxRecDepth 100000

namespace WNear.Binary.SerdeObjectPrefix
open Wasm Wasm.Near NearInterface.Json
open WNear.Binary.ScratchMixedTrace
open WNear.Binary.SerdeObjectMixedTrace
open WNear.Binary.SerdeStructObjPhase (Phase)
open WNear.Binary.SerdeStructObjPhaseReaders (PhaseBounds)

/-- Actual prefix history constrains the concrete scratch coordinates at each phase. -/
def Bound (bs : List UInt8) (start baseHL baseF : Nat) (saved : Bool) : PhaseBounds :=
  fun phase i hl F cap => ∃ pre, Prefix bs start phase i pre saved ∧
    cap = endCap 0 pre ∧ F = endFreeBound baseF 0 pre ∧
    baseHL ≤ hl ∧ hl ≤ baseHL + 65536 * (pages 0 pre + if saved then 1 else 0)

theorem Bound.forget {bs : List UInt8} {start baseHL baseF i hl F : Nat} {saved : Bool}
    {phase : Phase} {cap : UInt32} (h : Bound bs start baseHL baseF saved phase i hl F cap) :
    Ledger bs baseHL baseF saved i hl F cap := by
  obtain ⟨pre, hp, hc, hf, hlo, hhi⟩ := h
  exact hp.ledger hc hf hlo hhi

theorem Bound.initial (bs : List UInt8) (start baseHL baseF : Nat) :
    Bound bs start baseHL baseF false (.member true) start baseHL baseF 0 := by
  refine ⟨[], .initial, rfl, rfl, le_rfl, ?_⟩
  simp [pages]

theorem Bound.segment (bs : List UInt8) (start baseHL baseF i j hl F hl' : Nat)
    (saved saved' : Bool) (phase next : Phase) (cap : UInt32) (seg : Segment) (extra : Nat)
    (hslot : (if saved then 1 else 0) + extra = (if saved' then 1 else 0))
    (hstep : ∀ pre, Prefix bs start phase i pre saved → Prefix bs start next j (pre ++ [seg]) saved')
    (h : Bound bs start baseHL baseF saved phase i hl F cap)
    (hlo : hl ≤ hl') (hhi : hl' ≤ hl + 65536 * (Segment.pages cap seg + extra)) :
    Bound bs start baseHL baseF saved' next j hl' (Segment.endFreeBound F cap seg) (Segment.next cap seg) := by
  obtain ⟨pre, hp, rfl, rfl, hb, hh⟩ := h
  refine ⟨pre ++ [seg], hstep pre hp, ?_, ?_, by omega, ?_⟩
  · simp only [Ledger.endCap_append, endCap]
  · simp only [Ledger.free_append, endFreeBound]
  · rw [Ledger.pages_append]
    simp only [pages, Nat.add_zero]
    simp only [Nat.mul_add] at hh hhi ⊢
    omega

theorem Bound.closing (bs : List UInt8) (start baseHL baseF : Nat) (saved : Bool) :
    SerdeStructObjPhaseReaders.ClosingConditions bs (Bound bs start baseHL baseF saved) := by
  intro first i j hl F cap hj hb h
  obtain ⟨pre, hp, hc, hf, hlo, hhi⟩ := h
  subst j
  exact ⟨pre, .close hp hb, hc, hf, hlo, hhi⟩

/-- Only the actual prefix key charge against its selected allowance remains to be funded. -/
def KeyGasCharges (cfg : WasmConfig) (bs : List UInt8) (B : PhaseBounds) (K : Nat → Nat) : Prop :=
  ∀ first i q key rest hl F cap, i ≤ bs.length → SerdeNextKey.keyQ first bs i = some q →
    stringBody (bs.drop q) [] = some (some key, rest) →
    B (.member first) i hl F cap → cap.toNat < 2 ^ 25 → hl % 65536 = 0 → 0 < hl →
    SerdeKeyReuse.preciseCost cfg F cap bs key.toUTF8.toList rest q ≤ K q

theorem Bound.key_conditions (cfg : WasmConfig) (bs : List UInt8) (start baseHL baseF : Nat)
    (saved : Bool) (K : Nat → Nat) (hlen : bs.length ≤ 4194304)
    (hbase : baseHL + 18230154 ≤ 100663296)
    (hgas : KeyGasCharges cfg bs (Bound bs start baseHL baseF saved) K) :
    SerdeStructObjPhaseReaders.KeyConditions cfg 2048 bs (Bound bs start baseHL baseF saved) K := by
  intro first i q key rest hl F cap hi hq hm hb hc hal hp
  refine ⟨Ledger.key_room bs baseHL baseF i hl F q saved cap key rest hlen hbase hb.forget hal hp hm,
    hgas first i q key rest hl F cap hi hq hm hb hc hal hp, ?_⟩
  intro hl' hlo hhi
  exact Bound.segment bs start baseHL baseF i (bs.length - rest.length) hl F hl' saved saved
    (.member first) (.value key) cap (.append (ParseStrSuccess.appendChunks (bs.drop q) [])) 0
    (by omega) (fun pre hpre => .key hpre hq hm) hb hlo (by simpa only [Segment.pages, Nat.add_zero, Nat.mul_comm] using hhi)
open WNear.Binary.SerdeRead (wsLen)
open WNear.Binary.ParseStrSuccess (appendChunks)

def ValueGasCharges (cfg : WasmConfig) (bs : List UInt8) (B : PhaseBounds) (K : Nat → Nat) : Prop :=
  ∀ i j a rest hl F cap, i ≤ bs.length → bs[i + wsLen (bs.drop i)]? = some 0x3A →
    j = i + wsLen (bs.drop i) + 1 + wsLen (bs.drop (i + wsLen (bs.drop i) + 1)) →
    bs[j]? = some 0x22 → stringBody (bs.drop (j + 1)) [] = some (some a.val, rest) →
    WNear.SerdeStructModel.valueAs WNear.account (bs.drop (i + wsLen (bs.drop i) + 1)) = some (a, rest) →
    B (.value "account_id") i hl F cap → cap.toNat < 2 ^ 25 → hl % 65536 = 0 → 0 < hl →
    SerdeValueReuse.valueCost cfg F cap bs a.val.toUTF8.toList rest (i + wsLen (bs.drop i) + 1) j ≤
      K (i + wsLen (bs.drop i) + 1)

theorem Bound.value_conditions (cfg : WasmConfig) (bs : List UInt8) (start baseHL baseF : Nat)
    (K : Nat → Nat) (hlen : bs.length ≤ 4194304) (hbase : baseHL + 18230154 ≤ 100663296)
    (hbaseF : 1 ≤ baseF) (hgas : ValueGasCharges cfg bs (Bound bs start baseHL baseF false) K) :
    SerdeStructObjPhaseReaders.ValueConditions cfg 2048 bs
      (Bound bs start baseHL baseF false) (Bound bs start baseHL baseF true) K := by
  intro i j a rest hl F cap hi hcolon hj hq hs hm hb hc hal hp
  obtain ⟨herr, hroom, halloc⟩ := Ledger.account_room bs baseHL baseF i hl F (j + 1) false cap a rest hlen hbase hb.forget hal hp hs
  refine ⟨herr, hroom, halloc, hgas i j a rest hl F cap hi hcolon hj hq hs hm hb hc hal hp, ?_⟩
  intro hl' hlo hhi
  have hp := account_id_page a
  have hF := Ledger.free_positive bs baseHL baseF i hl F false cap hbaseF hb.forget
  have hF' : 1 ≤ ScratchGrow.endFreeBound F cap 0 (appendChunks (bs.drop (j + 1)) []) := by
    rw [ScratchGrow.endFreeBound_eq]
    omega
  rw [max_eq_left hF']
  have hr := JsonSuffix.drop_suf' (JsonSuffix.stringBody_suf' hs)
  have hlenr := (JsonSuffix.valueAs_suf WNear.account hm).length_le
  simp only [List.length_drop] at hlenr
  have hvle := SerdeNextKey.getElem_lt hcolon
  apply Bound.segment bs start baseHL baseF i (bs.length - rest.length) hl F hl' false true
    (.value "account_id") (.member false) cap (.append (appendChunks (bs.drop (j + 1)) [])) 1 (by decide)
  · intro pre hpre
    have hv : ValueSegment bs "account_id" (bs.drop (i + wsLen (bs.drop i) + 1))
        (bs.length - rest.length) (.append (appendChunks (bs.drop (j + 1)) [])) :=
      .account _ j a rfl rfl hj hq (by simpa only [hr] using hm) (by simpa only [hr] using hs)
    simpa using Prefix.value hpre (fun _ => rfl) hcolon (by omega) (by omega) hv
  · exact hb
  · exact hlo
  · dsimp only [Segment.pages]
    omega

def IgnoreGasCharges (cfg : WasmConfig) (bs : List UInt8) (B : PhaseBounds) (K : Nat → Nat) : Prop :=
  ∀ key i hl F cap rest ops, key ≠ "account_id" → B (.value key) i hl F cap →
    cap.toNat < 2 ^ 25 → i ≤ bs.length → bs[i + wsLen (bs.drop i)]? = some 0x3A →
    SerdeIgnMachineTrace.trace (bs.drop (i + wsLen (bs.drop i) + 1)) = some (rest, ops) →
    hl % 65536 = 0 → 0 < hl →
    (166 + 470 * (bs.length - rest.length - (i + wsLen (bs.drop i) + 1))) * cfg.regularOpCost +
      SerdeIgnTrace.extraCost cfg F cap 0 ops ≤ K (i + wsLen (bs.drop i) + 1)

theorem Bound.ignore_conditions (cfg : WasmConfig) (bs : List UInt8) (start baseHL baseF : Nat)
    (saved : Bool) (K : Nat → Nat) (hlen : bs.length ≤ 4194304)
    (hbase : baseHL + 18230154 ≤ 100663296)
    (hgas : IgnoreGasCharges cfg bs (Bound bs start baseHL baseF saved) K) :
    SerdeStructObjPhaseReaders.IgnoreConditions cfg bs K (Bound bs start baseHL baseF saved) := by
  intro key i hl F cap rest ops hkey hb hc hi hcolon ht hal hp
  refine ⟨Ledger.heap_ceiling bs baseHL baseF i hl F saved cap hlen hbase hb.forget,
    hgas key i hl F cap rest ops hkey hb hc hi hcolon ht hal hp, ?_⟩
  intro hl' hh
  have hskip : WNear.IgnoreModel.vSkip (bs.drop (i + wsLen (bs.drop i) + 1)) = some rest := by
    rw [← SerdeIgnMachineTrace.erase_trace, ht]
    rfl
  have hr := JsonSuffix.drop_suf' (IgnoreShallow.vSkip_suf hskip)
  have hrlen := WNear.IgnoreModel.vSkip_length hskip
  simp only [List.length_drop] at hrlen
  have hvle := SerdeNextKey.getElem_lt hcolon
  have hheap := SerdeIgnExecution.heap_pages_bound hl cap 0 ops hl' hh
  apply Bound.segment bs start baseHL baseF i (bs.length - rest.length) hl F hl' saved saved
    (.value key) (.member false) cap (.frames ops) 0 (by omega)
  · intro pre hpre
    have hv : ValueSegment bs key (bs.drop (i + wsLen (bs.drop i) + 1))
        (bs.length - rest.length) (.frames ops) :=
      .ignored _ ops hkey rfl (by simpa only [hr] using ht)
    have hdup : key = "account_id" → saved = false := fun heq => False.elim (hkey heq)
    have hres := Prefix.value hpre hdup hcolon (by omega) (by omega) hv
    have hkfalse : (key == "account_id") = false := by simp [hkey]
    simpa only [hkfalse, Bool.or_false] using hres
  · exact hb
  · exact hheap.1
  · simpa only [Segment.pages, Nat.add_zero, Nat.mul_comm] using hheap.2.1

end WNear.Binary.SerdeObjectPrefix
