import Bridge.Functions.SerdeObjectMixedTrace
import Bridge.Functions.SerdeIgnObjectV86

namespace WNear.Binary.SerdeObjectMixedTrace
open Wasm Wasm.Near
open NearInterface.Json
open WNear.Binary.ScratchMixedTrace

open WNear.Binary.SerdeStructObjKeyState (Bounds)

namespace Ledger
end Ledger

/-- One retained scratch history and zero/one separately owned account allocation. -/
def Ledger (bs : List UInt8) (baseHL baseF : Nat) (saved : Bool) : Bounds :=
  fun _ hl F cap => ∃ batches, (∀ seg ∈ batches, SegmentModel bs seg) ∧
    cap = endCap 0 batches ∧ F = endFreeBound baseF 0 batches ∧
    baseHL ≤ hl ∧ hl ≤ baseHL + 65536 * (pages 0 batches + if saved then 1 else 0)

namespace Ledger

theorem endCap_append (cap : UInt32) (pre post : Batches) :
    endCap cap (pre ++ post) = endCap (endCap cap pre) post := by
  induction pre generalizing cap with
  | nil => rfl
  | cons seg pre ih => simpa only [List.cons_append, endCap] using ih (Segment.next cap seg)

theorem pages_append (cap : UInt32) (pre post : Batches) :
    pages cap (pre ++ post) = pages cap pre + pages (endCap cap pre) post := by
  induction pre generalizing cap with
  | nil => simp [pages, endCap]
  | cons seg pre ih => simp only [List.cons_append, pages, endCap, ih, Nat.add_assoc]

theorem free_append (F : Nat) (cap : UInt32) (pre post : Batches) :
    endFreeBound F cap (pre ++ post) = endFreeBound (endFreeBound F cap pre) (endCap cap pre) post := by
  induction pre generalizing F cap with
  | nil => rfl
  | cons seg pre ih => simpa only [List.cons_append, endFreeBound, endCap] using ih (Segment.endFreeBound F cap seg) (Segment.next cap seg)

theorem initial (bs : List UInt8) (baseHL baseF i : Nat) : Ledger bs baseHL baseF false i baseHL baseF 0 := by
  refine ⟨[], by simp, rfl, rfl, le_rfl, ?_⟩
  simp [pages]

set_option maxRecDepth 100000 in
theorem heap_ceiling (bs : List UInt8) (baseHL baseF i hl F : Nat) (saved : Bool) (cap : UInt32)
    (hlen : bs.length ≤ 4194304) (hbase : baseHL + 18230154 ≤ 100663296)
    (h : Ledger bs baseHL baseF saved i hl F cap) : hl ≤ 100663296 := by
  obtain ⟨batches, hm, _, _, _, hh⟩ := h
  have hp := scratch_pages bs batches hlen hm
  have hs : (if saved then (1 : Nat) else 0) ≤ 1 := by cases saved <;> decide
  simp only [Nat.mul_add] at hh
  omega

theorem closing (bs : List UInt8) (baseHL baseF : Nat) (saved : Bool) :
    SerdeStructObjModelState.ClosingConditions bs (Ledger bs baseHL baseF saved) := by
  intro i j hl F cap _ _ h
  exact h

theorem segment (bs : List UInt8) (baseHL baseF i j hl F hl' : Nat) (saved saved' : Bool) (cap : UInt32)
    (seg : Segment) (extra : Nat)
    (hslot : (if saved then 1 else 0) + extra = (if saved' then 1 else 0))
    (hm : SegmentModel bs seg) (h : Ledger bs baseHL baseF saved i hl F cap)
    (hlo : hl ≤ hl') (hhi : hl' ≤ hl + 65536 * (Segment.pages cap seg + extra)) :
    Ledger bs baseHL baseF saved' j hl' (Segment.endFreeBound F cap seg) (Segment.next cap seg) := by
  obtain ⟨pre, hmodels, rfl, rfl, hb, hh⟩ := h
  refine ⟨pre ++ [seg], ?_, ?_, ?_, by omega, ?_⟩
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hmodels x hx
    · have he := List.mem_singleton.mp hx
      subst x
      exact hm
  · simp only [endCap_append, endCap]
  · simp only [free_append, endFreeBound]
  · rw [pages_append]
    simp only [pages, Nat.add_zero]
    simp only [Nat.mul_add] at hh hhi ⊢
    omega

end Ledger


namespace Ledger

theorem ignored (bs : List UInt8) (baseHL baseF i q hl F hl' : Nat) (saved : Bool) (cap : UInt32)
    (rest : List UInt8) (ops : List Bool)
    (ht : SerdeIgnMachineTrace.trace (bs.drop q) = some (rest, ops))
    (h : Ledger bs baseHL baseF saved i hl F cap)
    (hh : SerdeIgnExecution.HeapTrace hl cap 0 ops hl') :
    Ledger bs baseHL baseF saved (bs.length - rest.length) hl'
      (SerdeIgnTrace.endFreeBound F cap 0 ops) (SerdeIgnTrace.endState cap 0 ops).1 := by
  have hp := SerdeIgnExecution.heap_pages_bound hl cap 0 ops hl' hh
  exact segment bs baseHL baseF i (bs.length - rest.length) hl F hl' saved saved cap (.frames ops) 0
    (by omega) (.ignored q rest ops ht) h hp.1 (by simpa only [Segment.pages, Nat.add_zero] using hp.2.1)

end Ledger

/-- Only the ignored-reader gas allowance; room and state transport are supplied by the ledger. -/
def IgnoreCharges (cfg : WasmConfig) (bs : List UInt8) (K : Nat → Nat) (B : Bounds) : Prop :=
  ∀ i hl F cap rest ops, B i hl F cap → cap.toNat < 2 ^ 25 → i ≤ bs.length →
    bs[i + SerdeRead.wsLen (bs.drop i)]? = some 0x3A →
    SerdeIgnMachineTrace.trace (bs.drop (i + SerdeRead.wsLen (bs.drop i) + 1)) = some (rest, ops) →
    hl % 65536 = 0 → 0 < hl →
    (166 + 470 * (bs.length - rest.length - (i + SerdeRead.wsLen (bs.drop i) + 1))) * cfg.regularOpCost +
      SerdeIgnTrace.extraCost cfg F cap 0 ops ≤ K (i + SerdeRead.wsLen (bs.drop i) + 1)

namespace Ledger

set_option maxRecDepth 100000 in
theorem ignore_conditions (cfg : WasmConfig) (bs : List UInt8) (baseHL baseF : Nat) (saved : Bool)
    (K : Nat → Nat) (hlen : bs.length ≤ 4194304) (hbase : baseHL + 18230154 ≤ 100663296)
    (hcharges : IgnoreCharges cfg bs K (Ledger bs baseHL baseF saved)) :
    SerdeIgnObject.ReachableIgnoreConditions cfg bs K (Ledger bs baseHL baseF saved) := by
  intro i hl F cap rest ops hb hcap hi hcolon ht halign hpositive
  refine ⟨heap_ceiling bs baseHL baseF i hl F saved cap hlen hbase hb,
    hcharges i hl F cap rest ops hb hcap hi hcolon ht halign hpositive, ?_⟩
  intro hl' hh
  exact ignored bs baseHL baseF i (i + SerdeRead.wsLen (bs.drop i) + 1) hl F hl' saved cap rest ops ht hb hh

end Ledger


open WNear.Binary.SerdeRead (wsLen)
open WNear.Binary.SerdeNextKey (keyQ)
open WNear.Binary.ScratchGrow (growthPages endFreeBound endState)
open WNear.Binary.ParseStrSuccess (appendChunks)
open WNear.Binary.VecFromElem (roomFor)

def KeyRoomCharges (cfg : WasmConfig) (maxP : Nat) (bs : List UInt8) (B : Bounds) (K : Nat → Nat) : Prop :=
  ∀ (first : Bool) (i q : Nat) (key : String) (rest : List UInt8) (hl F : Nat) (cap : UInt32),
    i ≤ bs.length → SerdeNextKey.keyQ first bs i = some q →
    NearInterface.Json.stringBody (bs.drop q) [] = some (some key, rest) → B i hl F cap → cap.toNat < 2 ^ 25 → hl % 65536 = 0 → 0 < hl →
    SerdeKeyReuse.keyRoom maxP hl cap (bs.drop q) ∧ SerdeKeyReuse.keyCost cfg F cap bs key.toUTF8.toList rest q ≤ K q

def ValueRoomCharges (cfg : WasmConfig) (maxP : Nat) (bs : List UInt8) (B : Bounds) (K : Nat → Nat) : Prop :=
  ∀ (i j : Nat) (a : WNear.AccountId) (rest : List UInt8) (hl F : Nat) (cap : UInt32),
    i ≤ bs.length → bs[i + wsLen (bs.drop i)]? = some 0x3A →
    j = i + wsLen (bs.drop i) + 1 + wsLen (bs.drop (i + wsLen (bs.drop i) + 1)) →
    bs[j]? = some 0x22 → stringBody (bs.drop (j + 1)) [] = some (some a.val, rest) →
    B i hl F cap → cap.toNat < 2 ^ 25 → hl % 65536 = 0 → 0 < hl →
    SerdeErrBox.roomFor4 hl maxP 20 ∧ ParseStr.roomRun maxP hl cap [] (bs.drop (j + 1)) ∧
    roomFor (hl + growthPages cap 0 (appendChunks (bs.drop (j + 1)) []) * 65536)
      maxP (UInt32.ofNat a.val.toUTF8.toList.length) ∧
    SerdeValueReuse.valueCost cfg F cap bs a.val.toUTF8.toList rest (i + wsLen (bs.drop i) + 1) j ≤
      K (i + wsLen (bs.drop i) + 1)

namespace Ledger

theorem key_conditions (cfg : WasmConfig) (bs : List UInt8) (baseHL baseF : Nat) (saved : Bool)
    (K : Nat → Nat) (hcharges : KeyRoomCharges cfg 2048 bs (Ledger bs baseHL baseF saved) K) :
    SerdeStructObjKeyState.KeyConditions cfg 2048 bs (Ledger bs baseHL baseF saved) K := by
  intro first i q key rest hl F cap hi hq hs hb hcap halign hpositive
  obtain ⟨hr, hgas⟩ := hcharges first i q key rest hl F cap hi hq hs hb hcap halign hpositive
  refine ⟨hr, hgas, ?_⟩
  intro hl' hlo hhi
  exact segment bs baseHL baseF i (bs.length - rest.length) hl F hl' saved saved cap
    (.append (appendChunks (bs.drop q) [])) 0 (by omega) (.string q key rest hs) hb hlo
    (by simpa only [Segment.pages, Nat.add_zero, Nat.mul_comm] using hhi)

theorem free_positive (bs : List UInt8) (baseHL baseF i hl F : Nat) (saved : Bool) (cap : UInt32)
    (hbase : 1 ≤ baseF) (h : Ledger bs baseHL baseF saved i hl F cap) : 1 ≤ F := by
  obtain ⟨batches, _, _, rfl, _, _⟩ := h
  rw [ScratchMixedTrace.endFreeBound_eq]
  omega

theorem value_conditions (cfg : WasmConfig) (bs : List UInt8) (baseHL baseF : Nat)
    (K : Nat → Nat) (hbaseF : 1 ≤ baseF)
    (hcharges : ValueRoomCharges cfg 2048 bs (Ledger bs baseHL baseF false) K) :
    SerdeStructObjValueState.ValueConditions cfg 2048 bs (Ledger bs baseHL baseF false) (Ledger bs baseHL baseF true) K := by
  intro i j a rest hl F cap hi hcolon hj hquote hs hb hcap halign hpositive
  obtain ⟨hr, hroom, halloc, hgas⟩ := hcharges i j a rest hl F cap hi hcolon hj hquote hs hb hcap halign hpositive
  refine ⟨hr, hroom, halloc, hgas, ?_⟩
  intro hl' hlo hhi
  have hp := account_id_page a
  have hF : 1 ≤ F := free_positive bs baseHL baseF i hl F false cap hbaseF hb
  have hF' : 1 ≤ ScratchGrow.endFreeBound F cap 0 (appendChunks (bs.drop (j + 1)) []) := by
    rw [ScratchGrow.endFreeBound_eq]
    omega
  rw [max_eq_left hF']
  exact segment bs baseHL baseF i (bs.length - rest.length) hl F hl' false true cap
    (.append (appendChunks (bs.drop (j + 1)) [])) 1 (by decide) (.string (j + 1) a.val rest hs) hb hlo
    (by dsimp only [Segment.pages]; omega)

end Ledger



end WNear.Binary.SerdeObjectMixedTrace
