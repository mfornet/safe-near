import Bridge.Functions.SerdeObjectLedgerComposition
import Bridge.Functions.StrPageRoom
import Bridge.Functions.StrRetainedRoom

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace WNear.Binary.SerdeObjectMixedTrace
open Wasm Wasm.Near
open NearInterface.Json
open WNear.Binary.SerdeStructObjKeyState (Bounds)
open WNear.Binary.SerdeRead (wsLen)
open WNear.Binary.ScratchMixedTrace

theorem Ledger.append_pages_bound (bs : List UInt8) (baseHL baseF i hl F q : Nat) (saved : Bool)
    (cap : UInt32) (value : String) (rest : List UInt8) (hlen : bs.length ≤ 4194304)
    (h : Ledger bs baseHL baseF saved i hl F cap)
    (hm : stringBody (bs.drop q) [] = some (some value, rest)) :
    65536 * ScratchGrow.growthPages cap 0 (ParseStrSuccess.appendChunks (bs.drop q) []) ≤ 18164618 := by
  obtain ⟨batches, hs, hc, _, _, _⟩ := h
  let seg := Segment.append (ParseStrSuccess.appendChunks (bs.drop q) [])
  have hv : SegmentModel bs seg := SegmentModel.string q value rest hm
  have hall : ∀ s ∈ batches ++ [seg], SegmentModel bs s := by
    intro s hin
    rcases List.mem_append.mp hin with hin | hin
    · exact hs s hin
    · simp only [List.mem_singleton] at hin
      subst s
      exact hv
  have hp := scratch_pages bs (batches ++ [seg]) hlen hall
  rw [Ledger.pages_append] at hp
  simp only [pages, Segment.pages, Nat.add_zero] at hp
  change 65536 * (pages 0 batches + ScratchGrow.growthPages (endCap 0 batches) 0
    (ParseStrSuccess.appendChunks (bs.drop q) [])) ≤ 18164618 at hp
  rw [← hc] at hp
  omega

theorem Ledger.account_room (bs : List UInt8) (baseHL baseF i hl F q : Nat) (saved : Bool)
    (cap : UInt32) (a : WNear.AccountId) (rest : List UInt8) (hlen : bs.length ≤ 4194304)
    (hbase : baseHL + 18230154 ≤ 100663296)
    (h : Ledger bs baseHL baseF saved i hl F cap) (hal : hl % 65536 = 0) (hpos : 0 < hl)
    (hm : stringBody (bs.drop q) [] = some (some a.val, rest)) :
    SerdeErrBox.roomFor4 hl 2048 20 ∧ ParseStr.roomRun 2048 hl cap [] (bs.drop q) ∧
      VecFromElem.roomFor (hl + ScratchGrow.growthPages cap 0 (ParseStrSuccess.appendChunks (bs.drop q) []) * 65536)
        2048 (UInt32.ofNat a.val.toUTF8.toList.length) := by
  have hh := Ledger.heap_ceiling bs baseHL baseF i hl F saved cap hlen hbase h
  have hr : LookupMapOps.HeapRoomK 131 hl 2048 := ⟨hal, hpos, by omega, by omega⟩
  have hv := a.toNear.property
  change validAccountIdBytes a.val.toUTF8.toList = true at hv
  simp only [validAccountIdBytes, Bool.and_eq_true, decide_eq_true_eq] at hv
  have hs : a.val.toUTF8.toList.length ≤ 64 := by omega
  obtain ⟨hok, _⟩ := SerdeAccountIdEsc.strRun_of_stringBody _ _ _ hm
  have hrun := ParseStrRoom.roomRun_short_any 2048 hl cap [] (bs.drop q) a.val.toUTF8.toList rest
    (by simp) hs hok (ParseStrRoom.heap_room_mono hr (by simp only [List.length_nil, Nat.sub_zero]; omega))
  refine ⟨ParseStrRoom.error_room hr (by decide), hrun, ?_⟩
  have hp := Ledger.append_pages_bound bs baseHL baseF i hl F q saved cap a.val rest hlen h hm
  have hsize : (UInt32.ofNat a.val.toUTF8.toList.length).toNat ≤ 64 := (Nat.mod_le _ _).trans hs
  have hpage := ScratchMixedTrace.account_page _ hsize
  unfold VecFromElem.roomFor
  refine ⟨?_, by omega, by omega, by omega⟩
  simpa [Nat.add_mod, Nat.mul_mod] using hal

def ValueGasCharges (cfg : WasmConfig) (bs : List UInt8) (B : Bounds) (K : Nat → Nat) : Prop :=
  ∀ (i j : Nat) (a : WNear.AccountId) (rest : List UInt8) (hl F : Nat) (cap : UInt32),
    i ≤ bs.length → bs[i + wsLen (bs.drop i)]? = some 0x3A →
    j = i + wsLen (bs.drop i) + 1 + wsLen (bs.drop (i + wsLen (bs.drop i) + 1)) →
    bs[j]? = some 0x22 → stringBody (bs.drop (j + 1)) [] = some (some a.val, rest) →
    B i hl F cap → cap.toNat < 2 ^ 25 → hl % 65536 = 0 → 0 < hl →
    SerdeValueReuse.valueCost cfg F cap bs a.val.toUTF8.toList rest (i + wsLen (bs.drop i) + 1) j ≤
      K (i + wsLen (bs.drop i) + 1)

/-- All account reader room comes from the actual ledger; only its gas witness is assumed. -/
theorem Ledger.value_charges (cfg : WasmConfig) (bs : List UInt8) (baseHL baseF : Nat)
    (K : Nat → Nat) (hlen : bs.length ≤ 4194304) (hbase : baseHL + 18230154 ≤ 100663296)
    (hgas : ValueGasCharges cfg bs (Ledger bs baseHL baseF false) K) :
    ValueRoomCharges cfg 2048 bs (Ledger bs baseHL baseF false) K := by
  intro i j a rest hl F cap hi hcolon hj hq hm hb hc hal hp
  obtain ⟨herr, hrun, halloc⟩ := Ledger.account_room bs baseHL baseF i hl F (j + 1) false cap a rest hlen hbase hb hal hp hm
  exact ⟨herr, hrun, halloc, hgas i j a rest hl F cap hi hcolon hj hq hm hb hc hal hp⟩

end WNear.Binary.SerdeObjectMixedTrace

namespace WNear.Binary.SerdeObjectMixedTrace
open Wasm Wasm.Near
open NearInterface.Json
open WNear.Binary.SerdeStructObjKeyState (Bounds)
open WNear.Binary.SerdeRead (wsLen)
open WNear.Binary.ScratchMixedTrace

theorem Ledger.key_room (bs : List UInt8) (baseHL baseF i hl F q : Nat) (saved : Bool)
    (cap : UInt32) (key : String) (rest : List UInt8) (hlen : bs.length ≤ 4194304)
    (hbase : baseHL + 18230154 ≤ 100663296)
    (h : Ledger bs baseHL baseF saved i hl F cap) (hal : hl % 65536 = 0) (hpos : 0 < hl)
    (hm : stringBody (bs.drop q) [] = some (some key, rest)) :
    SerdeKeyReuse.keyRoom 2048 hl cap (bs.drop q) := by
  have hh := Ledger.heap_ceiling bs baseHL baseF i hl F saved cap hlen hbase h
  by_cases hb : ParseStr.borrowed (bs.drop q)
  · simp only [SerdeKeyReuse.keyRoom, if_pos hb]
    apply ParseStrRoom.error_room (show LookupMapOps.HeapRoomK 1 hl 2048 from ?_) (by decide)
    exact ⟨hal, hpos, by omega, by omega⟩
  · simp only [SerdeKeyReuse.keyRoom, if_neg hb]
    obtain ⟨hok, _⟩ := SerdeAccountIdEsc.strRun_of_stringBody _ _ _ hm
    have hp := Ledger.append_pages_bound bs baseHL baseF i hl F q saved cap key rest hlen h hm
    have he := ParseStrRoom.roomChunks_copied (bs.drop q) [] key.toUTF8.toList rest hok (Or.inr hb)
    apply ParseStrRoom.roomRun_pages 2048 hl cap [] (bs.drop q) key.toUTF8.toList rest hok
    rw [he]
    change LookupMapOps.HeapRoomK (ScratchGrow.growthPages cap 0 (ParseStrSuccess.appendChunks (bs.drop q) []) + 1) hl 2048
    refine ⟨hal, hpos, ?_, ?_⟩ <;> omega

def KeyGasCharges (cfg : WasmConfig) (bs : List UInt8) (B : Bounds) (K : Nat → Nat) : Prop :=
  ∀ (first : Bool) (i q : Nat) (key : String) (rest : List UInt8) (hl F : Nat) (cap : UInt32),
    i ≤ bs.length → SerdeNextKey.keyQ first bs i = some q →
    NearInterface.Json.stringBody (bs.drop q) [] = some (some key, rest) → B i hl F cap → cap.toNat < 2 ^ 25 → hl % 65536 = 0 → 0 < hl →
    SerdeKeyReuse.keyCost cfg F cap bs key.toUTF8.toList rest q ≤ K q


/-- Concrete key room leaves only the chosen actual key gas allowance unresolved. -/
theorem Ledger.key_charges (cfg : WasmConfig) (bs : List UInt8) (baseHL baseF : Nat) (saved : Bool)
    (K : Nat → Nat) (hlen : bs.length ≤ 4194304) (hbase : baseHL + 18230154 ≤ 100663296)
    (hgas : KeyGasCharges cfg bs (Ledger bs baseHL baseF saved) K) :
    KeyRoomCharges cfg 2048 bs (Ledger bs baseHL baseF saved) K := by
  intro first i q key rest hl F cap hi hq hm hb hc hal hp
  exact ⟨Ledger.key_room bs baseHL baseF i hl F q saved cap key rest hlen hbase hb hal hp hm,
    hgas first i q key rest hl F cap hi hq hm hb hc hal hp⟩

end WNear.Binary.SerdeObjectMixedTrace
