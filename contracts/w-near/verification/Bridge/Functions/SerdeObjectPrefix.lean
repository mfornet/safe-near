import Bridge.Functions.SerdeObjectLedger
import Bridge.Functions.SerdeStructObjPhase

namespace WNear.Binary.SerdeObjectPrefix
open Wasm Wasm.Near NearInterface.Json
open WNear.Binary.ScratchMixedTrace
open WNear.Binary.SerdeObjectMixedTrace
open WNear.Binary.SerdeStructObjPhase (Phase)

/-- Actual successful field prefixes, including the pending field name and retained scratch history. -/
inductive Prefix (bs : List UInt8) (start : Nat) : Phase → Nat → Batches → Bool → Prop
  | initial : Prefix bs start (.member true) start [] false
  | key {first : Bool} {i q : Nat} {key : String} {rest : List UInt8} {pre : Batches} {saved : Bool}
      (hpre : Prefix bs start (.member first) i pre saved)
      (hq : SerdeNextKey.keyQ first bs i = some q)
      (hs : stringBody (bs.drop q) [] = some (some key, rest)) :
      Prefix bs start (.value key) (bs.length - rest.length)
        (pre ++ [.append (ParseStrSuccess.appendChunks (bs.drop q) [])]) saved
  | value {key : String} {i e : Nat} {pre : Batches} {saved : Bool} {seg : Segment}
      (hpre : Prefix bs start (.value key) i pre saved)
      (hdup : key = "account_id" → saved = false)
      (hc : bs[i + SerdeRead.wsLen (bs.drop i)]? = some 0x3A)
      (he : i + SerdeRead.wsLen (bs.drop i) + 1 ≤ e) (heb : e ≤ bs.length)
      (hv : ValueSegment bs key (bs.drop (i + SerdeRead.wsLen (bs.drop i) + 1)) e seg) :
      Prefix bs start (.member false) e (pre ++ [seg]) (saved || key == "account_id")
  | close {first : Bool} {i : Nat} {pre : Batches} {saved : Bool}
      (hpre : Prefix bs start (.member first) i pre saved)
      (hb : bs[i + SerdeRead.wsLen (bs.drop i)]? = some 0x7D) :
      Prefix bs start .done (i + SerdeRead.wsLen (bs.drop i) + 1) pre saved

/-- Every retained segment comes from the corresponding actual successful reader model. -/
theorem Prefix.models {bs : List UInt8} {start i : Nat} {phase : Phase} {pre : Batches} {saved : Bool}
    (h : Prefix bs start phase i pre saved) : ∀ seg ∈ pre, SegmentModel bs seg := by
  induction h with
  | initial => simp
  | key hpre hq hs ih =>
    intro seg hseg
    rcases List.mem_append.mp hseg with hseg | hseg
    · exact ih seg hseg
    · have heq := List.mem_singleton.mp hseg
      subst seg
      exact .string _ _ _ hs
  | value hpre hdup hc he heb hv ih =>
    intro seg hseg
    rcases List.mem_append.mp hseg with hseg | hseg
    · exact ih seg hseg
    · have heq := List.mem_singleton.mp hseg
      subst seg
      exact value_segment_model hv
  | close hpre hb ih => exact ih

/-- The prefix witness specializes the existing coarse physical ledger without changing its bound. -/
theorem Prefix.ledger {bs : List UInt8} {start i baseHL baseF hl F : Nat} {phase : Phase}
    {pre : Batches} {saved : Bool} {cap : UInt32}
    (h : Prefix bs start phase i pre saved)
    (hcap : cap = endCap 0 pre) (hfree : F = endFreeBound baseF 0 pre)
    (hlo : baseHL ≤ hl)
    (hhi : hl ≤ baseHL + 65536 * (pages 0 pre + if saved then 1 else 0)) :
    Ledger bs baseHL baseF saved i hl F cap :=
  ⟨pre, h.models, hcap, hfree, hlo, hhi⟩

/-- Initial history is available at the initial member phase and exact body cursor. -/
theorem initial_ledger (bs : List UInt8) (start baseHL baseF : Nat) :
    ∃ pre, Prefix bs start (.member true) start pre false ∧
      (0 : UInt32) = endCap 0 pre ∧ baseF = endFreeBound baseF 0 pre ∧
      Ledger bs baseHL baseF false start baseHL baseF 0 := by
  exact ⟨[], .initial, rfl, rfl, Ledger.initial bs baseHL baseF start⟩
/-- The first-member phase cannot be reintroduced at an arbitrary later cursor. -/
theorem Prefix.first_exact {bs : List UInt8} {start i : Nat} {pre : Batches} {saved : Bool}
    (h : Prefix bs start (.member true) i pre saved) :
    i = start ∧ pre = [] ∧ saved = false := by
  cases h
  exact ⟨rfl, rfl, rfl⟩

/-- A pending field has an actual key read immediately before it, with the retained prefix extended once. -/
theorem Prefix.pending_key {bs : List UInt8} {start i : Nat} {key : String} {pre : Batches} {saved : Bool}
    (h : Prefix bs start (.value key) i pre saved) :
    ∃ (first : Bool) (j q : Nat) (rest : List UInt8) (before : Batches),
      Prefix bs start (.member first) j before saved ∧
      SerdeNextKey.keyQ first bs j = some q ∧
      stringBody (bs.drop q) [] = some (some key, rest) ∧
      i = bs.length - rest.length ∧
      pre = before ++ [.append (ParseStrSuccess.appendChunks (bs.drop q) [])] := by
  cases h with
  | key hpre hq hs => exact ⟨_, _, _, _, _, hpre, hq, hs, rfl, rfl⟩

end WNear.Binary.SerdeObjectPrefix
