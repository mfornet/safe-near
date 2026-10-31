import Bridge.Functions.SerdeObjectPrefix
import Bridge.Functions.SerdeKeyPrecise

set_option maxRecDepth 100000

namespace WNear.Binary.SerdeObjectPrefix
open Wasm Wasm.Near NearInterface.Json
open WNear.Binary.ScratchMixedTrace
open WNear.Binary.SerdeStructObjPhase (Phase)

/-- Each retained key/value segment advances the actual cursor by at least one byte. -/
theorem Prefix.progress {bs : List UInt8} {start i : Nat} {phase : Phase} {pre : Batches} {saved : Bool}
    (h : Prefix bs start phase i pre saved) : start + pre.length ≤ i := by
  induction h with
  | initial => simp
  | key hpre hq hs ih =>
    have hstrict := SerdeObjectCoverage.keyQ_strict hq
    have hqle := SerdeStructObj.keyQ_le hq
    have hslen := (JsonSuffix.stringBody_suf' hs).length_le
    simp only [List.length_drop] at hslen
    simp only [List.length_append, List.length_singleton]
    omega
  | value hpre hdup hc he heb hv ih =>
    simp only [List.length_append, List.length_singleton]
    omega
  | close hpre hb ih => omega

/-- A successful prefix can retain only finitely many segments within the actual consumed bytes. -/
theorem Prefix.history_length {bs : List UInt8} {start i : Nat} {phase : Phase} {pre : Batches} {saved : Bool}
    (h : Prefix bs start phase i pre saved) : start ≤ i ∧ pre.length ≤ i - start := by
  have hp := h.progress
  omega

open WNear.Binary.SerdeRead (wsLen)

/-- One executable pure parser transition, used only to select the actual prefix history. -/
def step (bs : List UInt8) : Phase → Nat → Bool → Option (Phase × Nat × Option Segment × Bool)
  | .member first, i, saved =>
    if bs[i + wsLen (bs.drop i)]? = some 0x7D then
      some (.done, i + wsLen (bs.drop i) + 1, none, saved)
    else do
      let q ← SerdeNextKey.keyQ first bs i
      let (decoded, rest) ← stringBody (bs.drop q) []
      let key ← decoded
      pure (.value key, bs.length - rest.length,
        some (.append (ParseStrSuccess.appendChunks (bs.drop q) [])), saved)
  | .value key, i, saved =>
    if bs[i + wsLen (bs.drop i)]? = some 0x3A then
      let v := i + wsLen (bs.drop i) + 1
      if key = "account_id" then
        if saved then none else do
          let (_, rest) ← WNear.SerdeStructModel.valueAs WNear.account (bs.drop v)
          pure (.member false, bs.length - rest.length,
            some (.append (ParseStrSuccess.appendChunks (bs.drop (v + wsLen (bs.drop v) + 1)) [])), true)
      else do
        let (rest, ops) ← SerdeIgnMachineTrace.trace (bs.drop v)
        pure (.member false, bs.length - rest.length, some (.frames ops), saved)
    else none
  | .done, _, _ => none

theorem step_key {bs : List UInt8} {first : Bool} {i q : Nat} {key : String} {rest : List UInt8}
    (saved : Bool) (hq : SerdeNextKey.keyQ first bs i = some q)
    (hs : stringBody (bs.drop q) [] = some (some key, rest)) :
    step bs (.member first) i saved = some (.value key, bs.length - rest.length,
      some (.append (ParseStrSuccess.appendChunks (bs.drop q) [])), saved) := by
  have hn : bs[i + wsLen (bs.drop i)]? ≠ some 0x7D := by
    intro hc
    cases first <;> simp [SerdeNextKey.keyQ, hc] at hq
  simp [step, hn, hq, hs]

theorem step_close {bs : List UInt8} {first : Bool} {i : Nat} (saved : Bool)
    (hb : bs[i + wsLen (bs.drop i)]? = some 0x7D) :
    step bs (.member first) i saved = some (.done, i + wsLen (bs.drop i) + 1, none, saved) := by
  simp [step, hb]

theorem step_value {bs : List UInt8} {key : String} {i e : Nat} {seg : Segment} (saved : Bool)
    (hdup : key = "account_id" → saved = false)
    (hc : bs[i + wsLen (bs.drop i)]? = some 0x3A) (heb : e ≤ bs.length)
    (hv : SerdeObjectMixedTrace.ValueSegment bs key (bs.drop (i + wsLen (bs.drop i) + 1)) e seg) :
    step bs (.value key) i saved = some (.member false, e, some seg, saved || key == "account_id") := by
  have hcolon := SerdeNextKey.getElem_lt hc
  have he : bs.length - (bs.drop e).length = e := by simp only [List.length_drop]; omega
  cases hv with
  | account v j a hk hin hj hq hm hs =>
    have hquote := SerdeNextKey.getElem_lt hq
    have hvlen := congrArg List.length hin
    simp only [List.length_drop] at hvlen
    have hvEq : v = i + wsLen (bs.drop i) + 1 := by omega
    subst v
    subst key
    have hsave := hdup rfl
    subst saved
    subst j
    simp [step, hc, hm, he]
    omega
  | ignored v ops hk hin ht =>
    have hskip : WNear.IgnoreModel.vSkip (bs.drop v) = some (bs.drop e) := by
      rw [← SerdeIgnMachineTrace.erase_trace, ht]
      rfl
    have hstrict := IgnoreShallow.vSkip_strict hskip
    simp only [List.length_drop] at hstrict
    have hvlen := congrArg List.length hin
    simp only [List.length_drop] at hvlen
    have hvEq : v = i + wsLen (bs.drop i) + 1 := by omega
    subst v
    simp [step, hc, hk, ht, he]
    omega

abbrev TraceState := Phase × Nat × Batches × Bool

def advance (bs : List UInt8) (st : TraceState) : Option TraceState := do
  let (phase, i, segment, saved) ← step bs st.1 st.2.1 st.2.2.2
  pure (phase, i, st.2.2.1 ++ segment.toList, saved)

def trajectory (bs : List UInt8) (start : Nat) : Nat → Option TraceState
  | 0 => some (.member true, start, [], false)
  | n + 1 => (trajectory bs start n).bind (advance bs)

/-- Every modeled prefix is the corresponding finite state of one functional actual-reader trace. -/
theorem Prefix.canonical_trace {bs : List UInt8} {start i : Nat} {phase : Phase} {pre : Batches} {saved : Bool}
    (h : Prefix bs start phase i pre saved) :
    trajectory bs start (pre.length + if phase = .done then 1 else 0) = some (phase, i, pre, saved) := by
  induction h with
  | initial => simp [trajectory]
  | key hpre hq hs ih =>
    simp only [reduceCtorEq, ite_false, Nat.add_zero] at ih ⊢
    simp [trajectory, ih, advance, step_key _ hq hs]
  | value hpre hdup hc he heb hv ih =>
    simp only [reduceCtorEq, ite_false, Nat.add_zero] at ih ⊢
    simp [trajectory, ih, advance, step_value _ hdup hc heb hv]
  | close hpre hb ih =>
    simp only [reduceCtorEq, ite_false, Nat.add_zero] at ih
    simp [trajectory, ih, advance, step_close _ hb]

theorem before_succ {bs : List UInt8} {start n current : Nat} {previous : TraceState}
    (hp : trajectory bs start n = some previous) (hstrict : previous.2.1 < current)
    (hb : ∀ m st, m < n → trajectory bs start m = some st → st.2.1 < previous.2.1) :
    ∀ m st, m < n + 1 → trajectory bs start m = some st → st.2.1 < current := by
  intro m st hm ht
  by_cases hmn : m < n
  · have h := hb m st hmn ht
    omega
  · have heq : m = n := by omega
    subst m
    have hst := Option.some.inj (hp.symm.trans ht)
    subst st
    exact hstrict

/-- Every earlier state in the functional trace has a strictly smaller cursor. -/
theorem Prefix.before_index {bs : List UInt8} {start i : Nat} {phase : Phase} {pre : Batches} {saved : Bool}
    (h : Prefix bs start phase i pre saved) :
    ∀ n st, n < pre.length + (if phase = .done then 1 else 0) →
      trajectory bs start n = some st → st.2.1 < i := by
  induction h with
  | initial => simp
  | key hpre hq hs ih =>
    simp only [reduceCtorEq, ite_false, Nat.add_zero, List.length_append, List.length_singleton] at ih ⊢
    apply before_succ (by simpa using hpre.canonical_trace)
    · have hstrict := SerdeObjectCoverage.keyQ_strict hq
      have hqle := SerdeStructObj.keyQ_le hq
      have hlen := (JsonSuffix.stringBody_suf' hs).length_le
      simp only [List.length_drop] at hlen
      dsimp only
      omega
    · exact ih
  | value hpre hdup hc he heb hv ih =>
    simp only [reduceCtorEq, ite_false, Nat.add_zero, List.length_append, List.length_singleton] at ih ⊢
    apply before_succ (by simpa using hpre.canonical_trace)
    · dsimp only; omega
    · exact ih
  | close hpre hb ih =>
    simp only [reduceCtorEq, ite_true, ite_false, Nat.add_zero] at ih ⊢
    apply before_succ (by simpa using hpre.canonical_trace)
    · dsimp only; omega
    · exact ih

/-- A cursor reached by actual prefixes determines its phase, retained history and saved-account flag. -/
theorem Prefix.unique_at_cursor {bs : List UInt8} {start i : Nat} {phase phase' : Phase}
    {pre pre' : Batches} {saved saved' : Bool}
    (h : Prefix bs start phase i pre saved) (h' : Prefix bs start phase' i pre' saved') :
    phase = phase' ∧ pre = pre' ∧ saved = saved' := by
  have ht := h.canonical_trace
  have ht' := h'.canonical_trace
  have hn : pre.length + (if phase = .done then 1 else 0) =
      pre'.length + (if phase' = .done then 1 else 0) := by
    rcases lt_trichotomy (pre.length + if phase = .done then 1 else 0)
        (pre'.length + if phase' = .done then 1 else 0) with hl | he | hr
    · have hc := h'.before_index _ _ hl ht
      dsimp only at hc
      omega
    · exact he
    · have hc := h.before_index _ _ hr ht'
      dsimp only at hc
      omega
  rw [hn] at ht
  have heq := Option.some.inj (ht.symm.trans ht')
  exact ⟨congrArg Prod.fst heq, congrArg (fun x => x.2.2.1) heq, congrArg (fun x => x.2.2.2) heq⟩

theorem Prefix.key_no_later_start {bs : List UInt8} {start i i' q : Nat} {first first' : Bool}
    {pre pre' : Batches} {saved saved' : Bool} {key : String} {rest : List UInt8}
    (h : Prefix bs start (.member first) i pre saved)
    (h' : Prefix bs start (.member first') i' pre' saved')
    (hq : SerdeNextKey.keyQ first bs i = some q)
    (hq' : SerdeNextKey.keyQ first' bs i' = some q)
    (hs : stringBody (bs.drop q) [] = some (some key, rest))
    (hlt : pre.length < pre'.length) : False := by
  have hnext := Prefix.key h hq hs
  have ht := hnext.canonical_trace
  have ht' := h'.canonical_trace
  simp only [reduceCtorEq, ite_false, Nat.add_zero, List.length_append, List.length_singleton] at ht ht'
  have hqstrict := SerdeObjectCoverage.keyQ_strict hq'
  have hqle := SerdeStructObj.keyQ_le hq
  have hrlen := (JsonSuffix.stringBody_suf' hs).length_le
  simp only [List.length_drop] at hrlen
  have hle : pre.length + 1 ≤ pre'.length := by omega
  rcases lt_or_eq_of_le hle with hl | he
  · have hc := h'.before_index _ _ (by simpa using hl) ht
    dsimp only at hc
    omega
  · rw [he] at ht
    have heq := Option.some.inj (ht.symm.trans ht')
    have hecur := congrArg (fun x => x.2.1) heq
    dsimp only at hecur
    omega

/-- A key-body charge index determines the exact retained scratch history of its actual caller. -/
theorem Prefix.key_history_unique {bs : List UInt8} {start i i' q : Nat} {first first' : Bool}
    {pre pre' : Batches} {saved saved' : Bool} {key key' : String} {rest rest' : List UInt8}
    (h : Prefix bs start (.member first) i pre saved)
    (h' : Prefix bs start (.member first') i' pre' saved')
    (hq : SerdeNextKey.keyQ first bs i = some q) (hq' : SerdeNextKey.keyQ first' bs i' = some q)
    (hs : stringBody (bs.drop q) [] = some (some key, rest))
    (hs' : stringBody (bs.drop q) [] = some (some key', rest')) : pre = pre' ∧ saved = saved' := by
  have hn : pre.length = pre'.length := by
    rcases lt_trichotomy pre.length pre'.length with hl | he | hr
    · exact False.elim (h.key_no_later_start h' hq hq' hs hl)
    · exact he
    · exact False.elim (h'.key_no_later_start h hq' hq hs' hr)
  have ht := h.canonical_trace
  have ht' := h'.canonical_trace
  simp only [reduceCtorEq, ite_false, Nat.add_zero] at ht ht'
  rw [hn] at ht
  have heq := Option.some.inj (ht.symm.trans ht')
  exact ⟨congrArg (fun x => x.2.2.1) heq, congrArg (fun x => x.2.2.2) heq⟩

structure KeyWitness (bs : List UInt8) (start q : Nat) where
  first : Bool
  cursor : Nat
  key : String
  rest : List UInt8
  history : Batches
  saved : Bool
  prefixModel : Prefix bs start (.member first) cursor history saved
  quote : SerdeNextKey.keyQ first bs cursor = some q
  model : stringBody (bs.drop q) [] = some (some key, rest)

/-- Selects the actual key charge; fitting its sum to the model budget is a separate obligation. -/
noncomputable def selectedKeyCost (cfg : WasmConfig) (bs : List UInt8) (start baseF q : Nat) : Nat := by
  classical
  exact
    if h : Nonempty (KeyWitness bs start q) then
      let w := Classical.choice h
      SerdeKeyReuse.preciseCost cfg (endFreeBound baseF 0 w.history) (endCap 0 w.history)
        bs w.key.toUTF8.toList w.rest q
    else 0

theorem selectedKeyCost_of_witness (cfg : WasmConfig) (bs : List UInt8) (start baseF q : Nat)
    (w : KeyWitness bs start q) :
    SerdeKeyReuse.preciseCost cfg (endFreeBound baseF 0 w.history) (endCap 0 w.history)
      bs w.key.toUTF8.toList w.rest q = selectedKeyCost cfg bs start baseF q := by
  classical
  unfold selectedKeyCost
  rw [dif_pos ⟨w⟩]
  let other := Classical.choice (show Nonempty (KeyWitness bs start q) from ⟨w⟩)
  change _ = SerdeKeyReuse.preciseCost cfg (endFreeBound baseF 0 other.history) (endCap 0 other.history)
    bs other.key.toUTF8.toList other.rest q
  have hhistory := w.prefixModel.key_history_unique other.prefixModel w.quote other.quote w.model other.model
  have hmodel := Option.some.inj (w.model.symm.trans other.model)
  have hkey := Option.some.inj (congrArg Prod.fst hmodel)
  have hrest := congrArg Prod.snd hmodel
  dsimp only at hrest
  rw [hhistory.1, hkey, hrest]

end WNear.Binary.SerdeObjectPrefix
