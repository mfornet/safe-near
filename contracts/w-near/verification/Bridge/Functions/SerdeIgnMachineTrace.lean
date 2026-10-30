import Bridge.Functions.IgnoreModel
import Bridge.Functions.SerdeIgnTrace

/-!
# A physical frame trace for the complete ignored-value machine

The pure machine carries the pending current frame in the head of its stack
while expecting a value. Function 81 keeps that frame in a local instead.
It appends the pending frame only when the next value opens another container.
The trace records those actual vector pushes and the nonempty vector pops;
scalar completion and entering a member do not write a frame byte.
-/

namespace WNear.Binary.SerdeIgnMachineTrace

open NearInterface.Json WNear.JsonFuel WNear.SerdeStructModel WNear.IgnoreModel

abbrev Result := List UInt8 × List SerdeIgnTrace.Op

/-- Number of saved frames physically in the vector, excluding the pending local frame. -/
def depth : Mode → List UInt8 → Nat
  | .val, frames => frames.length - 1
  | .opened _, frames => frames.length
  | .cont _, frames => frames.length

/-- Prepend one actual vector operation to a successful continuation. -/
def mark (op : SerdeIgnTrace.Op) (res : Option Result) : Option Result :=
  res.map fun (r, ops) => (r, op :: ops)

/-- A nested container saves the pending local frame; the top-level container saves none. -/
def save (frames : List UInt8) (res : Option Result) : Option Result :=
  match frames with
  | [] => res
  | _ :: _ => mark true res

/-- Popping a pending local frame is free of vector operations; a saved frame records a pop. -/
def pop (record : Bool) (frames r : List UInt8)
    (k : UInt8 → List UInt8 → List UInt8 → Option Result) : Option Result :=
  match frames with
  | [] => some (r, [])
  | f :: frames => if record then mark false (k f frames r) else k f frames r

/-- The same key/colon transition, with a continuation that also returns the trace. -/
def key {α : Type} (sk : List UInt8 → Option (List UInt8)) (r : List UInt8)
    (k : List UInt8 → Option α) : Option α :=
  match skipWhitespace r with
  | 0x22 :: r1 => (sk r1).bind fun r2 =>
    match skipWhitespace r2 with
    | 0x3A :: r3 => k r3
    | _ => none
  | _ => none

/-- The complete machine, recording actual scratch-vector operations in execution order. -/
def run (sv sk : List UInt8 → Option (List UInt8)) : Nat → Mode → List UInt8 → List UInt8 → Option Result
  | 0, _, _, _ => none
  | n + 1, .val, frames, bs =>
    match skipWhitespace bs with
    | 0x5B :: r => save frames (run sv sk n (.opened 0x5B) frames r)
    | 0x7B :: r => save frames (run sv sk n (.opened 0x7B) frames r)
    | s => (sv s).bind fun r => pop false frames r fun f frames r => run sv sk n (.cont f) frames r
  | n + 1, .opened f, frames, r =>
    if f = 0x5B then
      match skipWhitespace r with
      | 0x5D :: r' => pop true frames r' fun g frames r => run sv sk n (.cont g) frames r
      | s => run sv sk n .val (0x5B :: frames) s
    else
      match skipWhitespace r with
      | 0x7D :: r' => pop true frames r' fun g frames r => run sv sk n (.cont g) frames r
      | s => key sk s (run sv sk n .val (0x7B :: frames))
  | n + 1, .cont f, frames, r =>
    match skipWhitespace r with
    | 0x2C :: r' => if f = 0x5B then run sv sk n .val (0x5B :: frames) r'
        else key sk r' (run sv sk n .val (0x7B :: frames))
    | 0x5D :: r' => if f = 0x5B then pop true frames r' (fun g frames r => run sv sk n (.cont g) frames r) else none
    | 0x7D :: r' => if f = 0x5B then none else pop true frames r' (fun g frames r => run sv sk n (.cont g) frames r)
    | _ => none

theorem erase_mark (op : SerdeIgnTrace.Op) (res : Option Result) :
    (mark op res).map Prod.fst = res.map Prod.fst := by
  cases res <;> rfl

theorem erase_save (frames : List UInt8) (res : Option Result) :
    (save frames res).map Prod.fst = res.map Prod.fst := by
  cases frames <;> simp only [save, erase_mark]

theorem erase_pop (record : Bool) (frames r : List UInt8)
    (k : UInt8 → List UInt8 → List UInt8 → Option Result) :
    (pop record frames r k).map Prod.fst = popThen frames r (fun f frames r => (k f frames r).map Prod.fst) := by
  cases frames <;> simp only [pop, popThen, Option.map_some]
  split <;> simp only [erase_mark]

theorem map_key {α β : Type} (f : α → β) (sk : List UInt8 → Option (List UInt8))
    (r : List UInt8) (k : List UInt8 → Option α) :
    (key sk r k).map f = key sk r (fun r => (k r).map f) := by
  unfold key
  split
  · simp only [Option.map_bind]
    congr 1
    funext r2
    dsimp only [Function.comp_def]
    split <;> rfl
  · rfl

theorem erase_key (sk : List UInt8 → Option (List UInt8)) (r : List UInt8)
    (k : List UInt8 → Option Result) :
    (key sk r k).map Prod.fst = keyThen sk r (fun r => (k r).map Prod.fst) :=
  map_key Prod.fst sk r k

/-- Forgetting the trace gives the original complete machine on every input and fuel. -/
theorem erase_run (sv sk : List UInt8 → Option (List UInt8)) (n : Nat) (mode : Mode)
    (frames bs : List UInt8) :
    (run sv sk n mode frames bs).map Prod.fst = ignM sv sk n mode frames bs := by
  induction n generalizing mode frames bs with
  | zero => cases mode <;> rfl
  | succ n ih =>
    cases mode with
    | val =>
      simp only [run, ignM]
      split <;> simp_all only [erase_save, erase_pop, Option.map_bind, Function.comp_def, ih]
    | opened f =>
      simp only [run, ignM]
      split <;> split <;>
        simp_all only [erase_pop, erase_key, ih]
    | cont f =>
      simp only [run, ignM]
      split
      · split <;> simp_all only [erase_key, ih]
      · split <;> simp_all only [erase_pop, ih, Option.map_none]
      · split <;> simp_all only [erase_pop, ih, Option.map_none]
      · simp_all only [Option.map_none]

/-- A successful complete trace starts at this physical height and finishes empty. -/
def Legal (len : Nat) : List SerdeIgnTrace.Op → Prop
  | [] => len = 0
  | true :: ops => Legal (len + 1) ops
  | false :: ops => 0 < len ∧ Legal (len - 1) ops

/-- Successful outcomes have legal stack operations and charge pushes to consumed input bytes. -/
def Good (len input : Nat) (res : Option Result) : Prop :=
  ∀ r ops, res = some (r, ops) → Legal len ops ∧ r.length ≤ input ∧ SerdeIgnTrace.pushCount ops ≤ input - r.length

theorem good_none (len input : Nat) : Good len input none := by
  intro r ops h; cases h

theorem good_mono {len input input' : Nat} {res : Option Result} (h : Good len input res)
    (hle : input ≤ input') : Good len input' res := by
  intro r ops hr
  obtain ⟨hl, hr, hp⟩ := h r ops hr
  exact ⟨hl, by omega, by omega⟩

theorem good_push {len input : Nat} {res : Option Result} (h : Good (len + 1) input res) :
    Good len (input + 1) (mark true res) := by
  intro r ops hr
  simp only [mark, Option.map_eq_some_iff] at hr
  obtain ⟨⟨r', ops'⟩, hres, he⟩ := hr
  cases he
  dsimp only
  obtain ⟨hl, hr, hp⟩ := h _ _ hres
  refine ⟨hl, by omega, ?_⟩
  simp only [SerdeIgnTrace.pushCount, ite_true]
  omega

theorem good_saved {frames : List UInt8} {input : Nat} {res : Option Result}
    (h : Good frames.length input res) : Good (frames.length - 1) (input + 1) (save frames res) := by
  cases frames with
  | nil => exact good_mono h (by omega)
  | cons f frames => simpa only [save, List.length_cons, Nat.add_sub_cancel] using good_push h

theorem good_pop_mark {len input : Nat} {res : Option Result} (h : Good len input res) :
    Good (len + 1) input (mark false res) := by
  intro r ops hr
  simp only [mark, Option.map_eq_some_iff] at hr
  obtain ⟨⟨r', ops'⟩, hres, he⟩ := hr
  cases he
  dsimp only
  obtain ⟨hl, hr, hp⟩ := h _ _ hres
  refine ⟨?_, hr, ?_⟩
  · simp only [Legal, Nat.add_sub_cancel]; exact ⟨by omega, hl⟩
  · simpa only [SerdeIgnTrace.pushCount, Bool.false_eq_true, ite_false, Nat.zero_add] using hp

theorem good_pop (record : Bool) (frames r : List UInt8)
    (k : UInt8 → List UInt8 → List UInt8 → Option Result)
    (hk : ∀ f frames r, Good frames.length r.length (k f frames r)) :
    Good (if record then frames.length else frames.length - 1) r.length (pop record frames r k) := by
  cases frames with
  | nil =>
    intro r' ops h
    simp only [pop, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [Legal, SerdeIgnTrace.pushCount]
  | cons f frames =>
    cases record
    · simpa only [pop, Bool.false_eq_true, ite_false, List.length_cons, Nat.add_sub_cancel] using hk f frames r
    · simpa only [pop, ite_true, List.length_cons] using good_pop_mark (hk f frames r)

theorem good_key (sk : List UInt8 → Option (List UInt8))
    (hsk : ∀ r r', sk r = some r' → r'.length ≤ r.length) (len : Nat) (r : List UInt8)
    (k : List UInt8 → Option Result) (hk : ∀ r, Good len r.length (k r)) : Good len r.length (key sk r k) := by
  intro rest ops h
  unfold key at h
  split at h
  · rename_i r1 h1
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨r2, h2, h⟩ := h
    split at h
    · rename_i r3 h3
      have hl1 := skip_cons_length h1
      have hl2 := hsk _ _ h2
      have hl3 := skip_cons_length h3
      exact good_mono (hk r3) (by omega) _ _ h
    · cases h
  · cases h

/-- Trace legality and push accounting hold for the complete machine, at every mode and fuel. -/
theorem run_good (sv sk : List UInt8 → Option (List UInt8))
    (hsv : ∀ r r', sv r = some r' → r'.length ≤ r.length)
    (hsk : ∀ r r', sk r = some r' → r'.length ≤ r.length)
    (n : Nat) (mode : Mode) (frames bs : List UInt8) :
    Good (depth mode frames) bs.length (run sv sk n mode frames bs) := by
  induction n generalizing mode frames bs with
  | zero => exact good_none _ _
  | succ n ih =>
    cases mode with
    | val =>
      simp only [run, depth]
      split
      · rename_i r hs
        have hl := skip_cons_length hs
        exact good_mono (good_saved (ih (.opened 0x5B) frames r)) (by omega)
      · rename_i r hs
        have hl := skip_cons_length hs
        exact good_mono (good_saved (ih (.opened 0x7B) frames r)) (by omega)
      · intro rest ops h
        simp only [Option.bind_eq_some_iff] at h
        obtain ⟨r, hr, h⟩ := h
        have hl := hsv _ _ hr
        have hw := skip_length bs
        exact good_mono (good_pop false frames r (fun f frames r => run sv sk n (.cont f) frames r)
          (fun f frames r => ih (.cont f) frames r)) (by omega) rest ops h
    | opened f =>
      simp only [run, depth]
      split
      · split
        · rename_i r hs
          have hl := skip_cons_length hs
          exact good_mono (good_pop true frames r (fun g frames r => run sv sk n (.cont g) frames r)
            (fun g frames r => ih (.cont g) frames r)) (by omega)
        · simpa only [depth, List.length_cons, Nat.add_sub_cancel] using
            good_mono (ih .val (0x5B :: frames) (skipWhitespace bs)) (skip_length bs)
      · split
        · rename_i r hs
          have hl := skip_cons_length hs
          exact good_mono (good_pop true frames r (fun g frames r => run sv sk n (.cont g) frames r)
            (fun g frames r => ih (.cont g) frames r)) (by omega)
        · apply good_mono (good_key sk hsk frames.length (skipWhitespace bs) _ ?_) (skip_length bs)
          intro r
          simpa only [depth, List.length_cons, Nat.add_sub_cancel] using ih .val (0x7B :: frames) r
    | cont f =>
      simp only [run, depth]
      split
      · rename_i r hs
        have hl := skip_cons_length hs
        split
        · simpa only [depth, List.length_cons, Nat.add_sub_cancel] using
            good_mono (ih .val (0x5B :: frames) r) (by omega : r.length ≤ bs.length)
        · apply good_mono (good_key sk hsk frames.length r _ ?_) (by omega)
          intro r
          simpa only [depth, List.length_cons, Nat.add_sub_cancel] using ih .val (0x7B :: frames) r
      · rename_i r hs
        have hl := skip_cons_length hs
        split
        · exact good_mono (good_pop true frames r (fun g frames r => run sv sk n (.cont g) frames r)
            (fun g frames r => ih (.cont g) frames r)) (by omega)
        · exact good_none _ _
      · rename_i r hs
        have hl := skip_cons_length hs
        split
        · exact good_none _ _
        · exact good_mono (good_pop true frames r (fun g frames r => run sv sk n (.cont g) frames r)
            (fun g frames r => ih (.cont g) frames r)) (by omega)
      · exact good_none _ _

/-- Ignored key strings retain their syntactic endpoint even when raw UTF-8 is invalid. -/
def keyBody (bs : List UInt8) : Option (List UInt8) := (stringBody bs []).map Prod.snd

theorem keyBody_length (bs r : List UInt8) (h : keyBody bs = some r) : r.length ≤ bs.length := by
  simp only [keyBody, Option.map_eq_some_iff] at h
  obtain ⟨⟨s, r'⟩, hb, hr⟩ := h
  dsimp only at hr
  subst hr
  have hl := stringBody_len hb
  omega

/-- The complete model-directed trace, with the fuel already proved sufficient for `ignM`. -/
def trace (bs : List UInt8) : Option Result :=
  run vSkip keyBody (2 * bs.length + 2) .val [] bs

/-- The trace's decoder covers exactly the original complete skipped-value semantics. -/
theorem erase_trace (bs : List UInt8) : (trace bs).map Prod.fst = vSkip bs := by
  unfold trace
  rw [erase_run]
  exact ignM_eq vSkip keyBody (fun _ _ _ _ => rfl) (fun _ => rfl) bs

/-- Every successful ignored value has a legal actual-vector trace bounded by consumed bytes. -/
theorem trace_some {bs r : List UInt8} (h : vSkip bs = some r) :
    ∃ ops, trace bs = some (r, ops) ∧ Legal 0 ops ∧ r.length ≤ bs.length ∧
      SerdeIgnTrace.pushCount ops ≤ bs.length - r.length ∧
      SerdeIgnTrace.peak 0 ops ≤ bs.length - r.length := by
  have hm : (trace bs).map Prod.fst = some r := by rw [erase_trace, h]
  obtain ⟨⟨r', ops⟩, ht, he⟩ := Option.map_eq_some_iff.mp hm
  dsimp only at he
  subst he
  have hg := run_good vSkip keyBody (fun _ _ => vSkip_length) keyBody_length
    (2 * bs.length + 2) .val [] bs
  have hp := hg _ _ ht
  simp only [depth, List.length_nil, Nat.zero_sub] at hp
  have hn := SerdeIgnTrace.peak_le 0 ops
  exact ⟨ops, ht, hp.1, hp.2.1, hp.2.2, by omega⟩

/-- Adding the trace leaves the full model-agreement statement intact. -/
theorem trace_agrees :
    Agrees (fun bs => (trace bs).map fun x => ((), x.1)) valueSkip := by
  intro bs
  have he : (trace bs).map (fun x => ((), x.1)) = (vSkip bs).map (fun r => ((), r)) := by
    rw [← erase_trace]
    simp only [Option.map_map, Function.comp_def]
  dsimp only
  rw [he]
  exact vSkip_agrees bs

/-- A legal complete trace leaves no saved vector frames. -/
theorem legal_endLen (cap : UInt32) (len : Nat) (ops : List SerdeIgnTrace.Op) (h : Legal len ops) :
    (SerdeIgnTrace.endState cap len ops).2 = 0 := by
  induction ops generalizing cap len with
  | nil => exact h
  | cons op ops ih =>
    cases op
    · exact ih cap (len - 1) h.2
    · exact ih (SerdeIgnTrace.nextCap cap len true) (len + 1) h

/-- Peak length bounds every reached length, including the initial one. -/
theorem le_peak (len : Nat) (ops : List SerdeIgnTrace.Op) : len ≤ SerdeIgnTrace.peak len ops := by
  cases ops <;> simp [SerdeIgnTrace.peak]

/-- A legal trace with a bounded peak discharges every reserve arithmetic premise. -/
theorem valid_of_legal (cap : UInt32) (len : Nat) (ops : List SerdeIgnTrace.Op) (hlegal : Legal len ops)
    (hlen : len ≤ cap.toNat) (hcap : cap.toNat < 2 ^ 27)
    (hpeak : 2 * SerdeIgnTrace.peak len ops + 8 < 2 ^ 27) : SerdeIgnTrace.Valid cap len ops := by
  induction ops generalizing cap len with
  | nil => exact ⟨hlen, hcap⟩
  | cons op ops ih =>
    cases op
    · have hnext : 2 * SerdeIgnTrace.peak (len - 1) ops + 8 < 2 ^ 27 := by
        simp only [SerdeIgnTrace.peak, SerdeIgnTrace.nextLen, Bool.false_eq_true, ite_false] at hpeak
        omega
      exact ⟨hlen, hcap, hlegal.1, ih cap (len - 1) hlegal.2 (by omega) hcap hnext⟩
    · have hnext : 2 * SerdeIgnTrace.peak (len + 1) ops + 8 < 2 ^ 27 := by
        simp only [SerdeIgnTrace.peak, SerdeIgnTrace.nextLen, ite_true] at hpeak
        omega
      have hused := le_peak (len + 1) ops
      have hsmall : len + 1 < 2 ^ 27 := by omega
      have hL : (UInt32.ofNat len).toNat = len := by simp; omega
      have hsum : (UInt32.ofNat len + 1).toNat = len + 1 := by rw [UInt32.toNat_add, hL]; simp; omega
      have hnew : len + 1 ≤ (ScratchGrow.capAfter cap (UInt32.ofNat len) 1).toNat := by
        by_cases hf : ScratchGrow.fits cap (UInt32.ofNat len) 1
        · simp only [ScratchGrow.capAfter, if_pos hf]
          simp only [ScratchGrow.fits, hL, UInt32.toNat_one] at hf
          omega
        · simp only [ScratchGrow.capAfter, if_neg hf]
          rw [VecGrow.growCap_toNat _ _ (by omega), hsum]
          omega
      have hc := ScratchGrow.capAfter_used cap (UInt32.ofNat len) 1 (by omega) (by rw [hL]; simp; omega)
      rw [hsum] at hc
      have hnewcap : (ScratchGrow.capAfter cap (UInt32.ofNat len) 1).toNat < 2 ^ 27 := by omega
      exact ⟨hlen, hcap, hsmall, ih _ (len + 1) hlegal hnew hnewcap hnext⟩

/-- On the parser's input-size domain, complete successful values yield valid reserve traces. -/
theorem trace_valid {bs r : List UInt8} (cap : UInt32) (hcap : cap.toNat < 2 ^ 27)
    (hlen : bs.length < 2 ^ 24) (h : vSkip bs = some r) :
    ∃ ops, trace bs = some (r, ops) ∧ SerdeIgnTrace.Valid cap 0 ops ∧
      (SerdeIgnTrace.endState cap 0 ops).2 = 0 ∧
      SerdeIgnTrace.pushCount ops ≤ bs.length - r.length ∧
      SerdeIgnTrace.peak 0 ops ≤ bs.length - r.length := by
  obtain ⟨ops, ht, hl, hr, hp, hn⟩ := trace_some h
  exact ⟨ops, ht, valid_of_legal cap 0 ops hl (by omega) hcap (by omega),
    legal_endLen cap 0 ops hl, hp, hn⟩

/-- The closed growth budget is monotone in its high-water argument. -/
theorem budget_mono (cfg : Wasm.Near.WasmConfig) (F G N M : Nat) (h : N ≤ M) :
    SerdeIgnTrace.budget cfg F G N ≤ SerdeIgnTrace.budget cfg F G M := by
  unfold SerdeIgnTrace.budget
  have hm : 18 * (2 * N + 8) ≤ 18 * (2 * M + 8) := by omega
  have hd : (4 * N + 16 + 66066 * G) / 65536 ≤ (4 * M + 16 + 66066 * G) / 65536 := by omega
  have ha := Nat.mul_le_mul_right cfg.regularOpCost (Nat.add_le_add_left hm (1790 * G + (F * G + G * G) * 320))
  have hb := Nat.mul_le_mul_left cfg.linearOpUnitCost hd
  exact Nat.add_le_add (Nat.add_le_add_right ha _) hb

/-- Full successful values have a growth reserve bounded by consumed input and their actual growth count. -/
theorem trace_budget (cfg : Wasm.Near.WasmConfig) (F : Nat) {bs r : List UInt8} (cap : UInt32)
    (hcap : cap.toNat < 2 ^ 27) (hlen : bs.length < 2 ^ 24) (h : vSkip bs = some r) :
    ∃ ops, trace bs = some (r, ops) ∧ SerdeIgnTrace.Valid cap 0 ops ∧
      (SerdeIgnTrace.endState cap 0 ops).2 = 0 ∧
      SerdeIgnTrace.peak 0 ops ≤ bs.length - r.length ∧
      SerdeIgnTrace.extraCost cfg F cap 0 ops ≤
        SerdeIgnTrace.budget cfg F (SerdeIgnTrace.growthCount cap 0 ops) (bs.length - r.length) := by
  obtain ⟨ops, ht, hv, he, _, hp⟩ := trace_valid cap hcap hlen h
  exact ⟨ops, ht, hv, he, hp, (SerdeIgnTrace.extraCost_budget cfg F cap 0 ops hv).trans
    (budget_mono cfg F _ _ _ hp)⟩

end WNear.Binary.SerdeIgnMachineTrace
