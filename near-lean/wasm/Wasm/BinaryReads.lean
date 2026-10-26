import Wasm.Binary

/-!
# Decoding one element at a time

Proofs about the decoding of a large binary cannot let the kernel run the
decoder on all of it at once. They prove what the decoder reads piece by
piece, and these lemmas put the pieces together.

`Reads p input xs a b` says that `p`, run repeatedly from position `a`,
reads the elements `xs` one after another and stops at `b`. A repetition
(`count`, and so `vec`) over such a chain returns exactly `xs`.
-/

namespace Wasm.Binary.Parser

/-- `p` reads `xs` one after another from `a`, ending at `b`. -/
def Reads (p : Parser α) (input : Input) : List α → Nat → Nat → Prop
  | [], a, b => a = b
  | x :: xs, a, b => ∃ m, p input a = .ok (x, m) ∧ Reads p input xs m b

theorem Reads.append {p : Parser α} {input : Input} {xs ys : List α} {a b c : Nat}
    (h₁ : Reads p input xs a b) (h₂ : Reads p input ys b c) : Reads p input (xs ++ ys) a c := by
  induction xs generalizing a with
  | nil => cases h₁; exact h₂
  | cons x xs ih =>
    obtain ⟨m, hx, hrest⟩ := h₁
    exact ⟨m, hx, ih hrest⟩

theorem bind_ok {p : Parser α} {f : α → Parser β} {input : Input} {pos pos' : Nat} {a : α}
    (h : p input pos = .ok (a, pos')) : (p >>= f) input pos = f a input pos' := by
  show Parser.bind p f input pos = _
  simp only [Parser.bind, h]

theorem count_go_of_reads {p : Parser α} {input : Input} {xs : List α} {a b : Nat}
    (acc : Array α) (h : Reads p input xs a b) :
    count.go p xs.length acc input a = .ok (acc ++ xs.toArray, b) := by
  induction xs generalizing a acc with
  | nil => cases h; simp [count.go]; rfl
  | cons x xs ih =>
    obtain ⟨m, hx, hrest⟩ := h
    simp only [List.length_cons, count.go]
    rw [bind_ok hx, ih _ hrest]
    simp

theorem count_of_reads {p : Parser α} {input : Input} {xs : List α} {a b : Nat}
    (h : Reads p input xs a b) : count xs.length p input a = .ok (xs.toArray, b) := by
  simpa [count] using count_go_of_reads (Array.mkEmpty xs.length) h

/-! ## Sections -/

theorem pure_bind_apply {a : α} {f : α → Parser β} {input : Input} {pos : Nat} :
    ((pure a : Parser α) >>= f) input pos = f a input pos := rfl

theorem sections_step {s s' : Sections} {input : Input} {pos pos' : Nat} (fuel : Nat)
    (hpos : pos < input.limit) (h : oneSection s input pos = .ok (s', pos')) :
    sections (fuel + 1) s input pos = sections fuel s' input pos' := by
  have hend : atEnd input pos = .ok (false, pos) := by
    simp [atEnd, Nat.not_le.mpr hpos]
  conv => lhs; unfold sections
  rw [bind_ok hend]
  simp only [Bool.false_eq_true, ↓reduceIte]
  exact bind_ok h

theorem sections_end {s : Sections} {input : Input} {pos : Nat} (fuel : Nat)
    (h : input.limit ≤ pos) : sections fuel s input pos = .ok (s, pos) := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
    have hend : atEnd input pos = .ok (true, pos) := by simp [atEnd, h]
    unfold sections
    rw [bind_ok hend]
    rfl

/-- The code section, from what its entries decode to. -/
theorem oneSection_code {s : Sections} {input : Input} {pos q size : Nat}
    {cs : Array (Nat × List ValType × Expr)}
    (hid : byte input pos = .ok (10, pos + 1)) (hsize : u32 input (pos + 1) = .ok (size, q))
    (hrank : s.lastRank < 11) (hlimit : q + size ≤ input.limit)
    (hvec : vec code { input with limit := q + size } q = .ok (cs, q + size)) :
    oneSection s input pos = .ok ({ s with lastRank := 11, codes := cs }, q + size) := by
  unfold oneSection
  rw [bind_ok hid, bind_ok hsize]
  simp only [show ((10 : UInt8) == 0) = false from rfl, show sectionRank 10 = some 11 from rfl,
    Bool.false_eq_true, ↓reduceIte]
  rw [pure_bind_apply]
  simp only [Nat.not_le.mpr hrank, ↓reduceIte]
  unfold sized
  simp only [show ¬ (q + size > input.limit) from Nat.not_lt.mpr hlimit, ↓reduceIte]
  rw [bind_ok hvec]
  change (if q + size = q + size then Except.ok (_, q + size) else _) = _
  simp

/-- The module, from the result of the section loop. -/
theorem body_eq {input : Input} {pos pos' : Nat} {s : Sections}
    (hs : sections (input.limit - pos) {} input pos = .ok (s, pos'))
    (hsize : s.funcTypes.size = s.codes.size) (hcount : s.dataCount = none)
    (hdata : (s.codes.any fun e => anyUsesDataIndex e.2.2) = false) :
    body input pos = .ok ({ s.module with funcs := s.funcTypes.zipWith entryFunc s.codes }, pos') := by
  unfold body
  rw [bind_ok (p := fun input pos => sections (input.limit - pos) {} input pos) hs]
  simp only [hsize, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, hcount, hdata]
  rfl

end Wasm.Binary.Parser
