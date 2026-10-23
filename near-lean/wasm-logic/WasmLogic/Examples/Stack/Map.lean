import WasmLogic.Examples.Stack.Specs

/-!
# `stack_map`: a loop with an indirect call

Iris-Wasm's `stack_map.v`. `stack_map` applies the function in entry `fn`
of the module's table to every element of the stack, bottom first, storing
each result in place. The callee is an arbitrary function given by its
specification: from `Φ u` it returns some `w` with `Ψ u w`, and it may use
the table entry. The loop's invariant is Iris-Wasm's `spec_map_loop_j`: the
top `j` elements are still to do, the rest are done.
-/

namespace WasmLogic.Examples.Stack

open Wasm Iris Iris.BI Iris.ProgramLogic WasmLogic

section Defs

variable {H : Type} {GF : BundledGFunctors} [WasmGS H GF]

/-- `stackAll s Φ`: `Φ` of every element. -/
def stackAll (s : List UInt32) (Φ : UInt32 → IProp GF) : IProp GF :=
  [∗list] x ∈ s, Φ x

/-- `stackAll2 s s' Ψ`: `Ψ` of corresponding elements; false if the lengths differ. -/
def stackAll2 : List UInt32 → List UInt32 → (UInt32 → UInt32 → IProp GF) → IProp GF
  | [], [], _ => iprop(emp)
  | a :: s, b :: s', Ψ => iprop(Ψ a b ∗ stackAll2 s s' Ψ)
  | _, _, _ => iprop(False)

/-- The element cells of a stack at `v`, as `isStack` lays them out. -/
abbrev stackElems (n v : Nat) (l : List UInt32) : IProp GF :=
  [∗list] i ↦ w ∈ l, n ↦[i32][ v + l.length * 4 - 4 * i ] w

end Defs

section Lemmas

variable {H : Type} {GF : BundledGFunctors} [WasmGS H GF]

theorem stackElems_append (n v : Nat) (A B : List UInt32) :
    stackElems (H := H) (GF := GF) n v (A ++ B) ⊣⊢
      stackElems n (v + B.length * 4) A ∗ stackElems n v B := by
  refine BigSepL.bigSepL_append.trans (sep_congr ?_ ?_)
  · have h : ∀ i, v + (A ++ B).length * 4 - 4 * i = v + B.length * 4 + A.length * 4 - 4 * i := by
      intro i; simp only [List.length_append]; omega
    simp only [h]
    exact .rfl
  · have h : ∀ i, v + (A ++ B).length * 4 - 4 * (i + A.length) = v + B.length * 4 - 4 * i := by
      intro i; simp only [List.length_append]; omega
    simp only [h]
    exact .rfl

theorem stackElems_single (n v : Nat) (x : UInt32) :
    stackElems (H := H) (GF := GF) n v [x] ⊣⊢ n ↦[i32][ v + 4 ] x := by
  refine BigSepL.bigSepL_singleton.trans ?_
  simp only [List.length_singleton, Nat.one_mul, Nat.mul_zero, Nat.sub_zero]
  exact .rfl

/-- The element `x` between `A` above and `B` below. -/
theorem stackElems_mid (n v : Nat) (A B : List UInt32) (x : UInt32) :
    stackElems (H := H) (GF := GF) n v (A ++ x :: B) ⊣⊢
      stackElems n (v + (B.length + 1) * 4) A ∗ n ↦[i32][ v + B.length * 4 + 4 ] x ∗
        stackElems n v B := by
  refine (stackElems_append n v A (x :: B)).trans (sep_congr .rfl ?_)
  refine (stackElems_append n v [x] B).trans (sep_congr ?_ .rfl)
  exact stackElems_single n _ x

theorem stackAll2_cons (a b : UInt32) (s s' : List UInt32) (Ψ : UInt32 → UInt32 → IProp GF) :
    stackAll2 (a :: s) (b :: s') Ψ = iprop(Ψ a b ∗ stackAll2 s s' Ψ) := rfl

theorem stackAll_snoc (s : List UInt32) (x : UInt32) (Φ : UInt32 → IProp GF) :
    stackAll (s ++ [x]) Φ ⊣⊢ stackAll s Φ ∗ Φ x :=
  BigSepL.bigSepL_snoc

end Lemmas

section Specs

variable {H : Type} {GF : BundledGFunctors} [WasmGS H GF] {lim : ExecLimits} {d : Nat}

/-- The callee's specification, as `stack_map` assumes it: from `Φ u` and
the table entry, it returns one `w` with `Ψ u w` and gives the entry back. -/
abbrev CalleeSpec (lim : ExecLimits) (d : Nat) (j0 a : Nat) (fn : UInt32) (ctype : FuncType)
    (cinst : Nat) (cmi : ModuleInst) (ccode : Func) (Φ : UInt32 → IProp GF)
    (Ψ : UInt32 → UInt32 → IProp GF) : IProp GF :=
  iprop(□ ∀ (u : UInt32) (Φf : FunPost GF),
    Φ u ∗ j0 ↦[wt][ fn.toNat ] Ref.func a ∗
      (∀ w, Ψ u w ∗ j0 ↦[wt][ fn.toNat ] Ref.func a -∗ Φf.ret [.i32 w]) -∗
    wpInvoke (H := H) lim (d + 1) ctype cinst cmi ccode [.i32 u] Φf)

/-- `spec_map_loop_j`: the loop, with the top `j` elements of `s` still to
map and `s'` the results for the rest. -/
theorem spec_map_loop (n v : Nat) (fn : UInt32) (s : List UInt32) (j0 a : Nat) (ctype : FuncType)
    (cinst : Nat) (cmi : ModuleInst) (ccode : Func) (Φ : UInt32 → IProp GF)
    (Ψ : UInt32 → UInt32 → IProp GF) (hd : d + 1 < lim.maxCallDepth)
    (hct : ctype = { params := [i32t], results := [i32t] })
    (hdiv : two16 ∣ v) (hle : v ≤ ffff0000) (hlen : s.length < two14) (Φl : Post H GF) (j : Nat) :
    ∀ (g : Frame) (s' : List UInt32), g.mi.memAddrs[0]? = some n →
      g.locals[1]? = some (.i32 fn) →
      g.locals[2]? = some (u32 (v + s.length * 4 - 4 * j)) →
      g.locals[3]? = some (u32 (v + s.length * 4)) → g.locals.size ≥ 4 →
      g.mi.types[1]! = ctype → g.mi.tableAddrs[0]? = some j0 → j + s'.length = s.length →
      a ↪[wf] FuncInst.wasm ctype cinst ccode ∗ cinst ↪[inst] cmi ∗
        CalleeSpec (H := H) lim d j0 a fn ctype cinst cmi ccode Φ Ψ ∗
        stackElems n v (s.take j ++ s') ∗ stackAll (s.take j) Φ ∗ stackAll2 (s.drop j) s' Ψ ∗
        j0 ↦[wt][ fn.toNat ] Ref.func a ∗
        (∀ (s'' : List UInt32) (g' : Frame), ⌜s''.length = s.length⌝ ∗ stackElems n v s'' ∗
          stackAll2 s s'' Ψ ∗ j0 ↦[wt][ fn.toNat ] Ref.func a ∗
          ⌜g'.inst = g.inst ∧ g'.mi = g.mi⌝ -∗ Φl.normal [] g')
      ⊢ wpi lim d g [] [.loop .empty map_loop_body] (Post.block 0 [] Φl) := by
  obtain ⟨_, _, hp⟩ := stack_bounds hdiv hle hlen
  induction j with
  | zero =>
    intro g s' hn h1 h2 h3 hsz hty htab hj
    iintro ⟨#Hf, #Hi, #Hspec, He, -, H2, Ht, HΦ⟩
    simp only [Nat.zero_add] at hj
    wp_apply 0 wpi_loop .empty map_loop_body [] [] rfl
    inext
    simp only [map_loop_body, Exec.blockType, List.length_nil]
    wp_step 0 wpi_local_get 2 (u32 (v + s.length * 4)) (by simpa using h2)
    inext; simp only [Post.seq_normal]
    wp_step 0 wpi_local_get 3 (u32 (v + s.length * 4)) h3
    inext; simp only [Post.seq_normal]
    wp_step 2 wpi_i32_relop .eq (UInt32.ofNat (v + s.length * 4)) (UInt32.ofNat (v + s.length * 4))
    inext; simp only [Post.seq_normal]
    rw [show Numeric.bool (Numeric.irelop32 .eq (UInt32.ofNat (v + s.length * 4))
      (UInt32.ofNat (v + s.length * 4))) = 1 by simp [Numeric.irelop32, Numeric.bool]]
    wp_step 1 wpi_br_if_true 1 _ (by decide)
    simp only [Post.seq_br, Post.loop, Post.block, List.length_nil, List.drop_nil, List.nil_append]
    isplitr
    · ipureintro; exact Nat.le_refl _
    iapply HΦ
    simp only []
    isplitr
    · ipureintro; omega
    isplitl [He]
    · iexact He
    isplitl [H2]
    · iexact H2
    isplitl [Ht]
    · iexact Ht
    · ipureintro; simp
  | succ k ih =>
    intro g s' hn h1 h2 h3 hsz hty htab hj
    have hk : k < s.length := by omega
    have htake : s.take (k + 1) = s.take k ++ [s[k]] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hk]; rfl
    have hdrop : s.drop k = s[k] :: s.drop (k + 1) := (List.drop_eq_getElem_cons hk)
    iintro ⟨#Hf, #Hi, #Hspec, He, H1, H2, Ht, HΦ⟩
    rw [htake, List.append_assoc, List.singleton_append]
    icases (stackElems_mid n v (s.take k) s' s[k]).1 $$ He with ⟨HA, Hx, HB⟩
    icases (stackAll_snoc (s.take k) s[k] Φ).1 $$ H1 with ⟨H1, Hφ⟩
    wp_apply 0 wpi_loop .empty map_loop_body [] [] rfl
    inext
    simp only [map_loop_body, Exec.blockType, List.length_nil]
    have hc : v + s.length * 4 - 4 * (k + 1) + 4 = v + s'.length * 4 + 4 := by omega
    have hc32 : v + s'.length * 4 + 4 < 2 ^ 32 := by omega
    wp_step 0 wpi_local_get 2 (u32 (v + s.length * 4 - 4 * (k + 1))) h2
    inext; simp only [Post.seq_normal]
    wp_step 0 wpi_local_get 3 (u32 (v + s.length * 4)) h3
    inext; simp only [Post.seq_normal]
    wp_step 2 wpi_i32_relop .eq (UInt32.ofNat (v + s.length * 4 - 4 * (k + 1)))
      (UInt32.ofNat (v + s.length * 4))
    inext; simp only [Post.seq_normal]
    rw [show Numeric.bool (Numeric.irelop32 .eq (UInt32.ofNat (v + s.length * 4 - 4 * (k + 1)))
        (UInt32.ofNat (v + s.length * 4))) = 0 by
      simp only [Numeric.irelop32, Numeric.bool, ofNat_beq (by omega : v + s.length * 4 - 4 * (k + 1) < 2 ^ 32) hp]
      simp; omega]
    wp_step 1 wpi_br_if_false 1
    inext; simp only [Post.seq_normal]
    wp_step 0 wpi_local_get 2 (u32 (v + s.length * 4 - 4 * (k + 1))) h2
    inext; simp only [Post.seq_normal]
    wp_step 0 wpi_i32_const 4
    inext; simp only [Post.seq_normal]
    wp_step 2 wpi_i32_binop .add (UInt32.ofNat (v + s.length * 4 - 4 * (k + 1))) 4
      (UInt32.ofNat (v + s'.length * 4 + 4)) (by
        simp only [Numeric.ibinop32, Except.ok.injEq]
        rw [← hc]
        apply UInt32.toNat_inj.mp
        rw [UInt32.toNat_add, ofNat_toNat_of_lt (by omega), ofNat_toNat_of_lt (by omega)]
        simp only [UInt32.reduceToNat]
        rw [Nat.mod_eq_of_lt (by omega)])
    inext; simp only [Post.seq_normal]
    wp_step 1 wpi_local_tee 2 (u32 (v + s'.length * 4 + 4))
    inext; simp only [Post.seq_normal]
    wp_step 0 wpi_local_get 2 (u32 (v + s'.length * 4 + 4)) (by
      simp [Frame.withLocals, Array.getElem?_setIfInBounds]; omega)
    inext; simp only [Post.seq_normal]
    wp_step 1 wpi_load_i32 a0 (UInt32.ofNat (v + s'.length * 4 + 4)) n (v + s'.length * 4 + 4) s[k]
      (by simpa [Frame.withLocals] using hn) (by rw [ofNat_toNat_of_lt hc32]; rfl)
    isplitl [Hx]
    · iexact Hx
    inext; iintro Hx; simp only [Post.seq_normal]
    wp_step 0 wpi_local_get 1 (.i32 fn) (by
      simp [Frame.withLocals, h1])
    inext; simp only [Post.seq_normal]
    have hci := wpi_call_indirect (H := H) (GF := GF) (lim := lim) (d := d)
      (f := g.withLocals (g.locals.set! 2 (u32 (v + s'.length * 4 + 4))))
      (Φ := Post.seq lim d [.store .i32 none a0, .br 0] (Post.loop lim d .empty map_loop_body 0 []
        (Post.block 0 [] Φl)))
      1 0 j0 fn a ctype cinst cmi ccode [u32 (v + s'.length * 4 + 4)] [.i32 s[k]]
      (by simpa [Frame.withLocals] using htab) (by simpa [Frame.withLocals] using hty.symm)
      (by subst hct; rfl) hd
    simp only [List.cons_append, List.nil_append, map_loop_body] at hci
    iapply wpi_cons
    wp_norm
    iapply hci
    isplitl [Ht]
    · iexact Ht
    isplitr
    · iexact Hf
    isplitr
    · iexact Hi
    inext
    iintro Ht
    iapply Hspec
    isplitl [Hφ]
    · iexact Hφ
    isplitl [Ht]
    · iexact Ht
    iintro %w ⟨Hψ, Ht⟩
    simp only [Post.seq_normal]
    wp_step 2 wpi_store_i32 a0 (UInt32.ofNat (v + s'.length * 4 + 4)) n (v + s'.length * 4 + 4) w
      (bytes32 s[k]) (by simpa [Frame.withLocals] using hn) (by rw [ofNat_toNat_of_lt hc32]; rfl)
      (by simp [bytes32])
    isplitl [Hx]
    · iexact Hx
    inext; iintro Hx; simp only [Post.seq_normal]
    wp_step 0 wpi_br 0
    simp only [Post.seq_br, Post.loop, List.append_nil, List.length_nil, List.drop_nil]
    isplitr
    · ipureintro; exact Nat.le_refl _
    have hih := ih (g.withLocals (g.locals.set! 2 (u32 (v + s'.length * 4 + 4)))) (w :: s')
      (by simpa [Frame.withLocals] using hn)
      (by simp [Frame.withLocals, h1])
      (by
        have : v + s'.length * 4 + 4 = v + s.length * 4 - 4 * k := by omega
        rw [this]
        simp [Frame.withLocals, Array.getElem?_setIfInBounds]
        omega)
      (by simpa [Frame.withLocals, Array.getElem?_setIfInBounds] using h3)
      (by simpa [Frame.withLocals] using hsz)
      (by simpa [Frame.withLocals] using hty)
      (by simpa [Frame.withLocals] using htab)
      (by simp only [List.length_cons]; omega)
    simp only [map_loop_body] at hih
    iapply hih
    isplitr
    · iexact Hf
    isplitr
    · iexact Hi
    isplitr
    · iexact Hspec
    isplitl [HA Hx HB]
    · iapply (stackElems_mid n v (s.take k) s' w).2
      isplitl [HA]
      · iexact HA
      isplitl [Hx]
      · iexact Hx
      · iexact HB
    isplitl [H1]
    · iexact H1
    isplitl [Hψ H2]
    · rw [hdrop, stackAll2_cons]
      isplitl [Hψ]
      · iexact Hψ
      · iexact H2
    isplitl [Ht]
    · iexact Ht
    iintro %s'' %g' ⟨%hl, He, H2, Ht, %hg⟩
    iapply HΦ
    isplitr
    · ipureintro; exact hl
    isplitl [He]
    · iexact He
    isplitl [H2]
    · iexact H2
    isplitl [Ht]
    · iexact Ht
    · ipureintro; exact hg

/-- `isStack` from its parts, for a list `s''` of the same length as `s`. -/
theorem isStack_intro (n v : Nat) (s s'' : List UInt32) (hl : s''.length = s.length)
    (hdiv : two16 ∣ v) (hle : v ≤ ffff0000) (hlen : s.length < two14) :
    n ↦[i32][ v ] UInt32.ofNat (v + s.length * 4) ∗ stackElems n v s'' ∗
      (∃ bs, ⌜bs.length = two16 - 4 - s.length * 4⌝ ∗ n ↦[wms][ v + s.length * 4 + 4 ] bs)
      ⊢ isStack (H := H) (GF := GF) v s'' n := by
  unfold isStack stackElems
  rw [hl]
  iintro ⟨Hp, He, Hfree⟩
  isplitr
  · ipureintro; exact hdiv
  isplitr
  · ipureintro; exact hle
  isplitr
  · ipureintro; exact hlen
  isplitl [Hp]
  · iexact Hp
  isplitl [He]
  · iexact He
  · iexact Hfree

/-- What `stack_map` needs besides the stack: the function's arguments, the
table entry and callee, and the callee's specification. -/
abbrev MapPre (lim : ExecLimits) (d : Nat) (f : Frame) (fn : UInt32) (s : List UInt32) (j0 a : Nat)
    (ctype : FuncType) (cinst : Nat) (cmi : ModuleInst) (ccode : Func) (Φ : UInt32 → IProp GF)
    (Ψ : UInt32 → UInt32 → IProp GF) : IProp GF :=
  iprop(⌜f.locals[1]? = some (.i32 fn)⌝ ∗ ⌜f.locals.size ≥ 4⌝ ∗ stackAll s Φ ∗
    ⌜f.mi.types[1]! = ctype⌝ ∗ ⌜f.mi.tableAddrs[0]? = some j0⌝ ∗
    j0 ↦[wt][ fn.toNat ] Ref.func a ∗ a ↪[wf] FuncInst.wasm ctype cinst ccode ∗ cinst ↪[inst] cmi ∗
    CalleeSpec (H := H) lim d j0 a fn ctype cinst cmi ccode Φ Ψ)

/-- What `stack_map` ensures. -/
abbrev MapPost (f : Frame) (n v : Nat) (fn : UInt32) (s : List UInt32) (j0 a : Nat)
    (Ψ : UInt32 → UInt32 → IProp GF) (vs : List Value) (g : Frame) : IProp GF :=
  iprop(⌜vs = []⌝ ∗ (∃ s', isStack (H := H) v s' n ∗ stackAll2 s s' Ψ) ∗
    ⌜g.inst = f.inst ∧ g.mi = f.mi⌝ ∗ j0 ↦[wt][ fn.toNat ] Ref.func a)

/-- `spec_map_op`. -/
theorem spec_map_op (f : Frame) (n v : Nat) (fn : UInt32) (s : List UInt32) (j0 a : Nat)
    (ctype : FuncType) (cinst : Nat) (cmi : ModuleInst) (ccode : Func) (Φ : UInt32 → IProp GF)
    (Ψ : UInt32 → UInt32 → IProp GF) (hd : d + 1 < lim.maxCallDepth)
    (hct : ctype = { params := [i32t], results := [i32t] }) :
    Triple (H := H) (GF := GF) lim d f
      iprop(⌜f.mi.memAddrs[0]? = some n⌝ ∗ ⌜f.locals[0]? = some (u32 v)⌝ ∗ isStack v s n ∗
        MapPre (H := H) lim d f fn s j0 a ctype cinst cmi ccode Φ Ψ)
      map_op (MapPost (H := H) f n v fn s j0 a Ψ) := by
  intro Φl
  iintro ⟨⟨%hn, %h0, Hs, %h1, %hsz, Hall, %hty, %htab, Ht, #Hf, #Hi, #Hspec⟩, HΦ⟩
  unfold isStack
  icases Hs with ⟨%hdiv, %hle, %hlen, Hp, He, Hfree⟩
  obtain ⟨_, hv, hp⟩ := stack_bounds hdiv hle hlen
  simp only [map_op, map_initialise, List.cons_append, List.nil_append]
  wp_step 0 wpi_local_get 0 (u32 v) h0
  inext; simp only [Post.seq_normal]
  wp_step 1 wpi_load_i32 a0 (UInt32.ofNat v) n v _ hn (by simp [ofNat_toNat_of_lt hv])
  isplitl [Hp]
  · iexact Hp
  inext; iintro Hp; simp only [Post.seq_normal]
  wp_step 1 wpi_local_set 3 (.i32 (UInt32.ofNat (v + s.length * 4)))
  inext; simp only [Post.seq_normal]
  wp_step 0 wpi_local_get 0 (u32 v) (by
    simpa [Frame.withLocals, Array.getElem?_setIfInBounds] using h0)
  inext; simp only [Post.seq_normal]
  wp_step 1 wpi_local_set 2 (u32 v)
  inext; simp only [Post.seq_normal]
  wp_step 0 wpi_block .empty [.loop .empty map_loop_body] [] [] rfl
  inext
  simp only [Exec.blockType, List.length_nil]
  iapply spec_map_loop n v fn s j0 a ctype cinst cmi ccode Φ Ψ hd hct hdiv hle hlen _ s.length _ []
    (by simpa [Frame.withLocals] using hn)
    (by simpa [Frame.withLocals, Array.getElem?_setIfInBounds] using h1)
    (by
      rw [show v + s.length * 4 - 4 * s.length = v by omega]
      simp [Frame.withLocals, Array.getElem?_setIfInBounds]; omega)
    (by simp [Frame.withLocals, Array.getElem?_setIfInBounds]; omega)
    (by simpa [Frame.withLocals] using hsz)
    (by simpa [Frame.withLocals] using hty)
    (by simpa [Frame.withLocals] using htab)
    (by simp)
  simp only [List.take_length, List.append_nil, List.drop_length]
  isplitr
  · iexact Hf
  isplitr
  · iexact Hi
  isplitr
  · iexact Hspec
  isplitl [He]
  · iexact He
  isplitl [Hall]
  · iexact Hall
  isplitr
  · simp only [stackAll2]; iempintro
  isplitl [Ht]
  · iexact Ht
  iintro %s'' %g' ⟨%hl, He, H2, Ht, %hg⟩
  simp only [Post.seq_normal]
  iapply wpi_nil
  iapply HΦ
  isplitr
  · ipureintro; rfl
  isplitl [Hp He Hfree H2]
  · iexists s''
    isplitl [Hp He Hfree]
    · iapply isStack_intro n v s s'' hl hdiv hle hlen
      isplitl [Hp]
      · iexact Hp
      isplitl [He]
      · iexact He
      · iexact Hfree
    · iexact H2
  isplitr
  · ipureintro; exact hg
  · iexact Ht

/-- `spec_stack_map`: `stack_map` maps the callee over the stack. -/
theorem spec_stack_map (f : Frame) (n v : Nat) (fn : UInt32) (s : List UInt32) (j0 a : Nat)
    (ctype : FuncType) (cinst : Nat) (cmi : ModuleInst) (ccode : Func) (Φ : UInt32 → IProp GF)
    (Ψ : UInt32 → UInt32 → IProp GF) (hd : d + 1 < lim.maxCallDepth)
    (hct : ctype = { params := [i32t], results := [i32t] }) :
    Triple (H := H) (GF := GF) lim d f
      iprop(⌜f.mi.memAddrs[0]? = some n⌝ ∗ ⌜f.locals[0]? = some (u32 v)⌝ ∗ isStack v s n ∗
        MapPre (H := H) lim d f fn s j0 a ctype cinst cmi ccode Φ Ψ)
      stack_map (MapPost (H := H) f n v fn s j0 a Ψ) :=
  validated f n v s _ map_op _ (spec_map_op f n v fn s j0 a ctype cinst cmi ccode Φ Ψ hd hct)

end Specs

end WasmLogic.Examples.Stack
