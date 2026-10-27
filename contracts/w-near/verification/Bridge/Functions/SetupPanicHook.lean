import Binary.Code.Part10
import Binary.Code.Part14
import NearLogic.Rules.CallWasm
import NearLogic.Rules.Control
import NearLogic.Tactic.Step

/-!
# `env::setup_panic_hook` (function 522), in the metered logic

`setup_panic_hook()` is `std::panic::set_hook(Box::new(panic_hook_impl))`:

```wat
i32.const 0  i32.const 1  call 503        ;; exchange_malloc(0, 1): the ZST box, dangling 1
i32.const 1055136  call 822               ;; set_hook(box, vtable)
```

Below it, on the path taken from a fresh instance:

* `509` `alloc_impl(out, size, align, zeroed)`: for `size = 0`, the dangling
  pointer `align` and length 0 at `out` (11 instructions).
* `508` `<Global as Allocator>::allocate(out, size, align)`: 509 into its frame,
  copied to `out` (24 instructions and the call).
* `503` `exchange_malloc(size, align)`: 508, then the pointer, not null, is
  returned (20 instructions and the call).
* `822` `std::panicking::set_hook(data, vtable)`: with no panic in progress
  (the word at 1074932 zero) and the hook's `RwLock` free (the word at
  1074920 zero), takes the write lock, swaps the hook `(data, vtable)` at
  1074924/1074928 with the new one, releases the lock and, the old hook being
  `Hook::Default` (vtable word zero), drops nothing (31 instructions,
  ending in `return`).

So `setup_panic_hook` leaves the static hook cell `(1, 1055136)` with the lock
free: that points-to is "the panic hook is set up".
-/

namespace WNear.Binary.SetupPanicHook

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic

/-! ## Helpers -/

theorem loadValue_bytes32 (w : UInt32) :
    loadValue .i32 none (Memory.decodeLE (bytes32 w)) = .i32 w := by
  simp [loadValue, decodeLE_bytes32]

theorem aset3_1 (a b c v : Value) : (#[a, b, c] : Array Value).set! 1 v = #[a, v, c] := rfl
theorem aset3_2 (a b c v : Value) : (#[a, b, c] : Array Value).set! 2 v = #[a, b, v] := rfl
theorem aset4_1 (a b c e v : Value) : (#[a, b, c, e] : Array Value).set! 1 v = #[a, v, c, e] := rfl
theorem aset4_2 (a b c e v : Value) : (#[a, b, c, e] : Array Value).set! 2 v = #[a, b, v, e] := rfl
theorem aset4_3 (a b c e v : Value) : (#[a, b, c, e] : Array Value).set! 3 v = #[a, b, c, v] := rfl

theorem blockType_empty (mi : ModuleInst) : Exec.blockType mi .empty = { params := [], results := [] } :=
  rfl

theorem bool_true : Numeric.bool true = 1 := rfl
theorem bool_false : Numeric.bool false = 0 := rfl

/-- Normalise frames, locals, loaded words and block postconditions. -/
macro "mclean" : tactic =>
  `(tactic| (try simp (disch := omega) only [Frame.withLocals, aset3_1, aset3_2, aset4_1, aset4_2,
    aset4_3, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero,
    loadValue_bytes32, storeBytes_i32, Post.mseq_normal, Post.mseq_br, Post.mseq_ret,
    Post.mblock_normal, Post.mblock_br_zero, Post.mblock_br_succ, Post.mblock_ret,
    blockType_empty, List.length_nil, List.nil_append, List.append_nil, List.drop_zero,
    Nat.sub_zero, List.length_cons, List.drop_length, beq_self_eq_true, bool_true]))

section Control

variable {GF : BundledGFunctors} [WasmGS NearState GF]
variable {cfg : WasmConfig} {lim : ExecLimits} {d : Nat} {f : Frame} {vs : List Value}
  {Φ : Post NearState GF} {Cg K : Nat}

theorem mwpi_br_if_true' (n : Nat) {rest : List Value} {c : UInt32} :
    ⌜vs.reverse = .i32 c :: rest ∧ c ≠ 0⌝ ∗ Φ.br n rest.reverse f
      ⊢ mwpi cfg lim d f vs [.br_if n] Φ := by
  iintro ⟨%⟨hs, hc⟩, H⟩
  rw [stack_top1 hs]
  iapply mwpi_br_if_true n c hc $$ H

theorem mwpi_br_if_false' (n : Nat) {rest : List Value} :
    credits Cg K ∗ ⌜vs.reverse = .i32 0 :: rest ∧ cfg.regularOpCost ≤ K ∧ True⌝ ∗
      ▷ (credits Cg (K - cfg.regularOpCost) -∗ Φ.normal rest.reverse f)
      ⊢ mwpi cfg lim d f vs [.br_if n] Φ :=
  credits_flex fun hs _ => by rw [stack_top1 hs]; exact mwpi_br_if_false n

theorem mwpi_block_empty (body : List Instr) :
    credits Cg K ∗ ▷ (credits Cg K -∗ mwpi cfg lim d f [] body (Post.mblock cfg Cg 0 vs Φ))
      ⊢ mwpi cfg lim d f vs [.block .empty body] Φ :=
  mwpi_block0 .empty body vs rfl

theorem pay_intro {k : Nat} {P : IProp GF} :
    credits Cg K ∗ ⌜k ≤ K⌝ ∗ (credits Cg (K - k) -∗ P) ⊢ pay Cg k P := by
  iintro ⟨Hc, %h, HP⟩
  unfold pay
  iexists K - k
  rw [Nat.add_sub_cancel' h]
  iframe Hc
  inext
  iexact HP

end Control

/-- `mstep`-like steps for `block`, `br_if` and `return`. -/
macro "mblock" : tactic => do
  let hc := Lean.mkIdent `Hc
  `(tactic| (
    first
      | (iapply mwpi_cons; iapply mwpi_block_empty)
      | iapply mwpi_block_empty
    isplitl [$hc:ident]
    · iexact $hc:ident
    inext
    iintro $hc:ident
    mclean))

macro "mbr_if_taken" : tactic =>
  `(tactic| (
    first
      | (iapply mwpi_cons; iapply mwpi_br_if_true')
      | iapply mwpi_br_if_true'
    isplitr
    · ipureintro; exact ⟨rfl, by first | decide | assumption⟩
    mclean))

macro "mbr_if_not" : tactic => do
  let hc := Lean.mkIdent `Hc
  `(tactic| (
    first
      | (iapply mwpi_cons; iapply mwpi_br_if_false')
      | iapply mwpi_br_if_false'
    isplitl [$hc:ident]
    · iexact $hc:ident
    isplitr
    · ipureintro; exact ⟨rfl, by omega, trivial⟩
    inext
    iintro $hc:ident
    mclean))

/-- Pay for the step leaving a block by a branch (`Post.mblock`'s `br 0`). -/
macro "mpay" : tactic => do
  let hc := Lean.mkIdent `Hc
  `(tactic| (
    isplitr
    · ipureintro; simp
    iapply pay_intro
    isplitl [$hc:ident]
    · iexact $hc:ident
    isplitr
    · ipureintro; omega
    iintro $hc:ident
    mclean))

/-! ## `std::panicking::set_hook` (822) -/

section SetHook

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The hook's static cells: no panic in progress, the lock word, the hook. -/
def hookCells (n : Nat) (lock data vtable : UInt32) : IProp GF :=
  iprop(n ↦[i32][ 1074932 ] 0 ∗ n ↦[i32][ 1074920 ] lock ∗ n ↦[i32][ 1074924 ] data ∗
    n ↦[i32][ 1074928 ] vtable)

def setHookPre (n : Nat) (data vtable old : UInt32) (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 data, .i32 vtable]⌝ ∗ hookCells n 0 old 0)

def setHookPost (n : Nat) (data vtable : UInt32) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = []⌝ ∗ hookCells n 0 data vtable)

theorem entryLocals_f822 (a b : UInt32) :
    entryLocals f822 [.i32 a, .i32 b] = #[.i32 a, .i32 b, .i32 0] := rfl

/-- `set_hook(data, vtable)` (822) over the default hook, with the lock free
and no panic in progress: 31 instructions. -/
theorem f822_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (n : Nat)
    (hn : mi.memAddrs[0]? = some n) (Cg : Nat) (data vtable old : UInt32) :
    ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f822 Cg (setHookPre n data vtable old)
      (fun _ => 31 * cfg.regularOpCost) (setHookPost n data vtable) := by
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold setHookPre, hookCells at HP
  icases HP with ⟨%hargs, Hpc, Hl, Hd, Hv⟩
  subst hargs
  rw [entryLocals_f822]
  ihave Hpc := (memBytes_congr (j := (0 : UInt32).toNat + 1074932) (by simp)).1 $$ Hpc
  ihave Hl := (memBytes_congr (j := (0 : UInt32).toNat + 1074920) (by simp)).1 $$ Hl
  ihave Hd := (memBytes_congr (j := (0 : UInt32).toNat + 1074924) (by simp)).1 $$ Hd
  ihave Hv := (memBytes_congr (j := (0 : UInt32).toNat + 1074928) (by simp)).1 $$ Hv
  simp only [f822]
  mblock; mblock; mblock
  mstep; mstep [Hpc]; mclean; mstep
  mbr_if_taken
  mpay
  -- the lock: taken for writing
  mstep; mstep [Hl]; mclean; mstep; mclean
  mstep; mstep; mstep [Hl]
  mstep; mclean
  mbr_if_not
  -- the hook swapped
  mstep; mstep [Hv]; mclean; mstep; mclean
  mstep; mstep; mclean; mstep [Hv]
  mstep; mstep [Hd]; mclean; mstep; mclean
  mstep; mstep; mclean; mstep [Hd]
  -- the lock released
  mstep; mstep; mstep [Hl]
  -- the old hook is the default: nothing to drop
  mblock
  mstep; mclean; mstep; mclean
  mbr_if_taken
  mpay
  iapply mwpi_return
  mclean
  unfold Post.mfunc
  simp only [htype, List.length_nil]
  isplitr
  · ipureintro; exact Nat.zero_le _
  iexists R
  isplitl [Hc]
  · iapply credits_le
    isplitl [Hc]
    · iexact Hc
    · ipureintro; omega
  iintro Hc
  iframe Hc
  iunfold setHookPost, hookCells
  simp only [show (0 : UInt32).toNat = 0 from rfl, Nat.zero_add]
  iframe Hpc Hl Hd Hv
  ipureintro; rfl

end SetHook

/-- Pay nothing to fall off the end of a block (`Post.mblock`'s `normal`). -/
macro "mpay0" : tactic => do
  let hc := Lean.mkIdent `Hc
  `(tactic| (
    iapply pay_intro
    isplitl [$hc:ident]
    · iexact $hc:ident
    isplitr
    · ipureintro; omega
    iintro $hc:ident
    mclean))

/-! ## `alloc_impl` (509), for a zero size -/

section AllocImpl

variable {GF : BundledGFunctors} [WasmGS NearState GF]

def allocImplPre (n : Nat) (out align z o1 o2 : UInt32) (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 out, .i32 0, .i32 align, .i32 z]⌝ ∗ n ↦[i32][ out.toNat ] o1 ∗
    n ↦[i32][ out.toNat + 4 ] o2)

/-- The dangling pointer `align` and the length 0 at `out`. -/
def allocImplPost (n : Nat) (out align : UInt32) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = []⌝ ∗ n ↦[i32][ out.toNat ] align ∗ n ↦[i32][ out.toNat + 4 ] 0)

theorem entryLocals_f509 (a b c e : UInt32) :
    entryLocals f509 [.i32 a, .i32 b, .i32 c, .i32 e] = #[.i32 a, .i32 b, .i32 c, .i32 e] := rfl

/-- `alloc_impl(out, 0, align, zeroed)` (509): 11 instructions. -/
theorem f509_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (n : Nat)
    (hn : mi.memAddrs[0]? = some n) (Cg : Nat) (out align z o1 o2 : UInt32) :
    ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f509 Cg (allocImplPre n out align z o1 o2)
      (fun _ => 11 * cfg.regularOpCost) (allocImplPost n out align) := by
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold allocImplPre at HP
  icases HP with ⟨%hargs, Ho1, Ho2⟩
  subst hargs
  rw [entryLocals_f509]
  simp only [f509]
  mblock; mblock
  mstep; mclean; mstep; mclean
  mbr_if_taken
  mpay
  mstep; mstep; mclean
  mpay0
  mstep; mstep; mclean; mstep [Ho2]
  mstep; mstep; mclean; mstep [Ho1]
  unfold Post.mfunc
  simp only [htype, List.length_nil]
  isplitr
  · ipureintro; exact Nat.zero_le _
  iexists R
  iframe Hc
  iintro Hc
  iunfold allocImplPost
  simp only [storeBytes_i32]
  iframe Hc Ho1 Ho2
  ipureintro; rfl

end AllocImpl

theorem toNat_plus8 (x : UInt32) (h : x.toNat + 8 < 2 ^ 32) : (x + 8).toNat = x.toNat + 8 := by
  simp [UInt32.toNat_add]; omega

theorem toNat_minus16 (x : UInt32) (h : 16 ≤ x.toNat) : (x - 16).toNat = x.toNat - 16 := by
  rw [UInt32.toNat_sub_of_le] <;> simp_all [UInt32.le_iff_toNat_le]

section Calls

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- `mwpi_call_spec` on a stack holding just the arguments. -/
theorem mwpi_call_spec_args {cfg : WasmConfig} {lim : ExecLimits} {d : Nat} {f : Frame}
    {Φ : Post NearState GF} (i a : Nat) (type : FuncType) (inst : Nat) (mi : ModuleInst)
    (code : Func) (args : List Value) {Cg R : Nat} (P : List Value → IProp GF)
    (K : List Value → Nat) (Q : List Value → List Value → IProp GF)
    (ha : f.mi.funcAddrs[i]? = some a) (hlen : args.length = type.params.length)
    (hd : d + 1 < lim.maxCallDepth) :
    credits Cg (cfg.regularOpCost + activationGas cfg.regularOpCost (entryLocals code args) +
        (K args + R)) ∗
      a ↪[wf] FuncInst.wasm type inst code ∗ inst ↪[inst] mi ∗
      MFunSpec cfg lim (d + 1) type inst mi code Cg P K Q ∗ P args ∗
      ▷ (∀ rs, credits Cg R -∗ Q args rs -∗ Φ.normal rs f)
      ⊢ mwpi cfg lim d f args [.call i] Φ :=
  mwpi_call_spec (vs₀ := []) i a type inst mi code args P K Q ha hlen hd

end Calls

/-! ## `<Global as Allocator>::allocate` (508), for a zero size -/

section Allocate

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The arguments, the stack pointer, the two words of the frame `alloc_impl`
writes (at `sp - 8`), and the two words at `out`. -/
def allocatePre (n g : Nat) (gi : GlobalInst) (sp out align w1 w2 o1 o2 : UInt32)
    (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 out, .i32 0, .i32 align]⌝ ∗ g ↦[wg] gi ∗
    n ↦[i32][ (sp - 16).toNat + 8 ] w1 ∗ n ↦[i32][ (sp - 16).toNat + 12 ] w2 ∗
    n ↦[i32][ out.toNat ] o1 ∗ n ↦[i32][ out.toNat + 4 ] o2)

def allocatePost (n g : Nat) (gi : GlobalInst) (sp out align : UInt32) (_args rs : List Value) :
    IProp GF :=
  iprop(⌜rs = []⌝ ∗ g ↦[wg] gi ∗
    n ↦[i32][ (sp - 16).toNat + 8 ] align ∗ n ↦[i32][ (sp - 16).toNat + 12 ] 0 ∗
    n ↦[i32][ out.toNat ] align ∗ n ↦[i32][ out.toNat + 4 ] 0)

theorem entryLocals_f508 (a b c : UInt32) :
    entryLocals f508 [.i32 a, .i32 b, .i32 c] = #[.i32 a, .i32 b, .i32 c, .i32 0] := rfl

theorem activation_f509 (c : Nat) (a b e h : UInt32) :
    activationGas c (entryLocals f509 [.i32 a, .i32 b, .i32 e, .i32 h]) = 10 * c := by
  simp [activationGas, entryLocals, f509]

/-- `allocate(out, 0, align)` (508): 24 instructions and `alloc_impl` (its
activation 10 and its 11 instructions), 45 in all. -/
theorem f508_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (n g a509 : Nat)
    (hn : mi.memAddrs[0]? = some n) (hg : mi.globalAddrs[0]? = some g)
    (ha : mi.funcAddrs[509]? = some a509) (ty509 : FuncType) (hty1 : ty509.params.length = 4)
    (hty2 : ty509.results = []) (hd : d + 1 < lim.maxCallDepth) (Cg : Nat)
    (gi : GlobalInst) (sp out align w1 w2 o1 o2 : UInt32) (hgi : gi.value = .i32 sp)
    (hsp : 16 ≤ sp.toNat) :
    a509 ↪[wf] FuncInst.wasm ty509 inst f509 ∗ inst ↪[inst] mi
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f508 Cg
        (allocatePre n g gi sp out align w1 w2 o1 o2)
        (fun _ => 45 * cfg.regularOpCost) (allocatePost n g gi sp out align) := by
  iintro ⟨#Hf, #Hi⟩
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold allocatePre at HP
  icases HP with ⟨%hargs, Hg, Hw1, Hw2, Ho1, Ho2⟩
  subst hargs
  obtain ⟨gt, gv⟩ := gi
  simp only at hgi
  subst hgi
  have hlt := sp.toNat_lt
  have h16 := toNat_minus16 sp hsp
  have h8 : (sp - 16 + 8).toNat = (sp - 16).toNat + 8 := toNat_plus8 _ (by omega)
  rw [entryLocals_f508]
  simp only [f508]
  -- sp -= 16
  mstep [Hg]; mstep; mstep; mstep; mclean; mstep [Hg]
  -- alloc_impl(sp - 8, 0, align, 0)
  mstep; mstep; mstep; mstep; mclean; mstep; mclean; mstep
  ihave Hw1 := (memBytes_congr (j := (sp - 16 + 8).toNat) h8.symm).1 $$ Hw1
  ihave Hw2 := (memBytes_congr (j := (sp - 16 + 8).toNat + 4) (by omega)).1 $$ Hw2
  iapply mwpi_cons
  iapply mwpi_call_spec_args (R := 12 * cfg.regularOpCost + R) 509 a509 ty509 inst mi f509
    [.i32 (sp - 16 + 8), .i32 0, .i32 align, .i32 0]
    (allocImplPre n (sp - 16 + 8) align 0 w1 w2) (fun _ => 11 * cfg.regularOpCost)
    (allocImplPost n (sp - 16 + 8) align) ha (by simp [hty1]) hd
  isplitl [Hc]
  · rw [activation_f509]
    iapply credits_le
    isplitl [Hc]
    · iexact Hc
    · ipureintro; omega
  isplitr; iexact Hf
  isplitr; iexact Hi
  isplitr
  · iapply f509_spec cfg lim (d + 1) ty509 hty2 inst mi n hn Cg
  isplitl [Hw1 Hw2]
  · iunfold allocImplPre
    iframe Hw1 Hw2
    ipureintro; rfl
  inext
  iintro %rs Hc HQ
  iunfold allocImplPost at HQ
  icases HQ with ⟨%hrs, Hw1, Hw2⟩
  subst hrs
  mclean
  ihave Hw1 := (memBytes_congr (j := (sp - 16).toNat + 8) h8).1 $$ Hw1
  ihave Hw2 := (memBytes_congr (j := (sp - 16).toNat + 12) (by omega)).1 $$ Hw2
  -- the result copied to out
  mstep; mstep; mclean; mstep [Hw1]; mclean; mstep [Ho1]
  mstep; mstep; mclean; mstep [Hw2]; mclean; mstep [Ho2]
  -- sp += 16
  mstep; mclean; mstep; mstep; mstep [Hg]
  have e : sp - 16 + 16 = sp := by simp
  simp only [e]
  unfold Post.mfunc
  simp only [htype, List.length_nil]
  isplitr
  · ipureintro; exact Nat.zero_le _
  iexists R
  iframe Hc
  iintro Hc
  iunfold allocatePost
  iframe Hc Hg Hw1 Hw2 Ho1 Ho2
  ipureintro; rfl

end Allocate

/-! ## `exchange_malloc` (503), for a zero size -/

section ExchangeMalloc

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The arguments, the stack pointer, the two words of its frame `allocate`
writes (at `sp - 8`), and the two of `allocate`'s frame (at `sp - 24`). -/
def mallocPre (n g : Nat) (gi : GlobalInst) (sp align a1 a2 b1 b2 : UInt32)
    (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 0, .i32 align]⌝ ∗ g ↦[wg] gi ∗
    n ↦[i32][ (sp - 16).toNat + 8 ] a1 ∗ n ↦[i32][ (sp - 16).toNat + 12 ] a2 ∗
    n ↦[i32][ (sp - 16 - 16).toNat + 8 ] b1 ∗ n ↦[i32][ (sp - 16 - 16).toNat + 12 ] b2)

/-- The dangling pointer `align` returned. -/
def mallocPost (n g : Nat) (gi : GlobalInst) (sp align : UInt32) (_args rs : List Value) :
    IProp GF :=
  iprop(⌜rs = [.i32 align]⌝ ∗ g ↦[wg] gi ∗
    n ↦[i32][ (sp - 16).toNat + 8 ] align ∗ n ↦[i32][ (sp - 16).toNat + 12 ] 0 ∗
    n ↦[i32][ (sp - 16 - 16).toNat + 8 ] align ∗ n ↦[i32][ (sp - 16 - 16).toNat + 12 ] 0)

theorem entryLocals_f503 (a b : UInt32) :
    entryLocals f503 [.i32 a, .i32 b] = #[.i32 a, .i32 b, .i32 0, .i32 0] := rfl

theorem activation_f508 (c : Nat) (a b e : UInt32) :
    activationGas c (entryLocals f508 [.i32 a, .i32 b, .i32 e]) = 10 * c := by
  simp [activationGas, entryLocals, f508, ValType.default]

/-- `exchange_malloc(0, align)` (503), `align` not zero: 20 instructions and
`allocate` (its activation 10 and its 45), 75 in all. -/
theorem f503_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (n g a508 a509 : Nat)
    (hn : mi.memAddrs[0]? = some n) (hg : mi.globalAddrs[0]? = some g)
    (ha8 : mi.funcAddrs[508]? = some a508) (ha9 : mi.funcAddrs[509]? = some a509)
    (ty508 ty509 : FuncType) (hty8 : ty508.params.length = 3) (hty8' : ty508.results = [])
    (hty9 : ty509.params.length = 4) (hty9' : ty509.results = [])
    (hd : d + 2 < lim.maxCallDepth) (Cg : Nat)
    (gi : GlobalInst) (sp align a1 a2 b1 b2 : UInt32) (hgi : gi.value = .i32 sp)
    (hsp : 32 ≤ sp.toNat) (halign : align ≠ 0) :
    a508 ↪[wf] FuncInst.wasm ty508 inst f508 ∗ a509 ↪[wf] FuncInst.wasm ty509 inst f509 ∗
      inst ↪[inst] mi
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f503 Cg
        (mallocPre n g gi sp align a1 a2 b1 b2)
        (fun _ => 75 * cfg.regularOpCost) (mallocPost n g gi sp align) := by
  iintro ⟨#Hf8, #Hf9, #Hi⟩
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold mallocPre at HP
  icases HP with ⟨%hargs, Hg, Ha1, Ha2, Hb1, Hb2⟩
  subst hargs
  obtain ⟨gt, gv⟩ := gi
  simp only at hgi
  subst hgi
  have hlt := sp.toNat_lt
  have h16 := toNat_minus16 sp (by omega)
  have h32 := toNat_minus16 (sp - 16) (by omega)
  have h8 : (sp - 16 + 8).toNat = (sp - 16).toNat + 8 := toNat_plus8 _ (by omega)
  rw [entryLocals_f503]
  simp only [f503]
  -- sp -= 16
  mstep [Hg]; mstep; mstep; mstep; mclean; mstep [Hg]
  -- allocate(sp - 8, 0, align)
  mstep; mstep; mstep; mstep; mclean; mstep; mclean
  ihave Ha1 := (memBytes_congr (j := (sp - 16 + 8).toNat) h8.symm).1 $$ Ha1
  ihave Ha2 := (memBytes_congr (j := (sp - 16 + 8).toNat + 4) (by omega)).1 $$ Ha2
  iapply mwpi_cons
  iapply mwpi_call_spec_args (R := 9 * cfg.regularOpCost + R) 508 a508 ty508 inst mi f508
    [.i32 (sp - 16 + 8), .i32 0, .i32 align]
    (allocatePre n g { type := gt, value := .i32 (sp - 16) } (sp - 16) (sp - 16 + 8) align
      b1 b2 a1 a2)
    (fun _ => 45 * cfg.regularOpCost)
    (allocatePost n g { type := gt, value := .i32 (sp - 16) } (sp - 16) (sp - 16 + 8) align)
    ha8 (by simp [hty8]) (by omega)
  isplitl [Hc]
  · rw [activation_f508]
    iapply credits_le
    isplitl [Hc]
    · iexact Hc
    · ipureintro; omega
  isplitr; iexact Hf8
  isplitr; iexact Hi
  isplitr
  · iapply f508_spec cfg lim (d + 1) ty508 hty8' inst mi n g a509 hn hg ha9 ty509 hty9 hty9'
      (by omega) Cg { type := gt, value := .i32 (sp - 16) } (sp - 16) (sp - 16 + 8) align
      b1 b2 a1 a2 rfl (by omega)
    iframe Hf9 Hi
  isplitl [Hg Ha1 Ha2 Hb1 Hb2]
  · iunfold allocatePre
    iframe Hg Ha1 Ha2 Hb1 Hb2
    ipureintro; rfl
  inext
  iintro %rs Hc HQ
  iunfold allocatePost at HQ
  icases HQ with ⟨%hrs, Hg, Hb1, Hb2, Ha1, Ha2⟩
  subst hrs
  mclean
  ihave Ha1 := (memBytes_congr (j := (sp - 16).toNat + 8) h8).1 $$ Ha1
  ihave Ha2 := (memBytes_congr (j := (sp - 16).toNat + 12) (by omega)).1 $$ Ha2
  -- the pointer, not null
  mblock
  mstep; mclean; mstep [Ha1]; mclean; mstep; mclean
  mbr_if_taken
  mpay
  -- sp += 16, return the pointer
  mstep; mclean; mstep; mstep; mstep [Hg]; mstep; mclean
  have e : sp - 16 + 16 = sp := by simp
  simp only [e]
  unfold Post.mfunc
  simp only [htype]
  isplitr
  · ipureintro; simp
  iexists R
  iframe Hc
  iintro Hc
  iunfold mallocPost
  iframe Hc Hg Ha1 Ha2 Hb1 Hb2
  ipureintro; rfl

end ExchangeMalloc

/-! ## `env::setup_panic_hook` (522) -/

section SetupPanicHook

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The stack pointer, the four words of the frames below it that the
allocation writes, and the hook's static cells: no panic in progress, the
lock free, the default hook. -/
def pre (n g : Nat) (gi : GlobalInst) (sp a1 a2 b1 b2 old : UInt32) (args : List Value) :
    IProp GF :=
  iprop(⌜args = []⌝ ∗ g ↦[wg] gi ∗
    n ↦[i32][ (sp - 16).toNat + 8 ] a1 ∗ n ↦[i32][ (sp - 16).toNat + 12 ] a2 ∗
    n ↦[i32][ (sp - 16 - 16).toNat + 8 ] b1 ∗ n ↦[i32][ (sp - 16 - 16).toNat + 12 ] b2 ∗
    hookCells n 0 old 0)

/-- The panic hook set up: the hook is near-sdk's `panic_hook_impl`, a
zero-sized box (the dangling pointer 1) with the vtable at 1055136; the lock
free. -/
def post (n g : Nat) (gi : GlobalInst) (sp : UInt32) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = []⌝ ∗ g ↦[wg] gi ∗
    n ↦[i32][ (sp - 16).toNat + 8 ] 1 ∗ n ↦[i32][ (sp - 16).toNat + 12 ] 0 ∗
    n ↦[i32][ (sp - 16 - 16).toNat + 8 ] 1 ∗ n ↦[i32][ (sp - 16 - 16).toNat + 12 ] 0 ∗
    hookCells n 0 1 1055136)

theorem entryLocals_f522 : entryLocals f522 [] = #[] := rfl

theorem activation_f503 (c : Nat) (a b : UInt32) :
    activationGas c (entryLocals f503 [.i32 a, .i32 b]) = 10 * c := by
  simp [activationGas, entryLocals, f503, ValType.default]

theorem activation_f822 (c : Nat) (a b : UInt32) :
    activationGas c (entryLocals f822 [.i32 a, .i32 b]) = 10 * c := by
  simp [activationGas, entryLocals, f822, ValType.default]

/-- `env::setup_panic_hook` (function 522 of `contract.wasm`), from the
statics of a fresh instance: 5 instructions, `exchange_malloc(0, 1)` (its
activation 10 and its 75) and `set_hook` (its activation 10 and its 31), 131
in all. -/
theorem f522_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (n g a503 a508 a509 a822 : Nat)
    (hn : mi.memAddrs[0]? = some n) (hg : mi.globalAddrs[0]? = some g)
    (ha3 : mi.funcAddrs[503]? = some a503) (ha8 : mi.funcAddrs[508]? = some a508)
    (ha9 : mi.funcAddrs[509]? = some a509) (ha2 : mi.funcAddrs[822]? = some a822)
    (ty503 ty508 ty509 ty822 : FuncType) (hty3 : ty503.params.length = 2)
    (hty3' : ty503.results.length = 1) (hty8 : ty508.params.length = 3)
    (hty8' : ty508.results = []) (hty9 : ty509.params.length = 4) (hty9' : ty509.results = [])
    (hty2 : ty822.params.length = 2) (hty2' : ty822.results = [])
    (hd : d + 3 < lim.maxCallDepth) (Cg : Nat)
    (gi : GlobalInst) (sp a1 a2 b1 b2 old : UInt32) (hgi : gi.value = .i32 sp)
    (hsp : 32 ≤ sp.toNat) :
    a503 ↪[wf] FuncInst.wasm ty503 inst f503 ∗ a508 ↪[wf] FuncInst.wasm ty508 inst f508 ∗
      a509 ↪[wf] FuncInst.wasm ty509 inst f509 ∗ a822 ↪[wf] FuncInst.wasm ty822 inst f822 ∗
      inst ↪[inst] mi
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f522 Cg (pre n g gi sp a1 a2 b1 b2 old)
        (fun _ => 131 * cfg.regularOpCost) (post n g gi sp) := by
  iintro ⟨#Hf3, #Hf8, #Hf9, #Hf2, #Hi⟩
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold pre at HP
  icases HP with ⟨%hargs, Hg, Ha1, Ha2, Hb1, Hb2, Hh⟩
  subst hargs
  rw [entryLocals_f522]
  simp only [f522]
  mstep; mstep
  -- exchange_malloc(0, 1)
  iapply mwpi_cons
  iapply mwpi_call_spec_args (R := 43 * cfg.regularOpCost + R) 503 a503 ty503 inst mi f503
    [.i32 0, .i32 1] (mallocPre n g gi sp 1 a1 a2 b1 b2) (fun _ => 75 * cfg.regularOpCost)
    (mallocPost n g gi sp 1) ha3 (by simp [hty3]) (by omega)
  isplitl [Hc]
  · rw [activation_f503]
    iapply credits_le
    isplitl [Hc]
    · iexact Hc
    · ipureintro; omega
  isplitr; iexact Hf3
  isplitr; iexact Hi
  isplitr
  · iapply f503_spec cfg lim (d + 1) ty503 hty3' inst mi n g a508 a509 hn hg ha8 ha9 ty508 ty509
      hty8 hty8' hty9 hty9' (by omega) Cg gi sp 1 a1 a2 b1 b2 hgi hsp (by decide)
    iframe Hf8 Hf9 Hi
  isplitl [Hg Ha1 Ha2 Hb1 Hb2]
  · iunfold mallocPre
    iframe Hg Ha1 Ha2 Hb1 Hb2
    ipureintro; rfl
  inext
  iintro %rs Hc HQ
  iunfold mallocPost at HQ
  icases HQ with ⟨%hrs, Hg, Ha1, Ha2, Hb1, Hb2⟩
  subst hrs
  mclean
  -- set_hook(1, 1055136)
  mstep
  iapply mwpi_call_spec_args (R := R) 822 a822 ty822 inst mi f822
    [.i32 1, .i32 1055136] (setHookPre n 1 1055136 old) (fun _ => 31 * cfg.regularOpCost)
    (setHookPost n 1 1055136) ha2 (by simp [hty2]) (by omega)
  isplitl [Hc]
  · rw [activation_f822]
    iapply credits_le
    isplitl [Hc]
    · iexact Hc
    · ipureintro; omega
  isplitr; iexact Hf2
  isplitr; iexact Hi
  isplitr
  · iapply f822_spec cfg lim (d + 1) ty822 hty2' inst mi n hn Cg 1 1055136 old
  isplitl [Hh]
  · iunfold setHookPre
    iframe Hh
    ipureintro; rfl
  inext
  iintro %rs Hc HQ
  iunfold setHookPost at HQ
  icases HQ with ⟨%hrs, Hh⟩
  subst hrs
  unfold Post.mfunc
  simp only [htype, List.length_nil]
  isplitr
  · ipureintro; exact Nat.zero_le _
  iexists R
  iframe Hc
  iintro Hc
  iunfold post
  iframe Hc Hg Ha1 Ha2 Hb1 Hb2 Hh
  ipureintro; rfl

end SetupPanicHook

end WNear.Binary.SetupPanicHook
