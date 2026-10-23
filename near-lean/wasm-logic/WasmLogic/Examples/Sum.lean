import WasmLogic.Adequacy
import WasmLogic.Tactic

/-!
# A worked example: a counting loop, for every input

`sumTo` is a hand-built module with one function `sum : [i32] → [i32]`
computing `1 + 2 + ... + n` (modulo `2^32`) with a `loop`, locals and
`br_if`. The specification is proved for every `n` by stepping through the
code with the instruction rules, by induction on the loop counter; adequacy
then turns it into a statement about every run of `Exec.run`.
-/

namespace WasmLogic.Examples

open Wasm Iris Iris.BI Iris.ProgramLogic WasmLogic

/-- `local 0` is `n`, `local 1` accumulates. -/
def sumLoop : List Instr := [
  .local_get 0, .i32_eqz, .br_if 1,
  .local_get 1, .local_get 0, .i32_binop .add, .local_set 1,
  .local_get 0, .i32_const 1, .i32_binop .sub, .local_set 0,
  .br 0]

def sumBody : Expr := [.block .empty [.loop .empty sumLoop], .local_get 1]

def sumType : FuncType := { params := [.i32], results := [.i32] }

def sumFunc : Func := { type := 0, locals := [.i32], body := sumBody }

def sumTo : Module :=
  { types := #[sumType], funcs := #[sumFunc], exports := #[{ name := "sum", desc := .func 0 }] }

/-- `0 + 1 + ... + m`, wrapping. -/
def tri : Nat → UInt32
  | 0 => 0
  | m + 1 => tri m + UInt32.ofNat (m + 1)

section Proof

variable {H : Type} {GF : BundledGFunctors} [WasmGS H GF] {lim : ExecLimits} {d : Nat}

/-- What the block around the loop does once the loop is done: read the
accumulator and return it. -/
abbrev afterLoop (Φf : FunPost GF) : Post H GF :=
  Post.block 0 [] (Post.seq lim d [.local_get 1] (Post.func 1 Φf))

/-- The loop, from counter `k` and accumulator `acc`, adds up to `tri N`. -/
theorem loop_spec (inst : Nat) (mi : ModuleInst) (N : Nat) (Φf : FunPost GF) :
    ∀ m (k acc : UInt32), k.toNat = m → acc + tri m = tri N →
      Φf.ret [.i32 (tri N)] ⊢
        wpi lim d ⟨#[.i32 k, .i32 acc], inst, mi⟩ [] [.loop .empty sumLoop]
          (afterLoop (lim := lim) (d := d) Φf) := by
  intro m
  induction m with
  | zero =>
    intro k acc hk hacc
    have hk0 : k = 0 := UInt32.toNat_inj.mp (by simpa using hk)
    subst hk0
    simp only [tri, UInt32.add_zero] at hacc
    subst hacc
    iintro HΦ
    wp_apply 0 wpi_loop .empty sumLoop [] [] rfl
    inext
    simp only [sumLoop, Exec.blockType, List.length_nil]
    wp_step 0 wpi_local_get 0 (.i32 0) rfl
    inext; simp only [Post.seq_normal]
    wp_step 1 wpi_i32_eqz 0
    inext; simp only [Post.seq_normal]
    wp_step 1 wpi_br_if_true 1 _ (by decide)
    simp only [Post.seq_br, Post.loop, Post.block, List.append_nil, List.length_nil, List.drop_nil]
    isplitr
    · ipureintro; simp
    simp only [Post.seq_normal]
    wp_step 0 wpi_local_get 1 (.i32 (tri N)) rfl
    inext; simp only [Post.seq_normal]
    iapply wpi_nil
    simp only [Post.func]
    isplitr
    · ipureintro; simp
    simp only [List.nil_append, List.length_singleton, Nat.sub_self, List.drop_zero]
    iexact HΦ
  | succ m ih =>
    intro k acc hk hacc
    have hk0 : k ≠ 0 := fun h => by subst h; simp at hk
    iintro HΦ
    wp_apply 0 wpi_loop .empty sumLoop [] [] rfl
    inext
    simp only [sumLoop, Exec.blockType, List.length_nil]
    wp_step 0 wpi_local_get 0 (.i32 k) rfl
    inext; simp only [Post.seq_normal]
    wp_step 1 wpi_i32_eqz k
    inext; simp only [Post.seq_normal]
    have hb : Numeric.bool (k == 0) = 0 := by simp [Numeric.bool, hk0]
    rw [hb]
    wp_step 1 wpi_br_if_false 1
    inext; simp only [Post.seq_normal]
    wp_step 0 wpi_local_get 1 (.i32 acc) rfl
    inext; simp only [Post.seq_normal]
    wp_step 0 wpi_local_get 0 (.i32 k) rfl
    inext; simp only [Post.seq_normal]
    wp_step 2 wpi_i32_binop .add acc k (acc + k) rfl
    inext; simp only [Post.seq_normal]
    wp_step 1 wpi_local_set 1 (.i32 (acc + k))
    inext; simp only [Post.seq_normal]
    wp_step 0 wpi_local_get 0 (.i32 k) rfl
    inext; simp only [Post.seq_normal]
    wp_step 0 wpi_i32_const 1
    inext; simp only [Post.seq_normal]
    wp_step 2 wpi_i32_binop .sub k 1 (k - 1) rfl
    inext; simp only [Post.seq_normal]
    wp_step 1 wpi_local_set 0 (.i32 (k - 1))
    inext; simp only [Post.seq_normal]
    wp_step 0 wpi_br 0
    simp only [Post.seq_br, Post.loop, Frame.withLocals]
    isplitr
    · ipureintro; simp
    have hk1 : (k - 1).toNat = m := by
      have h1 : (1 : UInt32) ≤ k := by rw [UInt32.le_iff_toNat_le]; simp [hk]
      rw [UInt32.toNat_sub_of_le _ _ h1]; simp [hk]
    have hk2 : k = UInt32.ofNat (m + 1) := by rw [← hk, UInt32.ofNat_toNat]
    have hacc' : acc + k + tri m = tri N := by
      rw [← hacc, hk2]; simp only [tri]; ac_rfl
    have hih := ih (k - 1) (acc + k) hk1 hacc'
    simp only [sumLoop] at hih
    simp only [List.append_nil, List.length_nil, List.drop_nil]
    wp_locals
    iapply hih $$ HΦ

/-- The specification of `sum`, as a function: it returns `tri n`. -/
theorem sum_spec (inst : Nat) (mi : ModuleInst) (n : UInt32) (Φf : FunPost GF) :
    Φf.ret [.i32 (tri n.toNat)] ⊢ wpInvoke lim d sumType inst mi sumFunc [.i32 n] Φf := by
  iintro HΦ
  iapply wpInvoke_intro
  simp only [sumFunc, sumBody, entryLocals, sumType]
  wp_step 0 wpi_block .empty [.loop .empty sumLoop] [] [] rfl
  inext
  simp only [Exec.blockType, List.length_nil, List.map_cons, List.map_nil, ValType.default]
  rw [show (#[Value.i32 n] ++ #[Value.i32 0] : Array Value) = #[.i32 n, .i32 0] from rfl]
  iapply loop_spec inst mi n.toNat Φf n.toNat n 0 rfl (by simp) $$ HΦ

end Proof

end WasmLogic.Examples

/-! ## End to end: validation, instantiation and every run -/

namespace WasmLogic.Examples

open Wasm Iris Iris.BI Iris.ProgramLogic WasmLogic

/-- The module instance `sumTo` instantiates to. -/
def sumInst : ModuleInst :=
  { types := #[sumType], funcAddrs := #[0], exports := #[("sum", .func 0)] }

/-- The store `sumTo` instantiates to, with no host state. -/
def sumStore : Store Unit :=
  { funcs := #[.wasm sumType 0 sumFunc], modules := #[sumInst], host := () }

/-- `sumTo` validates under nearcore's features and instantiates to
`sumStore`: the kernel runs the validator and the linker. -/
theorem sumTo_instantiates :
    (do let vm ← (sumTo.validate (.nearcore false)).toOption
        (Link.instantiateModule (Store.empty ()) vm []).toOption) = some (sumStore, sumInst) := by
  kernel_rfl

/-- Every run of `sum n` that finishes returns `tri n`, and none traps. -/
theorem sum_adequate (n : UInt32) (c : Config Unit)
    (hc : Exec.startWasm sumStore {} sumInst.funcAddrs[0]! [.i32 n] = some c) (fuel : Nat) :
    match Exec.run fuel c with
    | .done vs _ => vs = [.i32 (tri n.toNat)]
    | .trap _ _ => False
    | .outOfFuel _ => True := by
  have h := adequacy sumStore {} 0 [.i32 n] sumType 0 sumInst sumFunc rfl
    (fun vs => vs = [.i32 (tri n.toNat)]) False ?_ c hc fuel
  · revert h
    cases Exec.run fuel c <;> exact id
  intro _
  have hl : Iris.Std.get? (heapOf sumStore) (Loc.inst 0) = some (.inst sumInst) := by
    rw [get?_heapOf]; rfl
  iintro Hcells
  icases (BigSepM.bigSepM_delete hl).1 $$ Hcells with ⟨Hi, -⟩
  imod pointsTo_persist $$ Hi with #Hi
  imodintro
  isplitr
  · iunfold instPt; iexact Hi
  · iapply sum_spec
    ipureintro
    rfl

end WasmLogic.Examples
