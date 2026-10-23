import WasmLogic.Frag

/-!
# Rules for instructions that do not touch the store

Constants, numeric operations, locals, `drop`, `select`, `nop` and
`unreachable`. Each is Iris-Wasm's rule of the same name (`wp_binop`,
`wp_get_local`, …), restated for fragments: operands on top of `vs`, results
in the postcondition. Rules for the operations that can trap come in a
success and a trap version.
-/

namespace WasmLogic

open Wasm Iris Iris.BI Iris.ProgramLogic

variable {H : Type} {GF : BundledGFunctors} [WasmGS H GF]
variable {lim : ExecLimits} {d : Nat} {f : Frame} {vs : List Value} {Φ : Post H GF}

/-- Shorthand: fall through with `vs'` in the same frame. -/
private theorem pure_same (i : Instr) (vs' : List Value)
    (h : ∀ σ : Store H, ∀ base L R, Exec.instr σ f.mi f.locals (base ++ vs).toArray L i R =
      ⟨σ, .continue (base ++ vs').toArray L R f.locals⟩) :
    ▷ Φ.normal vs' f ⊢ wpi lim d f vs [i] Φ := by
  have := wpi_pure (Φ := Φ) (lim := lim) (d := d) i vs' f.locals h
  simpa using this

/-! ## Control without labels -/

theorem wpi_nop : ▷ Φ.normal vs f ⊢ wpi lim d f vs [.nop] Φ :=
  pure_same _ _ fun _ _ _ _ => rfl

theorem wpi_unreachable : ▷ Φ.trap ⊢ wpi lim d f vs [.unreachable] Φ :=
  wpi_pure_trap _ .unreachable fun _ _ _ _ => rfl

/-! ## Parametric -/

theorem wpi_drop (v : Value) : ▷ Φ.normal vs f ⊢ wpi lim d f (vs ++ [v]) [.drop] Φ :=
  pure_same _ _ fun _ _ _ _ => by simp [Exec.instr]

theorem wpi_select_true (t : Option (List ValType)) (a b : Value) (c : UInt32) (hc : c ≠ 0) :
    ▷ Φ.normal (vs ++ [a]) f ⊢ wpi lim d f (vs ++ [a, b, .i32 c]) [.select t] Φ :=
  pure_same _ _ fun _ _ _ _ => by simp [Exec.instr, Exec.i32, hc]

theorem wpi_select_false (t : Option (List ValType)) (a b : Value) :
    ▷ Φ.normal (vs ++ [b]) f ⊢ wpi lim d f (vs ++ [a, b, .i32 0]) [.select t] Φ :=
  pure_same _ _ fun _ _ _ _ => by simp [Exec.instr, Exec.i32]

/-! ## References -/

theorem wpi_ref_null (t : RefType) :
    ▷ Φ.normal (vs ++ [.ref (.null t)]) f ⊢ wpi lim d f vs [.ref_null t] Φ :=
  pure_same _ _ fun _ _ _ _ => by simp [Exec.instr]

theorem wpi_ref_is_null (r : Ref) :
    ▷ Φ.normal (vs ++ [.i32 (Numeric.bool (match r with | .null _ => true | _ => false))]) f
      ⊢ wpi lim d f (vs ++ [.ref r]) [.ref_is_null] Φ :=
  pure_same _ _ fun _ _ _ _ => by cases r <;> simp [Exec.instr]

theorem wpi_ref_func (i : Nat) :
    ▷ Φ.normal (vs ++ [.ref (.func f.mi.funcAddrs[i]!)]) f ⊢ wpi lim d f vs [.ref_func i] Φ :=
  pure_same _ _ fun _ _ _ _ => by simp [Exec.instr]

/-! ## Locals -/

theorem wpi_local_get (i : Nat) (v : Value) (h : f.locals[i]? = some v) :
    ▷ Φ.normal (vs ++ [v]) f ⊢ wpi lim d f vs [.local_get i] Φ :=
  pure_same _ _ fun _ _ _ _ => by simp [Exec.instr, getElem!_def, h]

theorem wpi_local_set (i : Nat) (v : Value) :
    ▷ Φ.normal vs (f.withLocals (f.locals.set! i v)) ⊢ wpi lim d f (vs ++ [v]) [.local_set i] Φ :=
  wpi_pure _ _ _ fun _ _ _ _ => by simp [Exec.instr]

theorem wpi_local_tee (i : Nat) (v : Value) :
    ▷ Φ.normal (vs ++ [v]) (f.withLocals (f.locals.set! i v))
      ⊢ wpi lim d f (vs ++ [v]) [.local_tee i] Φ :=
  wpi_pure _ _ _ fun _ _ _ _ => by simp [Exec.instr]

/-! ## Constants -/

theorem wpi_i32_const (n : UInt32) :
    ▷ Φ.normal (vs ++ [.i32 n]) f ⊢ wpi lim d f vs [.i32_const n] Φ :=
  pure_same _ _ fun _ _ _ _ => by simp [Exec.instr]

theorem wpi_i64_const (n : UInt64) :
    ▷ Φ.normal (vs ++ [.i64 n]) f ⊢ wpi lim d f vs [.i64_const n] Φ :=
  pure_same _ _ fun _ _ _ _ => by simp [Exec.instr]

theorem wpi_f32_const (n : UInt32) :
    ▷ Φ.normal (vs ++ [.f32 n]) f ⊢ wpi lim d f vs [.f32_const n] Φ :=
  pure_same _ _ fun _ _ _ _ => by simp [Exec.instr]

theorem wpi_f64_const (n : UInt64) :
    ▷ Φ.normal (vs ++ [.f64 n]) f ⊢ wpi lim d f vs [.f64_const n] Φ :=
  pure_same _ _ fun _ _ _ _ => by simp [Exec.instr]

/-! ## Integers -/

theorem wpi_i32_eqz (a : UInt32) :
    ▷ Φ.normal (vs ++ [.i32 (Numeric.bool (a == 0))]) f ⊢ wpi lim d f (vs ++ [.i32 a]) [.i32_eqz] Φ :=
  pure_same _ _ fun _ _ _ _ => by simp [Exec.instr, Exec.i32]

theorem wpi_i64_eqz (a : UInt64) :
    ▷ Φ.normal (vs ++ [.i32 (Numeric.bool (a == 0))]) f ⊢ wpi lim d f (vs ++ [.i64 a]) [.i64_eqz] Φ :=
  pure_same _ _ fun _ _ _ _ => by simp [Exec.instr]

theorem wpi_i32_unop (op : IUnOp) (a : UInt32) :
    ▷ Φ.normal (vs ++ [.i32 (Numeric.iunop32 op a)]) f
      ⊢ wpi lim d f (vs ++ [.i32 a]) [.i32_unop op] Φ :=
  pure_same _ _ fun _ _ _ _ => by simp [Exec.instr, Exec.i32]

theorem wpi_i64_unop (op : IUnOp) (a : UInt64) :
    ▷ Φ.normal (vs ++ [.i64 (Numeric.iunop64 op a)]) f
      ⊢ wpi lim d f (vs ++ [.i64 a]) [.i64_unop op] Φ :=
  pure_same _ _ fun _ _ _ _ => by simp [Exec.instr]

theorem wpi_i32_binop (op : IBinOp) (a b r : UInt32) (h : Numeric.ibinop32 op a b = .ok r) :
    ▷ Φ.normal (vs ++ [.i32 r]) f ⊢ wpi lim d f (vs ++ [.i32 a, .i32 b]) [.i32_binop op] Φ :=
  pure_same _ _ fun _ _ _ _ => by simp [Exec.instr, Exec.i32, h]

theorem wpi_i32_binop_trap (op : IBinOp) (a b : UInt32) (t : Trap)
    (h : Numeric.ibinop32 op a b = .error t) :
    ▷ Φ.trap ⊢ wpi lim d f (vs ++ [.i32 a, .i32 b]) [.i32_binop op] Φ :=
  wpi_pure_trap _ t fun _ _ _ _ => by simp [Exec.instr, Exec.i32, h]

theorem wpi_i64_binop (op : IBinOp) (a b r : UInt64) (h : Numeric.ibinop64 op a b = .ok r) :
    ▷ Φ.normal (vs ++ [.i64 r]) f ⊢ wpi lim d f (vs ++ [.i64 a, .i64 b]) [.i64_binop op] Φ :=
  pure_same _ _ fun _ _ _ _ => by simp [Exec.instr, h]

theorem wpi_i64_binop_trap (op : IBinOp) (a b : UInt64) (t : Trap)
    (h : Numeric.ibinop64 op a b = .error t) :
    ▷ Φ.trap ⊢ wpi lim d f (vs ++ [.i64 a, .i64 b]) [.i64_binop op] Φ :=
  wpi_pure_trap _ t fun _ _ _ _ => by simp [Exec.instr, h]

theorem wpi_i32_relop (op : IRelOp) (a b : UInt32) :
    ▷ Φ.normal (vs ++ [.i32 (Numeric.bool (Numeric.irelop32 op a b))]) f
      ⊢ wpi lim d f (vs ++ [.i32 a, .i32 b]) [.i32_relop op] Φ :=
  pure_same _ _ fun _ _ _ _ => by simp [Exec.instr, Exec.i32]

theorem wpi_i64_relop (op : IRelOp) (a b : UInt64) :
    ▷ Φ.normal (vs ++ [.i32 (Numeric.bool (Numeric.irelop64 op a b))]) f
      ⊢ wpi lim d f (vs ++ [.i64 a, .i64 b]) [.i64_relop op] Φ :=
  pure_same _ _ fun _ _ _ _ => by simp [Exec.instr]

/-! ## Floats, over the runtime's (kernel-opaque) operations -/

theorem wpi_f32_unop (op : FUnOp) (a : UInt32) :
    ▷ Φ.normal (vs ++ [.f32 (Numeric.funop32 op a)]) f
      ⊢ wpi lim d f (vs ++ [.f32 a]) [.f32_unop op] Φ :=
  pure_same _ _ fun _ _ _ _ => by simp [Exec.instr]

theorem wpi_f64_unop (op : FUnOp) (a : UInt64) :
    ▷ Φ.normal (vs ++ [.f64 (Numeric.funop64 op a)]) f
      ⊢ wpi lim d f (vs ++ [.f64 a]) [.f64_unop op] Φ :=
  pure_same _ _ fun _ _ _ _ => by simp [Exec.instr]

theorem wpi_f32_binop (op : FBinOp) (a b : UInt32) :
    ▷ Φ.normal (vs ++ [.f32 (Numeric.fbinop32 op a b)]) f
      ⊢ wpi lim d f (vs ++ [.f32 a, .f32 b]) [.f32_binop op] Φ :=
  pure_same _ _ fun _ _ _ _ => by simp [Exec.instr]

theorem wpi_f64_binop (op : FBinOp) (a b : UInt64) :
    ▷ Φ.normal (vs ++ [.f64 (Numeric.fbinop64 op a b)]) f
      ⊢ wpi lim d f (vs ++ [.f64 a, .f64 b]) [.f64_binop op] Φ :=
  pure_same _ _ fun _ _ _ _ => by simp [Exec.instr]

theorem wpi_f32_relop (op : FRelOp) (a b : UInt32) :
    ▷ Φ.normal (vs ++ [.i32 (Numeric.bool (Numeric.frelop32 op a b))]) f
      ⊢ wpi lim d f (vs ++ [.f32 a, .f32 b]) [.f32_relop op] Φ :=
  pure_same _ _ fun _ _ _ _ => by simp [Exec.instr]

theorem wpi_f64_relop (op : FRelOp) (a b : UInt64) :
    ▷ Φ.normal (vs ++ [.i32 (Numeric.bool (Numeric.frelop64 op a b))]) f
      ⊢ wpi lim d f (vs ++ [.f64 a, .f64 b]) [.f64_relop op] Φ :=
  pure_same _ _ fun _ _ _ _ => by simp [Exec.instr]

/-! ## Conversions -/

theorem wpi_cvt (op : CvtOp) (a r : Value) (h : Numeric.cvt op a = .ok r) :
    ▷ Φ.normal (vs ++ [r]) f ⊢ wpi lim d f (vs ++ [a]) [.cvt op] Φ :=
  pure_same _ _ fun _ _ _ _ => by simp [Exec.instr, h]

theorem wpi_cvt_trap (op : CvtOp) (a : Value) (t : Trap) (h : Numeric.cvt op a = .error t) :
    ▷ Φ.trap ⊢ wpi lim d f (vs ++ [a]) [.cvt op] Φ :=
  wpi_pure_trap _ t fun _ _ _ _ => by simp [Exec.instr, h]

end WasmLogic
