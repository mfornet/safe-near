import WasmLogic.Examples.Bulk
import WasmLogic.Adequacy

/-!
# Structural rules at work

Small fragments that use the structural rules the larger examples do not:
`br_table`, `memory.size`, traps (`unreachable`, division by zero), the
call-depth limit, a call to a host function against its contract, and the
frame rule.
-/

namespace WasmLogic.Examples

open Wasm Iris Iris.BI Iris.ProgramLogic WasmLogic

section Proof

variable {H : Type} {GF : BundledGFunctors} [WasmGS H GF] {lim : ExecLimits} {d : Nat}

/-- `br_table` leaves the block whatever the index: both targets are 0. -/
theorem br_table_spec (f : Frame) (k : UInt32) (Φ : Post H GF) (hk : f.locals[0]? = some (.i32 k)) :
    Φ.normal [.i32 7] f ⊢
      wpi lim d f [] [.block (.val (.num .i32)) [.i32_const 7, .local_get 0, .br_table [0] 0]] Φ := by
  iintro HΦ
  wp_step 0 wpi_block (.val (.num .i32)) [.i32_const 7, .local_get 0, .br_table [0] 0] [] [] rfl
  inext
  wp_step 0 wpi_i32_const 7
  inext; simp only [Post.seq_normal]
  wp_step 0 wpi_local_get 0 (.i32 k) hk
  inext; simp only [Post.seq_normal]
  wp_step 1 wpi_br_table [0] 0 k
  have hl : ([0] : List Nat)[k.toNat]?.getD 0 = 0 := by
    rcases h : k.toNat with _ | n <;> simp
  rw [hl]
  simp only [Post.seq_br, Post.block, Exec.blockType, List.length_singleton, Post.seq_normal]
  isplitr
  · ipureintro; exact Nat.le_refl _
  iapply wpi_nil
  simp only [Nat.sub_self, List.drop_zero, List.nil_append]
  iexact HΦ

/-- `memory.size` reads the owned length, in pages. -/
theorem memory_size_spec (f : Frame) (n len : Nat) (Φ : Post H GF) (hn : f.mi.memAddrs[0]? = some n) :
    n ↦[wmlength] len ∗ (n ↦[wmlength] len -∗ Φ.normal [.i32 (UInt32.ofNat (len / pageSize))] f)
      ⊢ wpi lim d f [] [.memory_size] Φ := by
  iintro ⟨Hl, HΦ⟩
  iapply wpi_memory_size n len hn
  isplitl [Hl]
  · iexact Hl
  · inext; simp only [List.nil_append]; iexact HΦ

/-- `unreachable` traps; `nop` before it does nothing. -/
theorem unreachable_spec (f : Frame) (Φ : Post H GF) : Φ.trap ⊢ wpi lim d f [] [.nop, .unreachable] Φ := by
  iintro HΦ
  wp_step 0 wpi_nop
  inext; simp only [Post.seq_normal]
  iapply wpi_unreachable
  inext
  iexact HΦ

/-- Division by zero traps. -/
theorem div_zero_spec (f : Frame) (Φ : Post H GF) :
    Φ.trap ⊢ wpi lim d f [] [.i32_const 1, .i32_const 0, .i32_binop .div_u] Φ := by
  iintro HΦ
  wp_step 0 wpi_i32_const 1
  inext; simp only [Post.seq_normal]
  wp_step 0 wpi_i32_const 0
  inext; simp only [Post.seq_normal]
  wp_step 2 wpi_i32_binop_trap .div_u 1 0 .integerDivideByZero rfl
  inext
  simp only [Post.seq_trap]
  iexact HΦ

/-- A call at the call-depth limit traps instead of calling. -/
theorem exhausted_spec (f : Frame) (a : Nat) (type : FuncType) (inst : Nat) (code : Func) (Φ : Post H GF)
    (ha : f.mi.funcAddrs[0]? = some a) (hd : lim.maxCallDepth ≤ d + 1) :
    a ↪[wf] FuncInst.wasm type inst code ∗ Φ.trap ⊢ wpi lim d f [] [.call 0] Φ := by
  iintro ⟨Hf, HΦ⟩
  iapply wpi_call_exhausted 0 a type inst code [] ha hd
  isplitl [Hf]
  · iexact Hf
  · inext; iexact HΦ

/-- A host function that returns its arguments and leaves everything else
alone. -/
def echo : HostFn H where
  type := { params := [.num .i32], results := [.num .i32] }
  call h mem args := .return args h mem

theorem echo_contract (h : H) (mx : Option Nat) (bs : List UInt8) (v : Value) :
    HostContract echo h [v] mx bs [v] h bs := by
  intro mem hwf hsz hmx hrd
  exact ⟨mem, rfl, hwf, hsz, hmx, hrd⟩

/-- Calling `echo` through its contract. -/
theorem host_call_spec (f : Frame) (a n : Nat) (h : H) (mx : Option Nat) (bs : List UInt8) (Φ : Post H GF)
    (ha : f.mi.funcAddrs[0]? = some a) (hn : f.mi.memAddrs[0]? = some n) :
    a ↪[wf] FuncInst.host echo ∗ n ↪[wmlimit] mx ∗ ↦[host] h ∗ n ↦[wmlength] bs.length ∗ n ↦[wms][ 0 ] bs ∗
      (↦[host] h ∗ n ↦[wmlength] bs.length ∗ n ↦[wms][ 0 ] bs -∗ Φ.normal [.i32 5] f)
      ⊢ wpi lim d f [] [.i32_const 5, .call 0] Φ := by
  iintro ⟨#Hf, #Hl, Hh, Hlen, Hb, HΦ⟩
  wp_step 0 wpi_i32_const 5
  inext; simp only [Post.seq_normal]
  wp_step 1 wpi_call_host 0 a n echo h h mx bs bs [] [.i32 5] [.i32 5] ha hn rfl (echo_contract h mx bs _)
  isplitr
  · iexact Hf
  isplitr
  · iexact Hl
  isplitl [Hh]
  · iexact Hh
  isplitl [Hlen]
  · iexact Hlen
  isplitl [Hb]
  · iexact Hb
  inext
  iintro H'
  simp only [Post.seq_normal, List.nil_append]
  iapply wpi_nil
  iapply HΦ $$ H'

/-- The frame rule: `fillCopy` keeps a resource it never touches. -/
theorem fillCopy_framed (f : Frame) (n : Nat) (o₁ o₂ : List UInt8) (R : IProp GF)
    (hn : f.mi.memAddrs[0]? = some n) (h₁ : o₁.length = 4) (h₂ : o₂.length = 4) :
    R ∗ n ↦[wms][ 8 ] o₁ ∗ n ↦[wms][ 16 ] o₂ ⊢
      wpi lim d f [] fillCopy (Post.frame R
        { normal := fun vs g => iprop(⌜vs = [] ∧ g = f⌝ ∗ n ↦[wms][ 8 ] List.replicate 4 0xAB ∗
            n ↦[wms][ 16 ] List.replicate 4 0xAB),
          br := fun _ _ _ => iprop(False), ret := fun _ _ => iprop(False), trap := iprop(False) }) := by
  iintro ⟨HR, H₁, H₂⟩
  iapply wpi_frame
  isplitl [HR]
  · iexact HR
  iapply fillCopy_spec f n o₁ o₂ _ hn h₁ h₂
  isplitl [H₁]
  · iexact H₁
  isplitl [H₂]
  · iexact H₂
  iintro ⟨H₁, H₂⟩
  isplitr
  · ipureintro; exact ⟨rfl, rfl⟩
  isplitl [H₁]
  · iexact H₁
  · iexact H₂

end Proof

end WasmLogic.Examples
