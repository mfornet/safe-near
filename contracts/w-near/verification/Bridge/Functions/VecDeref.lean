import Binary.Code.Part14
import NearLogic.Rules.CallWasm
import NearLogic.Rules.Memory
import NearLogic.Rules.Pure

/-!
# `<Vec<T> as Deref>::deref` (function 779), in the metered logic

The first function of `contract.wasm` proved in the metered separation logic.
`deref(out, vec)` copies the slice `(ptr, len)` of the `Vec` `(ptr, cap, len)`
at `vec` to the 8 bytes at `out`:

```wat
local.get 0  local.get 1  i32.load offset=8  i32.store offset=4
local.get 0  local.get 1  i32.load offset=0  i32.store offset=0
```

`f779_spec` is its `MFunSpec`: 8 instructions, the `out` and `vec` regions
owned separately (so disjoint; the harness's contract `vecDeref` only needs
the length slot `out+4..out+8` to miss the pointer word `vec..vec+4`).
-/

namespace WNear.Binary.VecDeref

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic

/-- An `i32` load of four bytes followed by an `i32` store writes the same four bytes. -/
theorem storeBytes_load_i32 (bs : List UInt8) (h : bs.length = 4) :
    storeBytes (loadValue .i32 none (Memory.decodeLE bs)) 4 = bs := by
  match bs, h with
  | [a, b, c, d], _ =>
    have ha := a.toNat_lt; have hb := b.toNat_lt; have hc := c.toNat_lt; have hd := d.toNat_lt
    simp only [loadValue, storeBytes, storeRaw, Memory.decodeLE, List.foldr, List.range,
      List.range.loop, List.map, Nat.shiftRight_eq_div_pow, List.cons.injEq,
      and_true]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> (apply UInt8.toNat_inj.mp; simp <;> omega)


section Body

variable {GF : BundledGFunctors} [WasmGS NearState GF]

theorem memBytes_split8 (n i : Nat) (ob : List UInt8) (h : ob.length = 8) :
    memBytes (H := NearState) (GF := GF) n i ob ⊢ n ↦[wms][ i ] (ob.take 4) ∗ n ↦[wms][ i + 4 ] (ob.drop 4) := by
  have e := memBytes_append (GF := GF) (H := NearState) n i (ob.take 4) (ob.drop 4)
  rw [List.take_append_drop, List.length_take, show min 4 ob.length = 4 by omega] at e
  exact e.1

theorem memBytes_split12 (n i : Nat) (vb : List UInt8) (h : vb.length = 12) :
    memBytes (H := NearState) (GF := GF) n i vb ⊢ n ↦[wms][ i ] (vb.take 4) ∗ n ↦[wms][ i + 4 ] ((vb.drop 4).take 4) ∗
      n ↦[wms][ i + 8 ] (vb.drop 8) := by
  have e1 := memBytes_append (GF := GF) (H := NearState) n i (vb.take 4) (vb.drop 4)
  rw [List.take_append_drop, List.length_take, show min 4 vb.length = 4 by omega] at e1
  have e2 := memBytes_append (GF := GF) (H := NearState) n (i + 4) ((vb.drop 4).take 4)
    ((vb.drop 4).drop 4)
  rw [List.take_append_drop, List.length_take, List.drop_drop,
    show min 4 (vb.drop 4).length = 4 by simp; omega, Nat.add_assoc] at e2
  iintro H
  icases e1.1 $$ H with ⟨H1, H2⟩
  icases e2.1 $$ H2 with ⟨H2, H3⟩
  isplitl [H1]
  · iexact H1
  isplitl [H2]
  · iexact H2
  · iexact H3

theorem memBytes_join8 (n i : Nat) (a b : List UInt8) (h : a.length = 4) :
    memBytes (H := NearState) (GF := GF) n i a ∗ n ↦[wms][ i + 4 ] b ⊢ n ↦[wms][ i ] (a ++ b) := by
  have e := memBytes_append (GF := GF) (H := NearState) n i a b
  rw [h] at e
  exact e.2

theorem memBytes_join12 (n i : Nat) (vb : List UInt8) (h : vb.length = 12) :
    memBytes (H := NearState) (GF := GF) n i (vb.take 4) ∗ n ↦[wms][ i + 4 ] ((vb.drop 4).take 4) ∗
      n ↦[wms][ i + 8 ] (vb.drop 8) ⊢ n ↦[wms][ i ] vb := by
  have e1 := memBytes_append (GF := GF) (H := NearState) n i (vb.take 4) (vb.drop 4)
  rw [List.take_append_drop, List.length_take, show min 4 vb.length = 4 by omega] at e1
  have e2 := memBytes_append (GF := GF) (H := NearState) n (i + 4) ((vb.drop 4).take 4)
    ((vb.drop 4).drop 4)
  rw [List.take_append_drop, List.length_take, List.drop_drop,
    show min 4 (vb.drop 4).length = 4 by simp; omega, Nat.add_assoc] at e2
  iintro ⟨H1, H2, H3⟩
  iapply e1.2
  isplitl [H1]
  · iexact H1
  iapply e2.2
  isplitl [H2]
  · iexact H2
  · iexact H3

variable {cfg : WasmConfig} {lim : ExecLimits} {d : Nat} {Φ : Post NearState GF} {Cg R : Nat}

/-- The body of `<Vec<T> as Deref>::deref` (function 779): from the 8 bytes at
`out` and the 12 bytes of the `Vec` at `vec` (disjoint, as separate
resources), and credits for its 8 instructions, it falls through with nothing
on the stack, the `Vec` unchanged, and at `out` its pointer word followed by
its length word. -/
theorem body_spec (f : Frame) (out vec : UInt32) (n : Nat) (ob vb : List UInt8)
    (hob : ob.length = 8) (hvb : vb.length = 12)
    (h0 : f.locals[0]? = some (.i32 out)) (h1 : f.locals[1]? = some (.i32 vec))
    (hn : f.mi.memAddrs[0]? = some n) :
    credits Cg (8 * cfg.regularOpCost + R) ∗ n ↦[wms][ out.toNat ] ob ∗
      n ↦[wms][ vec.toNat ] vb ∗
      (credits Cg R -∗ n ↦[wms][ out.toNat ] (vb.take 4 ++ vb.drop 8) -∗
        n ↦[wms][ vec.toNat ] vb -∗ Φ.normal [] f)
      ⊢ mwpi cfg lim d f [] f779.body Φ := by
  iintro ⟨Hc, Ho, Hv, HΦ⟩
  icases memBytes_split8 n out.toNat ob hob $$ Ho with ⟨Ho1, Ho2⟩
  icases memBytes_split12 n vec.toNat vb hvb $$ Hv with ⟨Hv1, Hv2, Hv3⟩
  simp only [f779]
  -- local.get 0
  iapply mwpi_cons
  iapply mwpi_local_get (R := 7 * cfg.regularOpCost + R) 0 (.i32 out) h0
  isplitl [Hc]
  · rw [show 8 * cfg.regularOpCost + R = cfg.regularOpCost + (7 * cfg.regularOpCost + R) by omega]
    iexact Hc
  inext
  iintro Hc
  simp only [Post.mseq_normal]
  -- local.get 1
  iapply mwpi_cons
  iapply mwpi_local_get (R := 6 * cfg.regularOpCost + R) 1 (.i32 vec) h1
  isplitl [Hc]
  · rw [show 7 * cfg.regularOpCost + R = cfg.regularOpCost + (6 * cfg.regularOpCost + R) by omega]
    iexact Hc
  inext
  iintro Hc
  simp only [Post.mseq_normal]
  -- i32.load offset=8
  have hl8 : (vb.drop 8).length = 4 := by simp; omega
  have hne8 : vb.drop 8 ≠ [] := fun h => by simp [h] at hl8
  iapply mwpi_cons
  iapply mwpi_load (R := 5 * cfg.regularOpCost + R) .i32 none ⟨2, 8⟩ vec n (vb.drop 8) hn
    (by simp [loadWidth, NumType.byteWidth, hl8]) hne8
  isplitl [Hc]
  · rw [show 6 * cfg.regularOpCost + R = cfg.regularOpCost + (5 * cfg.regularOpCost + R) by omega]
    iexact Hc
  isplitl [Hv3]
  · iexact Hv3
  inext
  iintro Hv3 Hc
  simp only [Post.mseq_normal]
  -- i32.store offset=4
  have hlo4 : (ob.drop 4).length = 4 := by simp; omega
  have hneo4 : ob.drop 4 ≠ [] := fun h => by simp [h] at hlo4
  iapply mwpi_cons
  rw [List.append_assoc, List.singleton_append]
  iapply mwpi_store (vs := []) (R := 4 * cfg.regularOpCost + R) .i32 none ⟨2, 4⟩ out _ n (ob.drop 4) hn
    (by simp [storeWidth, NumType.byteWidth, hlo4]) hneo4
  isplitl [Hc]
  · rw [show 5 * cfg.regularOpCost + R = cfg.regularOpCost + (4 * cfg.regularOpCost + R) by omega]
    iexact Hc
  isplitl [Ho2]
  · iexact Ho2
  inext
  rw [hlo4, storeBytes_load_i32 _ hl8]
  iintro Ho2 Hc
  simp only [Post.mseq_normal]
  -- local.get 0
  iapply mwpi_cons
  iapply mwpi_local_get (R := 3 * cfg.regularOpCost + R) 0 (.i32 out) h0
  isplitl [Hc]
  · rw [show 4 * cfg.regularOpCost + R = cfg.regularOpCost + (3 * cfg.regularOpCost + R) by omega]
    iexact Hc
  inext
  iintro Hc
  simp only [Post.mseq_normal]
  -- local.get 1
  iapply mwpi_cons
  iapply mwpi_local_get (R := 2 * cfg.regularOpCost + R) 1 (.i32 vec) h1
  isplitl [Hc]
  · rw [show 3 * cfg.regularOpCost + R = cfg.regularOpCost + (2 * cfg.regularOpCost + R) by omega]
    iexact Hc
  inext
  iintro Hc
  simp only [Post.mseq_normal]
  -- i32.load offset=0
  have hl0 : (vb.take 4).length = 4 := by simp; omega
  have hne0 : vb.take 4 ≠ [] := fun h => by simp [h] at hl0
  iapply mwpi_cons
  iapply mwpi_load (R := cfg.regularOpCost + R) .i32 none ⟨2, 0⟩ vec n (vb.take 4) hn
    (by simp [loadWidth, NumType.byteWidth, hl0]) hne0
  isplitl [Hc]
  · rw [show 2 * cfg.regularOpCost + R = cfg.regularOpCost + (cfg.regularOpCost + R) by omega]
    iexact Hc
  isplitl [Hv1]
  · iexact Hv1
  inext
  iintro Hv1 Hc
  simp only [Post.mseq_normal]
  -- i32.store offset=0
  have hlo0 : (ob.take 4).length = 4 := by simp; omega
  have hneo0 : ob.take 4 ≠ [] := fun h => by simp [h] at hlo0
  rw [List.append_assoc, List.singleton_append]
  iapply mwpi_store (vs := []) (R := R) .i32 none ⟨2, 0⟩ out _ n (ob.take 4) hn
    (by simp [storeWidth, NumType.byteWidth, hlo0]) hneo0
  isplitl [Hc]
  · iexact Hc
  isplitl [Ho1]
  · iexact Ho1
  inext
  rw [hlo0, storeBytes_load_i32 _ hl0]
  iintro Ho1 Hc
  ihave Ho := memBytes_join8 n out.toNat (vb.take 4) (vb.drop 8) hl0 $$ [Ho1 Ho2]
  · isplitl [Ho1]
    · iexact Ho1
    · iexact Ho2
  ihave Hv := memBytes_join12 n vec.toNat vb hvb $$ [Hv1 Hv2 Hv3]
  · isplitl [Hv1]
    · iexact Hv1
    isplitl [Hv2]
    · iexact Hv2
    · iexact Hv3
  iapply HΦ $$ Hc Ho Hv

end Body

/-! ## The function -/

section Spec

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The precondition of `deref(out, vec)`: the arguments, the 8 bytes at `out`
and the 12 bytes of the `Vec` at `vec`, owned separately (so the two regions
are disjoint). -/
def pre (n : Nat) (out vec : UInt32) (ob vb : List UInt8) (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 out, .i32 vec]⌝ ∗ n ↦[wms][ out.toNat ] ob ∗ n ↦[wms][ vec.toNat ] vb)

/-- The postcondition: no results, at `out` the `Vec`'s pointer word followed
by its length word, the `Vec` unchanged. -/
def post (n : Nat) (out vec : UInt32) (vb : List UInt8) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = []⌝ ∗ n ↦[wms][ out.toNat ] (vb.take 4 ++ vb.drop 8) ∗ n ↦[wms][ vec.toNat ] vb)

/-- `<Vec<T> as Deref>::deref` (function 779 of `contract.wasm`), at any call
depth, for the memory `n` of its instance: 8 instructions. -/
theorem f779_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (n : Nat)
    (hn : mi.memAddrs[0]? = some n) (Cg : Nat) (out vec : UInt32) (ob vb : List UInt8)
    (hob : ob.length = 8) (hvb : vb.length = 12) :
    ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f779 Cg (pre n out vec ob vb)
      (fun _ => 8 * cfg.regularOpCost) (post n out vec vb) := by
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold pre at HP
  icases HP with ⟨%hargs, Ho, Hv⟩
  subst hargs
  iapply body_spec ⟨entryLocals f779 [.i32 out, .i32 vec], inst, mi⟩ out vec n ob vb hob hvb
    rfl rfl hn
  isplitl [Hc]
  · iexact Hc
  isplitl [Ho]
  · iexact Ho
  isplitl [Hv]
  · iexact Hv
  iintro Hc Ho Hv
  unfold Post.mfunc
  simp only [htype, List.length_nil]
  isplitr
  · ipureintro; exact Nat.zero_le _
  iexists R
  isplitl [Hc]
  · iexact Hc
  iintro Hc
  isplitl [Hc]
  · iexact Hc
  iunfold post
  isplitr
  · ipureintro; rfl
  isplitl [Ho]
  · iexact Ho
  · iexact Hv

end Spec

end WNear.Binary.VecDeref
