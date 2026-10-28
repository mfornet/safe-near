import Bridge.Functions.ArgsLeaves
import Bridge.Methods.Code296
import Bridge.Methods.BalanceOfArgs

/-!
# The contract of `ft_balance_of`'s argument parser (M6): the statement

`ft_balance_of` (297) reads its arguments with
`serde_json::from_slice::<{ account_id: ValidAccountId }>` (65), which builds a
`SliceRead` (644) and runs `from_trait` (66):

```wat
;; 66 from_trait(out, rd)
Deserializer::new(sp + 48 ⇐ rd)          ;; 634: read (12 bytes), scratch Vec (1, 0, 0), depth 128
deserialize_struct(sp, sp + 48)           ;; 78 → 228 (and 199 functions below it)
Err(e) → out := (1, e)
Ok(v)  → end(sp + 48)                     ;; 320: only whitespace left, else Err
         Err(e) → out := (1, e); drop v
         Ok     → out := (0, v)            ;; v: the account id `String` (ptr, cap, len)
drop the scratch Vec                      ;; 68
```

The functions below 78 are serde_json 1.0.60's reader and serde's derived visitor for the
struct (keys, unknown fields skipped by `ignore_value`, duplicates rejected), near-sdk's
`ValidAccountId` (a `String`, then `is_valid_account_id`), and the error paths (`Error`
boxes formatted with `core::fmt`): about 14 000 instructions. They allocate and free through
wee_alloc, whose specifications so far cover free lists of at most two cells
(`AllocTwoHeap`).

This file states, without proving it, what 66 does, as one Lean proposition
`FromTraitContract`; and proves what it gives at 65's call site (`f65_contract`).

## `FromTraitContract`

On the instantiated module (`wInst`, function `k` at address `k`), from the code of the whole
binary (`funcCells`), for every input `bs` (the slice at `ptr`, `len = bs.length`), a stack
of `S` bytes below `sp`, and a heap `heapInv 0 2048 hl live F` with room for `R · (len + 1)`
more bytes:

* **Accepting:** `Call.decode "ft_balance_of" bs = some (.ftBalanceOf a)` ⇒ `out` holds
  `Ok`: the tag word 0 and the `String` `(p, cap, a.len)`, `p ↦ a`'s UTF-8 bytes (and
  `cap - a.len` more bytes), a block the heap lends (`(p, cap) :: live`).
* **Rejecting:** `Call.decode "ft_balance_of" bs = none` ⇒ `out` holds `Err`: the tag word
  1 and the error box.
* Either way it returns normally (no trap), leaves the input, the stack and the host as they
  were, and costs at most `K0 + K1 · len` `regular_op_cost`s.

Every `Call.decode "ft_balance_of"` result is `none` or some `ftBalanceOf a`
(`decode_shape`), so the two cases are exhaustive. That is the binary's side of `Parses` for
this method in both directions: the binary accepts exactly what the model accepts, with the
model's account, and rejects the rest before any effect (the method has none before the
parse: `env::input` only sets a register).

What `ftBalanceOf_refines_all` needs from it (`notes/todo/wnear_refinement_proof.md`, M6):

* `S` within the 1 MiB shadow stack below 297's frame (297 itself takes 160 bytes);
* `K1 · regular_op_cost ≤ argumentByteGas` less the other per-byte costs of the input (the
  `read_register` byte charges and 523's `vec![0; len]`), i.e. `K1 ≤ 480` under `CostsV86`,
  and `K0` within the method's share of `computeGas`;
* the heap room, from the memory limit and the input's register limit (`LimitsV86`);
* the allocator on any free list, for the code after the parse (`LookupMap::get`, the
  drops), since the parser leaves `F'` free cells.

`balanceOf_accepting_input` (`BalanceOfArgs.decode_balanceOfArgs`) gives the accepting case's
premise on the canonical input `{"account_id":"<a>"}`.
-/

namespace WNear.Binary.FromSliceSpec

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary.VecFromElem (stk)
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.AllocInv (heapInv block)
open WNear.Binary.ArgsLeaves (sliceRead f65_of_66)
open WNear.Binary.InitialState (funcCells)

/-- `Call.decode` of `ft_balance_of`'s arguments is a balance query or nothing. -/
theorem decode_shape (bs : List UInt8) (c : WNear.Call) (h : WNear.Call.decode "ft_balance_of" bs = some c) :
    ∃ a, c = .ftBalanceOf a := by
  simp only [WNear.Call.decode] at h
  revert h
  cases (NearInterface.Json.parse bs).bind (NearInterface.Json.structFields ["account_id"]) with
  | none => simp
  | some fs =>
    cases hr : NearInterface.Json.required WNear.account fs[0]?.join with
    | none => simp [hr]
    | some a =>
      intro h
      refine ⟨a, ?_⟩
      simp [hr] at h
      exact h.symm

/-- The canonical input is accepted with its account (`BalanceOfArgs`). -/
theorem balanceOf_accepting_input (a : WNear.AccountId) :
    WNear.Call.decode "ft_balance_of" (WNear.BalanceOfArgs.balanceOfArgs a) = some (.ftBalanceOf a) :=
  WNear.BalanceOfArgs.decode_balanceOfArgs a

section Statement

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- `Result<Args, serde_json::Error>` at `out` for the input `bs`, the heap after: `Ok` with
the account's bytes in a lent block, or `Err` with the error box; the heap `heapInv` of
the blocks lent before (`live`) and these. -/
def resultAt (n : Nat) (out : UInt32) (bs : List UInt8) (live : List (Nat × Nat)) : IProp GF :=
  match WNear.Call.decode "ft_balance_of" bs with
  | some (.ftBalanceOf a) =>
    iprop(∃ (p cap : UInt32) (hl' F' : Nat), ⌜p ≠ 0 ∧ a.val.utf8ByteSize ≤ cap.toNat⌝ ∗
      n ↦[i32][ out.toNat ] 0 ∗ n ↦[i32][ out.toNat + 4 ] p ∗ n ↦[i32][ out.toNat + 8 ] cap ∗
      n ↦[i32][ out.toNat + 12 ] UInt32.ofNat a.val.utf8ByteSize ∗
      n ↦[wms][ p.toNat ] a.val.toUTF8.toList ∗
      block n (p.toNat + a.val.utf8ByteSize) (cap.toNat - a.val.utf8ByteSize) ∗
      heapInv n 2048 hl' ((p.toNat, cap.toNat) :: live) F')
  | _ =>
    iprop(∃ (e : UInt32) (bs8 : List UInt8) (live' : List (Nat × Nat)) (hl' F' : Nat),
      ⌜bs8.length = 8 ∧ live.Sublist live'⌝ ∗
      n ↦[i32][ out.toNat ] 1 ∗ n ↦[i32][ out.toNat + 4 ] e ∗ n ↦[wms][ out.toNat + 8 ] bs8 ∗
      heapInv n 2048 hl' live' F')

/-- **The contract of `from_trait` (66) for `ft_balance_of`'s arguments**, with the stack
bound `S`, the cost `K0 + K1 · len` and the heap room `R · (len + 1)`. Stated, not proved:
see the module docstring. -/
def FromTraitContract (S K0 K1 R : Nat) : Prop :=
  ∀ (cfg : RuntimeConfig) (h0 : NearState) (lim : ExecLimits) (d : Nat), d + 64 < lim.maxCallDepth →
    ∀ (Cg : Nat) (gt : GlobalType) (sp out rd ptr idx : UInt32) (bs ob : List UInt8) (hl F : Nat)
      (live : List (Nat × Nat)),
    S ≤ sp.toNat → sp.toNat % 16 = 0 → ptr.toNat + bs.length ≤ 2 ^ 32 → bs.length < 2 ^ 28 →
    out.toNat + 16 ≤ 2 ^ 32 → ob.length = 16 → rd.toNat + 12 ≤ 2 ^ 32 →
    hl % 65536 = 0 → 0 < hl → hl + R * (bs.length + 1) ≤ 2048 * 65536 →
    ⊢ ((([∗list] p ∈ funcCells cfg h0, p.1 ↦ₛ□ p.2 : IProp GF)) ∗ (0 ↪[inst] wInst : IProp GF) -∗
      MFunSpec (GF := GF) cfg.wasm lim d types[14]! 0 wInst f66 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 rd]⌝ ∗ 0 ↦[wg] ⟨gt, .i32 sp⟩ ∗
          sliceRead 0 rd ptr (UInt32.ofNat bs.length) 0 ∗ stk 0 (sp.toNat - S) S ∗
          0 ↦[wms][ out.toNat ] ob ∗ 0 ↦[wms][ ptr.toNat ] bs ∗
          vt 0 1057464 idx 0 578 ∗ heapInv 0 2048 hl live F))
        (fun _ => K0 * cfg.wasm.regularOpCost + K1 * cfg.wasm.regularOpCost * bs.length)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ 0 ↦[wg] ⟨gt, .i32 sp⟩ ∗
          (∃ a b c : UInt32, sliceRead 0 rd a b c) ∗ stk 0 (sp.toNat - S) S ∗
          0 ↦[wms][ ptr.toNat ] bs ∗ vt 0 1057464 idx 0 578 ∗ resultAt 0 out bs live)))

/-- **`serde_json::from_slice` (65) for `ft_balance_of`, from `FromTraitContract`**: the
same result at `out`, with 16 more bytes of stack (its `SliceRead`) and 45 more
`regular_op_cost`s. -/
theorem f65_contract (S K0 K1 R : Nat) (hc : FromTraitContract (GF := GF) S K0 K1 R)
    (cfg : RuntimeConfig) (h0 : NearState) (lim : ExecLimits) (d : Nat) (hd : d + 65 < lim.maxCallDepth)
    (Cg : Nat) (gt : GlobalType) (sp out ptr idx : UInt32) (bs ob : List UInt8) (hl F : Nat)
    (live : List (Nat × Nat)) (hS : S + 16 ≤ sp.toNat) (hal : sp.toNat % 16 = 0)
    (hptr : ptr.toNat + bs.length ≤ 2 ^ 32) (hlen : bs.length < 2 ^ 28) (hout : out.toNat + 16 ≤ 2 ^ 32)
    (hob : ob.length = 16) (hl0 : hl % 65536 = 0) (hlpos : 0 < hl)
    (hroom : hl + R * (bs.length + 1) ≤ 2048 * 65536) :
    ([∗list] p ∈ funcCells cfg h0, p.1 ↦ₛ□ p.2) ∗ (0 ↪[inst] wInst : IProp GF) ⊢
      MFunSpec (GF := GF) cfg.wasm lim d types[31]! 0 wInst f65 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 ptr, .i32 (UInt32.ofNat bs.length)]⌝ ∗
          0 ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk 0 (sp.toNat - 16) 16 ∗
          (stk 0 (sp.toNat - 16 - S) S ∗ 0 ↦[wms][ out.toNat ] ob ∗ 0 ↦[wms][ ptr.toNat ] bs ∗
            vt 0 1057464 idx 0 578 ∗ heapInv 0 2048 hl live F)))
        (fun _ => 45 * cfg.wasm.regularOpCost +
          (K0 * cfg.wasm.regularOpCost + K1 * cfg.wasm.regularOpCost * bs.length))
        (fun _ rs => iprop(⌜rs = []⌝ ∗ 0 ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk 0 (sp.toNat - 16) 16 ∗
          (stk 0 (sp.toNat - 16 - S) S ∗ 0 ↦[wms][ ptr.toNat ] bs ∗ vt 0 1057464 idx 0 578 ∗
            resultAt 0 out bs live))) := by
  iintro #HF
  icases HF with ⟨#HF, #Hi⟩
  have hlt := sp.toNat_lt
  have h16 : (sp - 16).toNat = sp.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have hS' : S ≤ (sp - 16).toNat := by omega
  have hal' : (sp - 16).toNat % 16 = 0 := by omega
  have s66 := hc cfg h0 lim (d + 1) (by omega) Cg gt (sp - 16) out (sp - 16) ptr idx bs ob hl F live hS' hal'
    hptr hlen hout hob (by omega) hl0 hlpos hroom
  rw [h16] at s66
  ihave #S66 := s66 $$ [HF Hi]
  · iframe HF Hi
  ihave #F66 : (66 ↪[wf] FuncInst.wasm types[14]! 0 f66 : IProp GF) $$ []
  · iapply InitialState.wasmLeaf cfg h0 66 _ _ (by decide) (by decide) (by kernel_rfl) (by rfl)
    iexact HF
  ihave #F644 : (644 ↪[wf] FuncInst.wasm types[31]! 0 f644 : IProp GF) $$ []
  · iapply InitialState.wasmLeaf cfg h0 644 _ _ (by decide) (by decide) (by kernel_rfl) (by rfl)
    iexact HF
  have r := f65_of_66 (GF := GF) cfg.wasm lim d types[31]! (by rfl) 0 wInst 0 0
    (Interface.wInst_ifaceMod.mem) (Interface.wInst_ifaceMod.glob) 66 644
    (Interface.wInst_ifaceMod.funcs 66 (by decide)) (Interface.wInst_ifaceMod.funcs 644 (by decide))
    (by omega) Cg gt sp out ptr (UInt32.ofNat bs.length) (by omega)
    iprop(stk 0 ((sp - 16).toNat - S) S ∗ 0 ↦[wms][ out.toNat ] ob ∗ 0 ↦[wms][ ptr.toNat ] bs ∗
      vt 0 1057464 idx 0 578 ∗ heapInv 0 2048 hl live F)
    (K0 * cfg.wasm.regularOpCost + K1 * cfg.wasm.regularOpCost * bs.length)
    (fun _ => iprop(stk 0 ((sp - 16).toNat - S) S ∗ 0 ↦[wms][ ptr.toNat ] bs ∗ vt 0 1057464 idx 0 578 ∗
      resultAt 0 out bs live))
  rw [h16] at r
  iapply r
  iframe F644 F66 Hi
  iexact S66

end Statement

end WNear.Binary.FromSliceSpec
