import Bridge.Functions.ArgsLeaves
import Bridge.Functions.SerdeFromTrait
import Bridge.Methods.Code296
import Bridge.Methods.BalanceOfArgs

/-!
# The contracts of `ft_balance_of`'s argument parser (M6)

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

`Refines` asks two different things of the parser, so its contract has two halves.

* **Accepting (`AcceptContract`).** When `Call.decode "ft_balance_of" bs = some (.ftBalanceOf a)`,
  66 returns `Ok(a)` (`okAt`) within `K0 + K1 · len` `regular_op_cost`s plus a constant `X` (the
  allocation of the account's `String`, which the allocator charges partly in other units). The
  cost is tight: the method's gas bound pays for it.
* **Rejecting (`RejectContract`).** When `Call.decode … = none`, 66 returns `Err(box)` (`errAt`), at
  *some* finite cost. `Refines` needs only that a rejected input fails with no effects, and a run that
  runs out of gas fails too (`method_vm_any`), so no bound is asked. Stated, not proved.

Both run on the instantiated module (`wInst`, function `k` at address `k`) from the code of the whole
binary, the instance and the memory limit (`codeCtx`), with a stack of `S` bytes below `sp`, the
input `bs` at `ptr` (`ptr + len < 2^32`, `len + 1 < 2^28`), the read-only data the parser reads
(`roData`: the `ESCAPE` table at 1062392, the UTF-8 width table at 1071704, the field name at
1051092, given back), and a heap `heapInv 0 2048 hl live F` with room for an error box's page
(`roomFor4 hl 2048 20`).

`acceptContract` proves the accepting half from `SerdeFromTrait.f66_dec`, for any callees that satisfy
`AcceptCallees`: readers `dv` (169) and `ign` (81) that agree with the model, the specifications of
the functions not proved yet (`Hyp646` on keys, `Hyp169`, `Hyp81`, at 66's `Deserializer`,
`sp - 64`), and the cost bound `cost66 ≤ (K0 + K1 · len) · c + X`. `SerdeCost` derives that bound
from linear bounds on the callees' costs. `f65_accept` and `f65_reject` carry both halves to 65's call
site.

Every `Call.decode "ft_balance_of"` result is `none` or some `ftBalanceOf a` (`decode_shape`), so the
two halves are exhaustive.

What `ftBalanceOf_refines_all` needs from it (`notes/todo/wnear_refinement_proof.md`, M6):

* `S` within the 1 MiB shadow stack below 297's frame (297 itself takes 160 bytes);
* `K1 · regular_op_cost ≤ argumentByteGas` less the other per-byte costs of the input (the
  `read_register` byte charges and 523's `vec![0; len]`), i.e. `K1 ≲ 480` under `CostsV86`, and `K0`
  and `X` within the method's share of `computeGas`;
* the heap room, from the memory limit and the input's register limit (`LimitsV86`);
* the allocator on any free list, for the code after the parse (`LookupMap::get`, the drops).

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
open WNear.Binary.SerdeErrBox (roomFor4)
open WNear.Binary.SerdeStructArr (strRes Hyp169)
open WNear.Binary.SerdeStructObj (Hyp646 Hyp81)
open WNear.Binary.SerdeFromTrait (code66 cost66 f66_dec)
open WNear.SerdeStructModel (Agrees valueAs valueSkip)

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

/-- The persistent context of the parser: the binary's code, the instance and the memory limit. -/
noncomputable def codeCtx (cfg : RuntimeConfig) (h0 : NearState) : IProp GF :=
  iprop(([∗list] p ∈ funcCells cfg h0, p.1 ↦ₛ□ p.2) ∗ (0 ↪[inst] wInst) ∗ 0 ↪[wmlimit] some 2048)

instance (cfg : RuntimeConfig) (h0 : NearState) : Persistent (codeCtx (GF := GF) cfg h0) := by
  unfold codeCtx; infer_instance

/-- The read-only data the parser reads: the `ESCAPE` table, the UTF-8 width table, the field name. -/
def roData (n : Nat) : IProp GF :=
  iprop(n ↦[wms][ 1062392 ] WNear.Binary.ParseStr.escTable ∗ n ↦[wms][ 1071704 ] WNear.Binary.FromUtf8Gen.utf8Width ∗
    n ↦[wms][ 1051092 ] WNear.BalanceOfArgs.keyBytes)

/-- `Ok(a)` at `out`: the tag word 0 and the `String` `(p, cap, |a|)`, `p ↦ a`'s UTF-8 bytes and
`cap - |a|` more bytes, a block the heap lends (`(p, cap) :: live`). -/
def okAt (n : Nat) (out : UInt32) (a : WNear.AccountId) (live : List (Nat × Nat)) : IProp GF :=
  iprop(∃ (p cap : UInt32) (hl' F' : Nat), ⌜p ≠ 0 ∧ a.val.utf8ByteSize ≤ cap.toNat⌝ ∗
    n ↦[i32][ out.toNat ] 0 ∗ n ↦[i32][ out.toNat + 4 ] p ∗ n ↦[i32][ out.toNat + 8 ] cap ∗
    n ↦[i32][ out.toNat + 12 ] UInt32.ofNat a.val.utf8ByteSize ∗
    n ↦[wms][ p.toNat ] a.val.toUTF8.toList ∗
    block n (p.toNat + a.val.utf8ByteSize) (cap.toNat - a.val.utf8ByteSize) ∗
    heapInv n 2048 hl' ((p.toNat, cap.toNat) :: live) F')

/-- `Err(e)` at `out`: the tag word 1 and the error box `e`, the heap lending at least `live`. -/
def errAt (n : Nat) (out : UInt32) (live : List (Nat × Nat)) : IProp GF :=
  iprop(∃ (e : UInt32) (bs8 : List UInt8) (live' : List (Nat × Nat)) (hl' F' : Nat),
    ⌜bs8.length = 8 ∧ live.Sublist live'⌝ ∗
    n ↦[i32][ out.toNat ] 1 ∗ n ↦[i32][ out.toNat + 4 ] e ∗ n ↦[wms][ out.toNat + 8 ] bs8 ∗
    heapInv n 2048 hl' live' F')

/-- 66's precondition: `sp`, `out`, the `SliceRead` at `rd` over `bs` at `ptr`, a stack of `S` bytes. -/
def pre66 (S : Nat) (gt : GlobalType) (sp out rd ptr idx : UInt32) (bs ob : List UInt8) (hl F : Nat)
    (live : List (Nat × Nat)) (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 out, .i32 rd]⌝ ∗ 0 ↦[wg] ⟨gt, .i32 sp⟩ ∗
    sliceRead 0 rd ptr (UInt32.ofNat bs.length) 0 ∗ (stk 0 (sp.toNat - S) S ∗
    0 ↦[wms][ out.toNat ] ob ∗ 0 ↦[wms][ ptr.toNat ] bs ∗ roData 0 ∗
    vt 0 1057464 idx 0 578 ∗ heapInv 0 2048 hl live F))

/-- 66's postcondition, with the result `res` at `out`. -/
def post66 (S : Nat) (gt : GlobalType) (sp rd ptr idx : UInt32) (bs : List UInt8) (res : IProp GF)
    (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = []⌝ ∗ 0 ↦[wg] ⟨gt, .i32 sp⟩ ∗
    (∃ a b c : UInt32, sliceRead 0 rd a b c) ∗ (stk 0 (sp.toNat - S) S ∗
    0 ↦[wms][ ptr.toNat ] bs ∗ roData 0 ∗ vt 0 1057464 idx 0 578 ∗ res))

/-- **The callees of the accepting path that are not proved yet**, at 66's `Deserializer` `de`
over `bs`: readers `dv` (169) and `ign` (81) that agree with the model; the specifications `Hyp646`
(keys), `Hyp169` (the account id) and `Hyp81` (ignored values), with the costs `K646`, `K169`,
`K81`; and 66's cost under them within `(K0 + K1 · len) · c + X`. -/
def AcceptCallees (cfg : RuntimeConfig) (h0 : NearState) (lim : ExecLimits) (Cg : Nat) (gt : GlobalType)
    (de ptr idx : UInt32) (bs : List UInt8) (K0 K1 X : Nat) : Prop :=
  ∃ (dv : List UInt8 → Option (WNear.AccountId × List UInt8)) (ign : List UInt8 → Option (Unit × List UInt8))
    (K646 K169 K81 : Nat → Nat),
    Agrees dv (valueAs WNear.account) ∧ Agrees ign valueSkip ∧
    Hyp646 cfg.wasm lim 0 wInst 0 0 0 id Cg gt de ptr idx bs 2048 K646 (codeCtx (GF := GF) cfg h0) ∧
    Hyp169 cfg.wasm lim 0 wInst 0 0 0 id Cg gt de ptr idx bs 2048 dv K169 (codeCtx (GF := GF) cfg h0) ∧
    Hyp81 cfg.wasm lim 0 wInst 0 0 0 id Cg gt de ptr idx bs 2048 ign K81 (codeCtx (GF := GF) cfg h0) ∧
    cost66 cfg.wasm K646 K169 K81 dv ign bs ≤ (K0 + K1 * bs.length) * cfg.wasm.regularOpCost + X

/-- **The accepting contract of `from_trait` (66)** for `ft_balance_of`'s arguments: on an input the
model reads as `ftBalanceOf a`, `Ok(a)` at `out` (`okAt`), within `(K0 + K1 · len) · c + X`, given the
callees (`AcceptCallees`). -/
def AcceptContract (S K0 K1 X : Nat) : Prop :=
  ∀ (cfg : RuntimeConfig) (h0 : NearState) (lim : ExecLimits) (d : Nat), d + 64 < lim.maxCallDepth →
    ∀ (Cg : Nat) (gt : GlobalType) (sp out rd ptr idx : UInt32) (bs ob : List UInt8) (hl F : Nat)
      (live : List (Nat × Nat)) (a : WNear.AccountId),
    S ≤ sp.toNat → sp.toNat % 16 = 0 → ptr.toNat + bs.length < 2 ^ 32 → bs.length + 1 < 2 ^ 28 →
    out.toNat + 16 ≤ 2 ^ 32 → ob.length = 16 → rd.toNat + 12 ≤ 2 ^ 32 → roomFor4 hl 2048 20 →
    WNear.Call.decode "ft_balance_of" bs = some (.ftBalanceOf a) →
    AcceptCallees (GF := GF) cfg h0 lim Cg gt (sp - 64) ptr idx bs K0 K1 X →
    ⊢ (codeCtx (GF := GF) cfg h0 -∗
      MFunSpec (GF := GF) cfg.wasm lim d types[14]! 0 wInst f66 Cg
        (pre66 S gt sp out rd ptr idx bs ob hl F live)
        (fun _ => (K0 + K1 * bs.length) * cfg.wasm.regularOpCost + X)
        (post66 S gt sp rd ptr idx bs (okAt 0 out a live)))

/-- **The rejecting contract of `from_trait` (66)**: on an input the model rejects, `Err(box)` at
`out` (`errAt`), at some finite cost. Stated, not proved. -/
def RejectContract (S : Nat) : Prop :=
  ∀ (cfg : RuntimeConfig) (h0 : NearState) (lim : ExecLimits) (d : Nat), d + 64 < lim.maxCallDepth →
    ∀ (Cg : Nat) (gt : GlobalType) (sp out rd ptr idx : UInt32) (bs ob : List UInt8) (hl F : Nat)
      (live : List (Nat × Nat)),
    S ≤ sp.toNat → sp.toNat % 16 = 0 → ptr.toNat + bs.length < 2 ^ 32 → bs.length + 1 < 2 ^ 28 →
    out.toNat + 16 ≤ 2 ^ 32 → ob.length = 16 → rd.toNat + 12 ≤ 2 ^ 32 → roomFor4 hl 2048 20 →
    WNear.Call.decode "ft_balance_of" bs = none →
    ∃ K : Nat, ⊢ (codeCtx (GF := GF) cfg h0 -∗
      MFunSpec (GF := GF) cfg.wasm lim d types[14]! 0 wInst f66 Cg
        (pre66 S gt sp out rd ptr idx bs ob hl F live)
        (fun _ => K)
        (post66 S gt sp rd ptr idx bs (errAt 0 out live)))

open WNear.Binary.InitialState in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- The code 66 runs on its accepting path, from the store's function cells. -/
theorem code66_of (cfg : RuntimeConfig) (h : NearState) :
    codeCtx (GF := GF) cfg h ⊢ code66 0 2048 0 wInst id := by
  iintro #Hctx
  iunfold codeCtx at Hctx
  icases Hctx with ⟨#HF, #Hi, #Hm⟩
  simp only [code66, SerdeNextKey.code193, SerdeEnds.endCode, SerdeErrBox.errCode, AllocTwo.code310, id]
  repeat' (first
    | iexact Hi
    | iexact Hm
    | (iapply wasmLeaf cfg h _ _ _ ?_ ?_ ?_ ?_ <;> first | iexact HF | decide | kernel_rfl | rfl)
    | isplitl [])


end Statement

end WNear.Binary.FromSliceSpec
