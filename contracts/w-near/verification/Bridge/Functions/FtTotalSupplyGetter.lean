import Binary.Code.Part08
import Bridge.Functions.U128From

/-!
# `FungibleToken::ft_total_supply` (function 414), in the metered logic

`ft_total_supply(out, ft)` copies the `u128` total supply, the first 16 bytes
of the `FungibleToken` at `ft`, to `out`, through `U128::from` (566) on a
16-byte frame of the shadow stack:

```wat
global.get 0  i32.const 16  i32.sub  local.tee 2  global.set 0      ;; sp -= 16
local.get 2  local.get 1  i64.load  local.get 1  i32.const 8  i32.add  i64.load
call 566                                                           ;; frame := from(lo, hi)
local.get 2  i64.load  local.set 3
local.get 0  local.get 2  i32.const 8  i32.add  i64.load  i64.store offset=8
local.get 0  local.get 3  i64.store
local.get 2  i32.const 16  i32.add  global.set 0                    ;; sp += 16
```

`f414_spec` is its `MFunSpec`: 29 instructions and the call to 566 (its
activation 11 and its 6 instructions), 46 in all; with the activation 11
paid by the caller this is the harness's 57 (`ftTotalSupply`).
-/

namespace WNear.Binary.FtTotalSupplyGetter

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary.U128From (u128Bytes memBytes_split memBytes_join)

/-- An `i64` load of eight bytes followed by an `i64` store writes the same eight bytes. -/
theorem storeBytes_load_i64 (bs : List UInt8) (h : bs.length = 8) :
    storeBytes (loadValue .i64 none (Memory.decodeLE bs)) 8 = bs := by
  match bs, h with
  | [a, b, c, d, e, f, g, k], _ =>
    have ha := a.toNat_lt; have hb := b.toNat_lt; have hc := c.toNat_lt; have hd := d.toNat_lt
    have he := e.toNat_lt; have hf := f.toNat_lt; have hg := g.toNat_lt; have hk := k.toNat_lt
    simp only [loadValue, storeBytes, storeRaw, Memory.decodeLE, List.foldr, List.range,
      List.range.loop, List.map, Nat.shiftRight_eq_div_pow, List.cons.injEq, and_true]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (apply UInt8.toNat_inj.mp; simp <;> omega)

/-- `U128::from` on the two words loaded from `tb` writes `tb` back. -/
theorem u128Bytes_load (tb : List UInt8) (h : tb.length = 16) :
    u128Bytes (UInt64.ofNat (Memory.decodeLE (tb.take 8)))
      (UInt64.ofNat (Memory.decodeLE (tb.drop 8))) = tb := by
  have h1 := storeBytes_load_i64 (tb.take 8) (by simp; omega)
  have h2 := storeBytes_load_i64 (tb.drop 8) (by simp; omega)
  simp only [loadValue] at h1 h2
  rw [u128Bytes, h1, h2, List.take_append_drop]

theorem activation_f566 (c : Nat) (x : UInt32) (lo hi : UInt64) :
    activationGas c (entryLocals f566 [.i32 x, .i64 lo, .i64 hi]) = 11 * c := by
  simp [activationGas, entryLocals, f566]

theorem toNat_add8 (x : UInt32) (h : x.toNat + 8 < 2 ^ 32) : (x + 8).toNat = x.toNat + 8 := by
  simp [UInt32.toNat_add]; omega

/-! The frame of 414, its locals as a literal array. -/

theorem entryLocals_f414 (out ft : UInt32) :
    entryLocals f414 [.i32 out, .i32 ft] = #[.i32 out, .i32 ft, .i32 0, .i64 0] := rfl

theorem withLocals_set (inst : Nat) (mi : ModuleInst) (l : Array Value) (i : Nat) (v : Value) :
    (⟨l, inst, mi⟩ : Frame).withLocals (l.set! i v) = ⟨l.set! i v, inst, mi⟩ := rfl

theorem set2 (a b c e v : Value) : (#[a, b, c, e] : Array Value).set! 2 v = #[a, b, v, e] := rfl
theorem set3 (a b c e v : Value) : (#[a, b, c, e] : Array Value).set! 3 v = #[a, b, c, v] := rfl

section Spec

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

/-- The precondition of `ft_total_supply(out, ft)`: the arguments, the stack
pointer `sp` in global `g`, the 16 bytes of the frame below it, the 16 bytes
at `out`, and the total supply's 16 bytes at `ft`, all owned separately. -/
def pre (n g : Nat) (gi : GlobalInst) (sp out ft : UInt32) (fb ob tb : List UInt8)
    (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 out, .i32 ft]⌝ ∗ g ↦[wg] gi ∗ n ↦[wms][ (sp - 16).toNat ] fb ∗
    n ↦[wms][ out.toNat ] ob ∗ n ↦[wms][ ft.toNat ] tb)

/-- The postcondition: no results, the stack pointer restored, the total
supply at `out` (and left in the frame), the `FungibleToken` unchanged. -/
def post (n g : Nat) (gi : GlobalInst) (sp out ft : UInt32) (tb : List UInt8)
    (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = []⌝ ∗ g ↦[wg] gi ∗ n ↦[wms][ (sp - 16).toNat ] tb ∗
    n ↦[wms][ out.toNat ] tb ∗ n ↦[wms][ ft.toNat ] tb)

/-- `FungibleToken::ft_total_supply` (function 414 of `contract.wasm`), at a
call depth `d` with room for its call to `U128::from` (566, the function at
`a566`): 46 `regular_op_cost`s. -/
theorem f414_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (n g a566 : Nat)
    (hn : mi.memAddrs[0]? = some n) (hg : mi.globalAddrs[0]? = some g)
    (ha : mi.funcAddrs[566]? = some a566) (ty566 : FuncType) (hty1 : ty566.params.length = 3)
    (hty2 : ty566.results = []) (hd : d + 1 < lim.maxCallDepth) (Cg : Nat)
    (gi : GlobalInst) (sp out ft : UInt32) (hgi : gi.value = .i32 sp) (hsp : 16 ≤ sp.toNat)
    (hft : ft.toNat + 16 ≤ 2 ^ 32) (fb ob tb : List UInt8) (hfb : fb.length = 16)
    (hob : ob.length = 16) (htb : tb.length = 16) :
    a566 ↪[wf] FuncInst.wasm ty566 inst f566 ∗ inst ↪[inst] mi
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f414 Cg (pre n g gi sp out ft fb ob tb)
        (fun _ => 46 * cfg.regularOpCost) (post n g gi sp out ft tb) := by
  iintro ⟨#Hf, #Hi⟩
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold pre at HP
  icases HP with ⟨%hargs, Hg, Hfr, Ho, Ht⟩
  subst hargs
  obtain ⟨gt, gv⟩ := gi
  simp only at hgi
  subst hgi
  have hsp16 : (sp - 16).toNat = sp.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le] <;> simp_all [UInt32.le_iff_toNat_le]
  icases memBytes_split n ft.toNat 8 tb (by omega) $$ Ht with ⟨Ht1, Ht2⟩
  ihave Ht2 := (memBytes_congr (toNat_add8 ft (by omega)).symm).1 $$ Ht2
  rw [entryLocals_f414]
  simp only [f414]
  mstep [Hg]; mstep; mstep; mstep
  simp only [Frame.withLocals, set2]
  mstep [Hg]
  mstep; mstep; mstep [Ht1]
  mstep; mstep; mstep; mstep [Ht2]
  simp only [List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero]
  -- call 566: the frame gets `from(lo, hi)`
  iapply mwpi_cons
  simp only [loadValue]
  iapply mwpi_call_spec_args (R := 16 * cfg.regularOpCost + R) 566 a566 ty566 inst mi f566
    [.i32 (sp - 16), .i64 (UInt64.ofNat (Memory.decodeLE (tb.take 8))),
      .i64 (UInt64.ofNat (Memory.decodeLE (tb.drop 8)))]
    (U128From.pre n (sp - 16) (UInt64.ofNat (Memory.decodeLE (tb.take 8)))
      (UInt64.ofNat (Memory.decodeLE (tb.drop 8))) fb)
    (fun _ => 6 * cfg.regularOpCost)
    (U128From.post n (sp - 16) (UInt64.ofNat (Memory.decodeLE (tb.take 8)))
      (UInt64.ofNat (Memory.decodeLE (tb.drop 8))))
    ha (by simp [hty1]) hd
  isplitl [Hc]
  · rw [activation_f566]
    iapply credits_le
    isplitl [Hc]
    · iexact Hc
    · ipureintro; omega
  isplitr; iexact Hf
  isplitr; iexact Hi
  isplitr
  · iapply U128From.f566_spec cfg lim (d + 1) ty566 hty2 inst mi n hn Cg _ _ _ fb hfb
  isplitl [Hfr]
  · iunfold U128From.pre
    isplitr
    · ipureintro; rfl
    · iexact Hfr
  inext
  iintro %rs Hc HQ
  iunfold U128From.post at HQ
  icases HQ with ⟨%hrs, Hfr⟩
  subst hrs
  rw [u128Bytes_load tb htb]
  simp only [Post.mseq_normal]
  have hlt := sp.toNat_lt
  have hf8 : (sp - 16).toNat + 8 < 2 ^ 32 := by omega
  icases memBytes_split n (sp - 16).toNat 8 tb (by omega) $$ Hfr with ⟨Hf1, Hf2⟩
  ihave Hf2 := (memBytes_congr (toNat_add8 (sp - 16) hf8).symm).1 $$ Hf2
  icases memBytes_split n out.toNat 8 ob (by omega) $$ Ho with ⟨Ho1, Ho2⟩
  -- local.get 2; i64.load; local.set 3
  mstep; mstep [Hf1]; mstep
  simp only [Frame.withLocals, set3]
  -- out+8 := frame+8
  mstep; mstep; mstep; mstep; mstep [Hf2]; mstep [Ho2]
  -- out := local 3
  mstep; mstep
  simp only [List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero]
  mstep [Ho1]
  -- sp += 16
  mstep; mstep; mstep; mstep [Hg]
  have e : sp - 16 + 16 = sp := by simp
  simp only [e]
  rw [storeBytes_load_i64 (tb.take 8) (by simp; omega),
    storeBytes_load_i64 (tb.drop 8) (by simp; omega)]
  ihave Hf2 := (memBytes_congr (j := (sp - 16).toNat + 8)
    (by rw [Nat.add_zero, toNat_add8 _ hf8])).1 $$ Hf2
  ihave Ht2 := (memBytes_congr (j := ft.toNat + 8)
    (by rw [Nat.add_zero, toNat_add8 _ (by omega)])).1 $$ Ht2
  ihave Hfr := memBytes_join n (sp - 16).toNat 8 (tb.take 8) (tb.drop 8) (by simp; omega) $$ [Hf1 Hf2]
  · isplitl [Hf1] <;> iassumption
  ihave Ho := memBytes_join n out.toNat 8 (tb.take 8) (tb.drop 8) (by simp; omega) $$ [Ho1 Ho2]
  · isplitl [Ho1] <;> iassumption
  ihave Ht := memBytes_join n ft.toNat 8 (tb.take 8) (tb.drop 8) (by simp; omega) $$ [Ht1 Ht2]
  · isplitl [Ht1] <;> iassumption
  rw [List.take_append_drop]
  unfold Post.mfunc
  simp only [htype, List.length_nil]
  isplitr
  · ipureintro; exact Nat.zero_le _
  iexists R
  iframe Hc
  iintro Hc
  iunfold post
  iframe Hc Hg Hfr Ho Ht
  ipureintro; rfl

end Spec

end WNear.Binary.FtTotalSupplyGetter
