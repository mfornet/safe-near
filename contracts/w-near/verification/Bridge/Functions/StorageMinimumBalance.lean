import Bridge.Functions.U128View
import Bridge.Functions.StorageBalanceBounds

/-!
# `storage_minimum_balance` (function 231), assembled

```wat
;; 231 storage_minimum_balance(): ft_total_supply's body (296) with
storage_minimum_balance(sp0 + 16, sp0 + 32)      ;; 230 for 414: storage_balance_bounds().min
expect(sp0 + 128, sp0 + 72, 1050476)             ;; 158, another panic location
```

`body231` and `body231None` are `U128View.bodyView` and `U128View.bodyViewNone` for the getter
230 (`StorageBalanceBounds.f230_spec`, `getterOk_230`). The getter writes the `u128`
`(S.accountStorageUsage mod 2^64) · 10^19` (`minS`): the `u64` the contract stores, times
near-sdk's byte price. Below `2^128` for every `u64` (`mul_price_lt`), so the overflow panic of
`storage_balance_bounds` is never reached, and the JSON returned is `minJson S`.
-/

namespace WNear.Binary.StorageMinimumBalance

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv WNear.Binary.FtTotalSupply WNear.Binary.U128View
open WNear.Binary.StorageBalanceBounds
open WNear.Binary.Interface (IfaceMod ifaceCode)
open WNear.Binary.VecFromElem (stk)
open WNear.Binary.StateReadModel (contractBytes)
open WNear.Binary.FmtU128 (val)
open WNear.Binary.U128From (u128Bytes)
open WNear.Binary.PanicStr (panicked notInit)

/-! ## The body and the value -/

theorem f231_body : f231.body = bodyA ++ ((bodyB0 ++ bodyB1 230) ++ bodyCG 1050476) := rfl

theorem entryLocals_f231 : entryLocals f231 [] = #[.i32 0] := rfl

/-- The minimum balance the binary computes from the model state `S`: its `u64` storage usage
times `10^19`. -/
def minS (S : WNear.State) : Nat := S.accountStorageUsage % 2 ^ 64 * 10000000000000000000

/-- The JSON `storage_minimum_balance` returns on `S`. -/
def minJson (S : WNear.State) : List UInt8 := jsonOf (minS S)

theorem minS_lt (S : WNear.State) : minS S < 2 ^ 128 := by
  have h := mul_price_lt (UInt64.ofNat S.accountStorageUsage)
  simp only [UInt64.toNat_ofNat'] at h
  exact h

/-- The getter reads the `u64` of the contract's bytes. -/
theorem minOf_contractBytes (S : WNear.State) (p : UInt32) (pad : List UInt8) :
    minOf (contractBytes S p ++ pad) = minS S := by
  have e : ((contractBytes S p ++ pad).drop 16).take 8 = WNear.Borsh.u64 S.accountStorageUsage := by
    rw [contractBytes_split]
    simp [List.drop_append, List.take_append, u128_length, u64_length]
  rw [minOf, e, xOf, WNear.Borsh.u64, decodeLE_leBytes, minS]
  simp only [UInt64.toNat_ofNat']
  norm_num

theorem viewJson_minS (S : WNear.State) : viewJson (u128Of (minS S)) = minJson S := by
  have h : val (loV (u128Of (minS S))) (hiV (u128Of (minS S))) = minS S := by
    have hd := decodeLE_u128Of (minS S)
    rw [Nat.mod_eq_of_lt (minS_lt S), u128Of, U128From.decodeLE_u128Bytes] at hd
    rw [loV, hiV, u128Of, u128Bytes, List.take_left' (by simp), List.drop_left' (by simp),
      load_storeBytes_i64, load_storeBytes_i64, val]
    exact hd
  rw [viewJson, h, minJson]

/-! ## The getter -/

section Getter

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The code the getter 230 calls (persistent): 418, 553, 954, 566. -/
def code230 (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) : IProp GF :=
  iprop(A 418 ↪[wf] FuncInst.wasm types[14]! inst f418 ∗ A 553 ↪[wf] FuncInst.wasm types[0]! inst f553 ∗
    A 954 ↪[wf] FuncInst.wasm types[8]! inst f954 ∗ A 566 ↪[wf] FuncInst.wasm types[4]! inst f566 ∗
    inst ↪[inst] mi)

instance (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) : Persistent (code230 (GF := GF) inst mi A) := by
  unfold code230; infer_instance

/-- The getter 230 meets `GetterOk`, writing `u128Of (minS S)`. -/
theorem getterOk_230 (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 3 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s : UInt32) (hs : 736 ≤ s.toNat) (S : WNear.State) :
    GetterOk (GF := GF) cfg lim d inst mi A n g 230 f230 (code230 inst mi A) 128 (cost230 cfg) Cg gt s S
      (u128Of (minS S)) where
  idx := by decide
  frame := by decide
  vb_length := by simp
  locals := rfl
  spec := by
    intro ob p pad hob hpad
    have hlt := s.toNat_lt
    have e0 : (s - 144).toNat = s.toNat - 144 := by rw [tsub _ _ (by simp; omega)]; simp
    have h := f230_spec (GF := GF) cfg lim (d + 1) types[14]! rfl inst mi n g (A 418) (A 553) (A 954) (A 566)
      hm.mem hm.glob (hm.funcs 418 (by decide)) (hm.funcs 553 (by decide)) (hm.funcs 954 (by decide))
      (hm.funcs 566 (by decide)) (by omega) Cg gt (s - 144) (s - 144 + 16) (s - 144 + 32) (by omega)
      (by simp [UInt32.toNat_add, e0]; omega) (by simp [UInt32.toNat_add, e0]; omega) ob
      (contractBytes S p ++ pad) hob (by rw [List.length_append, contractBytes_length, hpad])
    rw [minOf_contractBytes] at h
    refine Entails.trans ?_ h
    iintro #H
    iunfold code230 at H
    icases H with ⟨#H1, #H2, #H3, #H4, #H5⟩
    iframe H1 H2 H3 H4 H5

end Getter

/-! ## The body -/

section Main

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The code `storage_minimum_balance` runs (persistent). -/
def code231 (e inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n maxP : Nat) : IProp GF :=
  codeView e inst mi A n maxP 230 f230 (code230 inst mi A)

instance (e inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n maxP : Nat) :
    Persistent (code231 (GF := GF) e inst mi A n maxP) := by
  unfold code231; infer_instance

/-- The cost of `storage_minimum_balance` (231), activation excluded: `costView` with the
getter's `cost230`. -/
noncomputable def cost231 (cfg : WasmConfig) (h : NearState) (S : WNear.State) (x96 : Nat) : Nat :=
  costView cfg h S x96 (cost230 cfg) (u128Of (minS S))

theorem cost231_eq (cfg : WasmConfig) (h : NearState) (S : WNear.State) (x96 : Nat) :
    cost231 cfg h S x96 = 2658 * cfg.regularOpCost + cost219 cfg h S +
      (ToVec.cost96 cfg (loV (u128Of (minS S))) (hiV (u128Of (minS S))) + x96) +
      valueReturnUse h (minJson S).length := by
  simp only [cost231, costView, cost230, viewJson_minS]
  omega

/-- **The body of `storage_minimum_balance`** (231), from its entry frame: with the statics,
736 bytes of stack below the stack pointer `s` and the host `h` reading the model state `S`, it
falls through with the stack pointer restored and the host `h1.selectReturnValue (minJson S)`,
`h1` the host after `storage_read`. -/
theorem body231 (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (e inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 28 < lim.maxCallDepth) (x96 : Nat)
    (H96 : ToVecAfterFree cfg lim x96) (Cg R : Nat) (gt : GlobalType) (s : UInt32) (hs : 736 ≤ s.toNat)
    (hal : s.toNat % 8 = 0) (old k3 idx ptr0 : UInt32) (maxP len : Nat) (hroom : HeapRoom len maxP)
    (h : NearState) (S : WNear.State) (st : Near.TrieOverlay.State) (hr : ReadOkV h S st (minJson S))
    (Φ : Post NearState GF) :
    code231 e inst mi A n maxP ∗ credits Cg (cost231 cfg h S x96 + R) ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
      stk n (s.toNat - 736) 736 ∗ statics n ta A old k3 idx ptr0 maxP len ∗ mhostPt h ∗
      (∀ h1, ⌜StorageReadPost h StateRead.stateKey 0 st h1⌝ -∗ credits Cg R -∗ g ↦[wg] ⟨gt, .i32 s⟩ -∗
        mhostPt (h1.selectReturnValue (minJson S)) -∗ Φ.normal [] ⟨#[.i32 (s - 144)], inst, mi⟩)
      ⊢ mwpi cfg lim d ⟨#[.i32 0], inst, mi⟩ [] f231.body Φ := by
  rw [← viewJson_minS] at hr ⊢
  exact bodyView cfg lim d e inst mi A n g ta hm hd x96 H96 Cg R gt s hs hal old k3 idx ptr0 maxP len hroom
    h S st 230 f230 (code230 inst mi A) 128 (cost230 cfg) (u128Of (minS S))
    (getterOk_230 cfg lim d inst mi A n g ta hm (by omega) Cg gt s hs S) hr 1050476 f231.body f231_body Φ

/-- **The body of `storage_minimum_balance` on an uninitialized contract** (231): the panic of
`ft_total_supply`'s (`U128View.bodyViewNone`), at `cost296None`. -/
theorem body231None (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (e inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 18 < lim.maxCallDepth)
    (Cg R : Nat) (gt : GlobalType) (s : UInt32) (hs : 736 ≤ s.toNat) (hal : s.toNat % 8 = 0)
    (old k3 idx ptr0 : UInt32) (maxP len : Nat) (h : NearState) (st : Near.TrieOverlay.State)
    (hr : ReadNone h st) (Φ : Post NearState GF) :
    code231 e inst mi A n maxP ∗ codeP e inst mi A ∗ credits Cg (cost296None cfg h + R) ∗
      g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 736) 736 ∗ statics n ta A old k3 idx ptr0 maxP len ∗
      staticsP n ta A ∗ mhostPt h ∗
      (∀ h1, ⌜StorageReadPost h StateRead.stateKey 0 st h1⌝ -∗ panicked Cg h1 notInit -∗ Φ.trap)
      ⊢ mwpi cfg lim d ⟨#[.i32 0], inst, mi⟩ [] f231.body Φ := by
  iintro ⟨#Hk, #HP, Hc, Hg, Stk, HS, HSP, Hh, W⟩
  iunfold code231, codeView at Hk
  icases Hk with ⟨#KA, #KB, #KC, -, -⟩
  ihave #HIC : ifaceCode e inst mi A n (some maxP) $$ []
  · iunfold codeC at KC
    icases KC with ⟨#HIC, -⟩
    iexact HIC
  iapply bodyViewNone cfg lim d e inst mi A n g ta hm hd Cg R gt s hs hal old k3 idx ptr0 maxP len h st hr
    (bodyB1 230 ++ bodyCG 1050476) f231.body (by rw [f231_body]; simp) Φ
  iframe KA KB HIC HP Hc Hg Stk HS HSP Hh W

end Main

end WNear.Binary.StorageMinimumBalance
