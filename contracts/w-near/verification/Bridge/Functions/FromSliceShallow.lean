import Bridge.Functions.FromSliceNoEsc
import Bridge.Functions.SerdeIgnValue

/-!
# `ft_balance_of`'s parser on the shallow input without escapes: no hypothesis left (M6)

`FromSliceNoEsc.acceptContract_noesc81` left `Hyp81`, the specification of `ignore_value` (81).
`SerdeIgnValue.f81_shallow` proves 81 on the values that push no frame onto the scratch: a scalar, or
one bracket of scalars (`IgnoreShallow.ign1`). Deeper values grow the scratch from capacity 0, which
changes the heap across 228's loop; they are not covered, so the contract is stated for the inputs
where serde's struct machine with the shallow skip accepts (`structDe … ign1R bs`), which are exactly
inputs the model accepts (`IgnoreShallow.decode_of_shallow`):

* `code81_of`: 81's code from the store's function cells;
* `K81s`, `hyp81_shallow`: `Hyp81` for the reader `ign1R`, at `(166 + 470 · bytes) · c`; `lin81_shallow`:
  `Lin81` with `a81 = 166`, `b81 = 470`;
* `cost66_struct`: `SerdeCost.cost66_le` restated from the struct machine's acceptance (`structDe`)
  instead of `Call.decode`, for readers that return suffixes;
* `acceptContract_shallow`: **on an input without `\` that the shallow machine accepts, 66 returns
  `Ok(a)` within `(1725 + 470 · len) · c + x169 cfg F`**, and `Call.decode` reads `ftBalanceOf a`. The
  only parameter left is the escapes' (`Hyp646` beyond escape-free keys), absent here by `0x5C ∉ bs`.

The per-byte constant is `K1 = 470`: the member condition `1714 + a81 + b81 ≤ 5 · K1` is met with
equality (`1714 + 166 + 470 = 2350`).
-/

namespace WNear.Binary.FromSliceSpec

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_addr)
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.AllocInv (heapInv block)
open WNear.Binary.ArgsLeaves (sliceRead)
open WNear.Binary.SerdeErrBox (roomFor4)
open WNear.Binary.SerdeStructArr (strRes tbl)
open WNear.Binary.SerdeFromTrait (code66)
open WNear.Binary.SerdeRead (rd wsLen)
open WNear.IgnoreShallow (ign1 ign1R)
open NearInterface.Json (skipWhitespace)

/-- 81's cost at `j`, by the shallow skip. -/
def K81s (c : Nat) (bs : List UInt8) (j : Nat) : Nat :=
  match ign1 (bs.drop j) with
  | some r => (166 + 470 * (bs.length - r.length - j)) * c
  | none => 0

theorem lin81_shallow (c : Nat) (bs : List UInt8) : SerdeCost.Lin81 c (K81s c bs) ign1R bs 166 470 := by
  intro j r hj h
  unfold ign1R at h
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨r', h1, h2⟩ := h
  cases h2
  unfold K81s
  rw [h1]

section Proof

variable {GF : BundledGFunctors} [WasmGS NearState GF]

open WNear.Binary.InitialState in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- The code 81 runs on a shallow value, from the store's function cells. -/
theorem code81_of (cfg : RuntimeConfig) (h : NearState) :
    codeCtx (GF := GF) cfg h ⊢ SerdeIgnValue.code81 0 wInst id := by
  iintro #Hctx
  iunfold codeCtx at Hctx
  icases Hctx with ⟨#HF, #Hi, #Hm⟩
  simp only [SerdeIgnValue.code81, SerdeIgnNum.numCode, VecAppend.appCode, id]
  repeat' (first
    | iexact Hi
    | iexact Hm
    | (iapply wasmLeaf cfg h _ _ _ ?_ ?_ ?_ ?_ <;> first | iexact HF | decide | kernel_rfl | rfl)
    | isplitl [])

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **`Hyp81` for the shallow skip**, on an input without `\`. -/
theorem hyp81_shallow (cfg : RuntimeConfig) (h0 : NearState) (lim : ExecLimits) (Cg : Nat) (gt : GlobalType)
    (de ptr idx : UInt32) (bs : List UInt8) (hlen : bs.length + 1 < 2 ^ 28) (hptr : ptr.toNat + bs.length < 2 ^ 32)
    (hde : de.toNat + 24 ≤ 2 ^ 32) (hnb : (0x5C : UInt8) ∉ bs) :
    SerdeStructObj.Hyp81 cfg.wasm lim 0 wInst 0 0 0 id Cg gt de ptr idx bs 2048 ign1R
      (K81s cfg.wasm.regularOpCost bs) (codeCtx (GF := GF) cfg h0) := by
  intro d sp j r mlen F live hd hsp hj hr hign
  unfold ign1R at hign
  simp only [Option.map_eq_some_iff] at hign
  obtain ⟨r', hx, h2⟩ := hign
  cases h2
  have s := SerdeIgnValue.f81_shallow (GF := GF) cfg.wasm lim d types[32]! (by rfl) 0 wInst id 0 0 0
    Interface.wInst_ifaceMod (by omega) Cg gt sp de ptr bs j r (by omega) (by omega) hde (by omega) hj hnb hx
  have hK : K81s cfg.wasm.regularOpCost bs j = (166 + 470 * (bs.length - r.length - j)) * cfg.wasm.regularOpCost := by
    unfold K81s; rw [hx]
  rw [hK]
  iintro #Hctx
  ihave #C81 := code81_of cfg h0 $$ Hctx
  ihave #S := s $$ C81
  clear s
  iapply (AllocFresh.MFunSpec_frame (Fr := iprop(vt 0 1057464 idx 0 (id 578) ∗ heapInv 0 2048 mlen live F ∗
      stk 0 (sp.toNat - 256) 160))
    (P := fun args => iprop(⌜args = [.i32 de]⌝ ∗ 0 ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk 0 (sp.toNat - 96) 96 ∗
      rd 0 de ptr bs j ∗ tbl 0 de))
    (Q := fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ 0 ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk 0 (sp.toNat - 96) 96 ∗
      rd 0 de ptr bs (bs.length - r.length) ∗ tbl 0 de)) ?hP ?hQ)
  case hP =>
    intro args
    iintro ⟨%ha, Hg, Hs, Hvt, Hh, Hrd, H256, Ht⟩
    iframe Hg Hs Hvt Hh Hrd H256 Ht
    ipureintro; exact ha
  case hQ =>
    intro args rs
    iintro ⟨⟨Hvt, Hh, H256⟩, %hrs, Hg, Hs, Hrd, Ht⟩
    isplitr
    · ipureintro; exact ⟨0, hrs⟩
    iframe Hg Hs Hvt Hh Hrd H256 Ht
    ipureintro; exact hrs
  iexact S

end Proof

/-! ## 66's cost, from the struct machine's acceptance -/

open NearInterface.Json WNear.JsonFuel WNear.SerdeStructModel WNear.SerdeStructLoop WNear.JsonSuffix in
open WNear.Binary.SerdeStructObj (objCost costObj) in
set_option maxHeartbeats 4000000 in
/-- **`SerdeCost.cost66_le` from `structDe`**: where serde's struct machine reads `a` and the rest `r`,
for readers that return suffixes (and strictly shorter ones), 66's cost is within
`(1725 + a169 + K1 · len) · c + x`. -/
theorem cost66_struct (cfg : WasmConfig) (K646 K169 K81 : Nat → Nat)
    (dv : List UInt8 → Option (WNear.AccountId × List UInt8)) (ign : List UInt8 → Option (Unit × List UInt8))
    (bs : List UInt8) (a : WNear.AccountId) (r : List UInt8) (hS : structDe "account_id" dv ign bs = some (a, r))
    (hdv0 : dv [] = none)
    (hdvs : ∀ j a r, j ≤ bs.length → dv (bs.drop j) = some (a, r) → bs.drop (bs.length - r.length) = r)
    (hdvS : ∀ bs a r, dv bs = some (a, r) → r <:+ bs) (hignS : ∀ bs r, ign bs = some ((), r) → r <:+ bs)
    (hdvL : ∀ bs a r, dv bs = some (a, r) → r.length < bs.length)
    (hignL : ∀ bs r, ign bs = some ((), r) → r.length < bs.length)
    (K1 a646 b646 a169 b169 x a81 b81 : Nat)
    (h646 : SerdeCost.Lin646 cfg.regularOpCost K646 bs a646 b646)
    (h169 : SerdeCost.Lin169 cfg.regularOpCost K169 dv bs a169 b169 x)
    (h81 : SerdeCost.Lin81 cfg.regularOpCost K81 ign bs a81 b81)
    (hK : 96 ≤ K1) (hb646 : b646 ≤ K1) (hb169 : b169 ≤ K1) (hb81 : b81 ≤ K1)
    (hM169 : 942 + SerdeKey.cost194 + a646 + b646 + a169 + b169 ≤ 5 * K1)
    (hM81 : 942 + SerdeKey.cost194 + a646 + b646 + a81 + b81 ≤ 5 * K1) :
    (425 + 96 * r.length) * cfg.regularOpCost + SerdeStruct78.costS cfg K646 K169 K81 dv ign bs ≤
      (1725 + a169 + K1 * bs.length) * cfg.regularOpCost + x := by
  have hsuf := JsonSuffix.structDe_suf "account_id" dv ign hdvS hignS hS
  have hrl : r.length ≤ bs.length := hsuf.length_le
  unfold SerdeStruct78.costS
  generalize hc : cfg.regularOpCost = c
  have e96 := Nat.mul_le_mul_right r.length hK
  rcases SerdeStruct78.structDe_cases hS hdv0 hdvs with ⟨ho, hl⟩ | ⟨r1, hok, hrr⟩
  · rw [if_pos ho]
    unfold costObj
    simp only [List.drop_zero, Nat.zero_add]
    rw [hc]
    have hw0 := SerdeNextKey.getElem_lt ho
    have hlb := SerdeCost.objCost_le c K646 K169 K81 dv ign bs K1 a646 b646 a169 b169 x a81 b81 (hc ▸ h646)
      (hc ▸ h169) (hc ▸ h81) hdvS hignS hdvL hignL hK hb646 hb169 hb81 hM169 hM81 _ true (wsLen bs + 1) none a r
      (by omega) (by simpa [loopRes] using hl)
    simp only [ite_true, Option.isNone_none] at hlb
    have hrF : r.length ≤ bs.length - (wsLen bs + 1) := by
      have := (SerdeCost.loopRes_suf "account_id" dv ign hdvS hignS (first := true) (seen := none)
        (by simpa [loopRes] using hl)).length_le
      simp at this; omega
    have e0 := Nat.mul_le_mul_right (wsLen bs) hK
    have hcoef : 400 + 96 * wsLen bs + (K1 + 300 + K1 * (bs.length - r.length - (wsLen bs + 1))) + 300 +
        (425 + 96 * r.length) ≤ 1725 + a169 + K1 * bs.length := by
      have hsplit : bs.length = (bs.length - r.length - (wsLen bs + 1)) + wsLen bs + 1 + r.length := by omega
      have : K1 * bs.length = K1 * (bs.length - r.length - (wsLen bs + 1)) + K1 * wsLen bs + K1 + K1 * r.length := by
        conv_lhs => rw [hsplit]
        ring
      omega
    have := Nat.mul_le_mul_right c hcoef
    calc (425 + 96 * r.length) * c + ((400 + 96 * wsLen bs) * c +
          objCost c K646 K169 K81 dv ign bs (bs.length - (wsLen bs + 1) + 1) true (wsLen bs + 1) + 300 * c)
        ≤ (425 + 96 * r.length) * c + ((400 + 96 * wsLen bs) * c +
          ((K1 + 300 + K1 * (bs.length - r.length - (wsLen bs + 1))) * c + x) + 300 * c) := by omega
      _ = (400 + 96 * wsLen bs + (K1 + 300 + K1 * (bs.length - r.length - (wsLen bs + 1))) + 300 +
            (425 + 96 * r.length)) * c + x := by ring
      _ ≤ (1725 + a169 + K1 * bs.length) * c + x := by omega
  · obtain ⟨hb0, -, hd, hb4⟩ := hok
    simp only [List.drop_zero, Nat.zero_add] at hb0 hd
    rw [if_neg (by rw [hb0]; decide), hd]
    unfold SerdeStructArr.costArr
    simp only [List.drop_zero, Nat.zero_add]
    rw [hc]
    have hw4 := SerdeNextKey.getElem_lt hb4
    have hr1 : r1 <:+ bs.drop (wsLen bs + 1 + wsLen (bs.drop (wsLen bs + 1))) := hdvS _ _ _ hd
    have hr1l : r1.length ≤ bs.length - (wsLen bs + 1 + wsLen (bs.drop (wsLen bs + 1))) := by
      have := hr1.length_le; simp at this; omega
    have hK169 := (hc ▸ h169) _ a r1 (by omega) hd
    have hrlen : r.length = bs.length - (bs.length - r1.length + wsLen (bs.drop (bs.length - r1.length)) + 1) := by
      rw [hrr]; simp
    generalize wsLen bs = w0 at hr1l hK169 hrlen ⊢
    generalize wsLen (bs.drop (w0 + 1)) = w2 at hr1l hK169 hrlen ⊢
    generalize wsLen (bs.drop (bs.length - r1.length)) = w4 at hw4 hrlen ⊢
    have e0 := Nat.mul_le_mul_right w0 hK
    have e2 := Nat.mul_le_mul_right w2 hK
    have e4 := Nat.mul_le_mul_right w4 hK
    have eb := Nat.mul_le_mul_right (bs.length - r1.length - (w0 + 1 + w2)) hb169
    have hcoef : 1300 + 96 * (w0 + w2 + w4) + (a169 + b169 * (bs.length - r1.length - (w0 + 1 + w2))) +
        (425 + 96 * r.length) ≤ 1725 + a169 + K1 * bs.length := by
      have hsplit : bs.length = w0 + 1 + w2 + (bs.length - r1.length - (w0 + 1 + w2)) + w4 + 1 + r.length := by omega
      have : K1 * bs.length = K1 * w0 + K1 + K1 * w2 + K1 * (bs.length - r1.length - (w0 + 1 + w2)) + K1 * w4 + K1 +
          K1 * r.length := by
        conv_lhs => rw [hsplit]
        ring
      rw [Nat.mul_add 96, Nat.mul_add 96]
      omega
    have := Nat.mul_le_mul_right c hcoef
    calc (425 + 96 * r.length) * c + ((1300 + 96 * (w0 + w2 + w4)) * c + K169 (w0 + 1 + w2))
        ≤ (425 + 96 * r.length) * c + ((1300 + 96 * (w0 + w2 + w4)) * c +
          ((a169 + b169 * (bs.length - r1.length - (w0 + 1 + w2))) * c + x)) := by omega
      _ = (1300 + 96 * (w0 + w2 + w4) + (a169 + b169 * (bs.length - r1.length - (w0 + 1 + w2))) +
            (425 + 96 * r.length)) * c + x := by ring
      _ ≤ (1725 + a169 + K1 * bs.length) * c + x := by omega

/-! ## The accepting contract -/

section Contract

variable {GF : BundledGFunctors} [WasmGS NearState GF]

theorem member_169 : 942 + SerdeKey.cost194 + 300 + 130 + 0 + 208 ≤ 5 * 470 := by
  decide

theorem member_81 : 942 + SerdeKey.cost194 + 300 + 130 + 166 + 470 ≤ 5 * 470 := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **The accepting contract of `from_trait` (66) on the shallow input without escapes**, with no
hypothesis on the callees: where serde's struct machine with the shallow skip reads `a` and then only
whitespace, on an input without `\`, `Call.decode` reads `ftBalanceOf a` and 66 returns `Ok(a)` at `out`
within `(1725 + 470 · len) · c + x169 cfg F`. -/
theorem acceptContract_shallow (cfg : RuntimeConfig) (h0 : NearState) (lim : ExecLimits) (d : Nat)
    (hd : d + 64 < lim.maxCallDepth) (Cg : Nat) (gt : GlobalType) (sp out rd ptr idx : UInt32)
    (bs ob : List UInt8) (hl F : Nat) (live : List (Nat × Nat)) (a : WNear.AccountId) (r : List UInt8)
    (hS : 400 ≤ sp.toNat) (hal : sp.toNat % 16 = 0) (hptr : ptr.toNat + bs.length < 2 ^ 32)
    (hlen : bs.length + 1 < 2 ^ 28) (hout : out.toNat + 16 ≤ 2 ^ 32) (hob : ob.length = 16)
    (hrd : rd.toNat + 12 ≤ 2 ^ 32) (hr : SerdeStructArr.roomS hl 2048) (hnb : (0x5C : UInt8) ∉ bs)
    (hacc : SerdeStructModel.structDe "account_id" (SerdeStructModel.valueAs WNear.account) ign1R bs = some (a, r))
    (hE : skipWhitespace r = []) :
    WNear.Call.decode "ft_balance_of" bs = some (.ftBalanceOf a) ∧
    (⊢ (codeCtx (GF := GF) cfg h0 -∗
      MFunSpec (GF := GF) cfg.wasm lim d types[14]! 0 wInst f66 Cg
        (pre66 400 gt sp out rd ptr idx bs ob hl F live)
        (fun _ => (1725 + 470 * bs.length) * cfg.wasm.regularOpCost + SerdeAcctHyp.x169 cfg.wasm F)
        (post66 400 gt sp rd ptr idx bs (okAt 0 out a live)))) := by
  refine ⟨IgnoreShallow.decode_of_shallow hacc hE, ?_⟩
  have hdvA : SerdeStructModel.Agrees (SerdeStructModel.valueAs WNear.account)
      (SerdeStructModel.valueAs WNear.account) := fun _ => Or.inl rfl
  obtain ⟨hdv0, hdvs, -, hstrs, hdvS, -⟩ := SerdeFromTrait.reader_facts hdvA IgnoreModel.vSkip_agrees bs
  have hignS : ∀ bs r, ign1R bs = some ((), r) → r <:+ bs := fun _ _ h => IgnoreShallow.ign1R_suf h
  have higns : ∀ j r, j ≤ bs.length → ign1R (bs.drop j) = some ((), r) → bs.drop (bs.length - r.length) = r :=
    fun _ _ _ h => JsonSuffix.drop_suf' (hignS _ _ h)
  have hdvL : ∀ bs a r, SerdeStructModel.valueAs WNear.account bs = some (a, r) → r.length < bs.length :=
    fun _ _ _ h => JsonSuffix.valueAs_strict _ h
  have hignL : ∀ bs r, ign1R bs = some ((), r) → r.length < bs.length := fun _ _ h => IgnoreShallow.ign1R_strict h
  have hsuf := JsonSuffix.drop_suf (JsonSuffix.structDe_suf "account_id" _ _ hdvS hignS hacc)
  have hlt := sp.toNat_lt
  have h64 : (sp - 64).toNat = sp.toNat - 64 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have h646 := SerdeKeyNoEsc.hyp646_noesc (GF := GF) cfg.wasm lim 0 wInst id 0 0 0 Interface.wInst_ifaceMod Cg gt
    (sp - 64) ptr idx bs 2048 hlen hptr (by omega) hnb (codeCtx cfg h0) (code646_of cfg h0)
  have h169 := SerdeAcctHyp.hyp169_noesc (GF := GF) cfg.wasm lim 0 wInst id 0 0 0 Interface.wInst_ifaceMod Cg gt
    (sp - 64) ptr idx bs 2048 hlen hptr (by omega) hnb F (codeCtx cfg h0) (code169_of cfg h0)
  have h81 := hyp81_shallow (GF := GF) cfg h0 lim Cg gt (sp - 64) ptr idx bs hlen hptr (by omega) hnb
  have hK := cost66_struct cfg.wasm (SerdeKeyNoEsc.K646 cfg.wasm bs) (SerdeAcctHyp.K169 cfg.wasm bs F)
    (K81s cfg.wasm.regularOpCost bs) (SerdeStructModel.valueAs WNear.account) ign1R bs a r hacc hdv0 hdvs hdvS hignS
    hdvL hignL 470 300 130 0 208 (SerdeAcctHyp.x169 cfg.wasm F) 166 470 (SerdeKeyNoEsc.lin646_noesc cfg.wasm bs hnb)
    (SerdeAcctHyp.lin169_noesc cfg.wasm bs hnb F) (lin81_shallow _ bs) (by omega) (by omega) (by omega) (by omega)
    member_169 member_81
  simp only [Nat.add_zero] at hK
  have s := SerdeFromTrait.f66_acc (GF := GF) cfg.wasm lim d types[14]! (by rfl) 0 wInst id 0 0 0
    Interface.wInst_ifaceMod (by omega) Cg gt sp out rd ptr idx ob bs 2048 hl F live hob hout hrd hlen hptr hS
    (by omega) hr (SerdeStructModel.valueAs WNear.account) ign1R (SerdeKeyNoEsc.K646 cfg.wasm bs)
    (SerdeAcctHyp.K169 cfg.wasm bs F) (K81s cfg.wasm.regularOpCost bs) F (codeCtx cfg h0) h646 h169 h81
    (Nat.le_refl F) hdv0 hdvs higns hstrs a r hacc hE hsuf
  simp only [id] at s
  iintro #Hctx
  ihave #C66 := code66_of cfg h0 $$ Hctx
  ihave #S := s $$ [C66 Hctx]
  · iframe C66 Hctx
  clear s
  iapply (AllocGen.MFunSpec_cost (K := fun _ => (425 + 96 * r.length) * cfg.wasm.regularOpCost +
    SerdeStruct78.costS cfg.wasm (SerdeKeyNoEsc.K646 cfg.wasm bs) (SerdeAcctHyp.K169 cfg.wasm bs F)
      (K81s cfg.wasm.regularOpCost bs) (SerdeStructModel.valueAs WNear.account) ign1R bs) (fun _ => hK))
  iapply (AllocFresh.MFunSpec_frame (Fr := iprop(emp))
    (P := fun args => iprop(⌜args = [.i32 out, .i32 rd]⌝ ∗ 0 ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk 0 (sp.toNat - 400) 400 ∗
      vt 0 1057464 idx 0 578 ∗ heapInv 0 2048 hl live F ∗ 0 ↦[wms][ out.toNat ] ob ∗
      sliceRead 0 rd ptr (UInt32.ofNat bs.length) 0 ∗ 0 ↦[wms][ ptr.toNat ] bs ∗
      0 ↦[wms][ 1062392 ] ParseStr.escTable ∗ 0 ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width ∗
      0 ↦[wms][ 1051092 ] WNear.BalanceOfArgs.keyBytes ∗ 0 ↦[wms][ 1048576 ] SerdeIdent.identBytes))
    (Q := fun _ rs => iprop(⌜rs = []⌝ ∗ 0 ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk 0 (sp.toNat - 400) 400 ∗
      vt 0 1057464 idx 0 578 ∗ sliceRead 0 rd ptr (UInt32.ofNat bs.length) 0 ∗ 0 ↦[wms][ ptr.toNat ] bs ∗
      0 ↦[wms][ 1062392 ] ParseStr.escTable ∗ 0 ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width ∗
      0 ↦[wms][ 1051092 ] WNear.BalanceOfArgs.keyBytes ∗ 0 ↦[wms][ 1048576 ] SerdeIdent.identBytes ∗
      ∃ (p cap : UInt32), 0 ↦[i32][ out.toNat ] 0 ∗ 0 ↦[i32][ out.toNat + 4 ] p ∗
        0 ↦[i32][ out.toNat + 8 ] cap ∗ 0 ↦[i32][ out.toNat + 12 ] (UInt32.ofNat a.val.utf8ByteSize) ∗
        strRes 0 2048 live a p cap)) ?hP ?hQ)
  case hP =>
    intro args
    iintro HP
    iunfold pre66 at HP
    icases HP with ⟨%ha, Hg, Hsr, Hs, Ho, Hbs, Hro, Hvt, Hh⟩
    iunfold roData at Hro
    icases Hro with ⟨He, Hw, Hk, Hid⟩
    iframe Hg Hsr Hs Ho Hbs He Hw Hk Hid Hvt Hh
    ipureintro; exact ha
  case hQ =>
    intro args rs
    iintro ⟨-, %hrs, Hg, Hs, Hvt, Hsr, Hbs, He, Hw, Hk, Hid, %p, %cap, W0, W4, W8, W12, Hstr⟩
    iunfold post66
    iframe Hg Hs Hbs Hvt
    isplitr
    · ipureintro; exact hrs
    isplitl [Hsr]
    · iexists ptr
      iexists UInt32.ofNat bs.length
      iexists 0
      iexact Hsr
    isplitl [He Hw Hk Hid]
    · iunfold roData
      iframe He Hw Hk Hid
    iunfold strRes at Hstr
    icases Hstr with ⟨%mlen', %F', %⟨hp, hcap, -⟩, Hbytes, Hblk, Hh⟩
    iunfold okAt
    iexists p
    iexists cap
    iexists mlen'
    iexists F'
    iframe W0 W4 W8 W12 Hbytes Hblk Hh
    ipureintro; exact ⟨hp, hcap⟩
  iexact S

end Contract

end WNear.Binary.FromSliceSpec
