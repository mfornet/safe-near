import Bridge.Functions.FmtWrite

/-!
# `to_string()` of a `u128` into an empty `String`: the sink and the composition (M5)

The `String` sink's `write_str` (759) as the two indirect callees of `core::fmt::write` (872,
`FmtWrite.f872_one`) needs it:

* `sink_grow`: the digits' `write_str` from `fmt_u128`'s `pad_integral`, on the empty `String`
  (`FmtSink.f759_grow`), as `FmtU128.sinkSpec`;
* `piece_room`: the empty piece's `write_str` (`FmtSink.f759_room` with `k = 0`).
-/

namespace WNear.Binary.FmtString

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.FmtPad (fmtr)
open WNear.Binary.FmtU128 (sinkSpec)
open WNear.Binary.FmtSink (sinkCode roomPre roomPost growPre growPost strGrown f759_room f759_grow)
open WNear.Binary.FmtGrow (newCap)
open WNear.Binary.VecWithCap (okF)
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_word stk_intro stk_addr roomFor costAlloc)
open WNear.Binary.AllocNewCell (memBytes_addr)

section Sink

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- What the digits' `write_str` owns besides the digits: `*dd = vec`, its 112 bytes of stack,
the allocator's vtable slot, the heap, the empty `String` `(1, 0, 0)` at `vec`. -/
def skPre (n maxP hl : Nat) (live : List (Nat × Nat)) (F : Nat) (ta a578 : Nat) (s dd vec idx : UInt32) : IProp GF :=
  iprop(n ↦[i32][ dd.toNat ] vec ∗ stk n (s.toNat - 112) 112 ∗ vt n 1057464 idx ta a578 ∗
    heapInv n maxP hl live F ∗ n ↦[i32][ vec.toNat ] 1 ∗ n ↦[i32][ vec.toNat + 4 ] 0 ∗
    n ↦[i32][ vec.toNat + 8 ] 0)

/-- After: the `String` grown to hold the `k` digits `ds`. -/
def skPost (n maxP hl : Nat) (live : List (Nat × Nat)) (F : Nat) (ta a578 : Nat) (s dd vec idx k : UInt32)
    (ds : List UInt8) : IProp GF :=
  iprop(n ↦[i32][ dd.toNat ] vec ∗ stk n (s.toNat - 112) 112 ∗ vt n 1057464 idx ta a578 ∗
    strGrown n maxP hl live F vec k ds)

/-- The sink's cost on `k` bytes. -/
def costGrow (cfg : WasmConfig) (k : UInt32) : Nat :=
  453 * cfg.regularOpCost + costAlloc cfg false (newCap 0 k) + MemCpy.cost k.toNat * cfg.regularOpCost

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- The digits' `write_str` (759 on the empty `String`) as `fmt_u128`'s sink. -/
theorem sink_grow (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 16 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s c dd vec idx : UInt32) (maxP hl : Nat) (live : List (Nat × Nat))
    (ds : List UInt8) (hs : 112 ≤ s.toNat) (hs2 : s.toNat + 144 ≤ 2 ^ 32) (hc : c.toNat < 39)
    (hds : ds.length = 39 - c.toNat) (hdd : dd.toNat + 4 ≤ 2 ^ 32) (hvec : vec.toNat + 12 ≤ 2 ^ 32)
    (hr : roomFor hl maxP (newCap 0 (39 - c))) (F : Nat := 1) (hF : okF F := by exact Or.inl rfl) :
    sinkCode n maxP inst mi A
      ⊢ sinkSpec (GF := GF) cfg lim d inst mi n g gt s c dd f759 ds
          (skPre n maxP hl live F ta (A 578) s dd vec idx)
          (skPost n maxP hl live F ta (A 578) s dd vec idx (39 - c) ds) (costGrow cfg (39 - c)) Cg := by
  iintro #Hk
  iunfold sinkSpec
  imodintro
  iintro %p %k %⟨hp, hk⟩
  have hc39 : (39 - c).toNat = 39 - c.toNat := by
    rw [UInt32.toNat_sub_of_le]; · rfl
    simp [UInt32.le_iff_toNat_le]; omega
  have ek : k = 39 - c := UInt32.toNat_inj.mp (by rw [hk, hc39])
  subst ek
  iapply AllocFresh.MFunSpec_frame (Fr := iprop(True))
    (P := fun args => iprop(⌜args = [.i32 dd, .i32 p, .i32 (39 - c)]⌝ ∗ n ↦[i32][ dd.toNat ] vec ∗
      growPre n g gt s vec 1 p idx ta (A 578) maxP hl live F ds))
    (Q := fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ n ↦[i32][ dd.toNat ] vec ∗
      growPost n g gt s vec p (39 - c) idx ta (A 578) maxP hl live F ds))
  · intro args
    iintro ⟨%ha, Hg, Hds, Hsk⟩
    iunfold skPre at Hsk
    icases Hsk with ⟨Hdd, Hs, Hvt, Hh, V0, V4, V8⟩
    iframe Hdd
    isplitr; · ipureintro; exact ha
    iunfold growPre
    iframe Hg Hs Hvt Hh V0 V4 V8 Hds
  · intro args rs
    iintro ⟨-, %hrs, Hdd, HQ⟩
    iunfold growPost at HQ
    icases HQ with ⟨Hg, Hs, Hvt, Hsg, Hds⟩
    iframe Hg Hds
    isplitr; · ipureintro; exact hrs
    iunfold skPost
    iframe Hdd Hs Hvt Hsg
  iunfold costGrow
  iapply f759_grow cfg lim d types[15]! (by rfl) inst mi A n g ta hm hd Cg gt s dd vec 1 p (39 - c) idx maxP hl
    live ds hs (by rw [hds, hc39]) hdd hvec (by omega) (by omega) (by omega) hr (F := F) (hF := hF)
  iexact Hk

end Sink

section Compose

variable {GF : BundledGFunctors} [WasmGS NearState GF]

open WNear.Binary.FmtDigits (decDigits lut)
open WNear.Binary.FmtU128 (val)
open WNear.Binary.U128From (u128Bytes)
open WNear.Binary.FmtDisplay (fmtCode f353_spec)
open WNear.Binary.FmtWrite (argsAt pieceArg f872_one)

theorem memBytes_nil (n a : Nat) : ⊢ WasmLogic.memBytes (H := NearState) (GF := GF) n a [] := by
  simp only [WasmLogic.memBytes, WasmLogic.byteCells]
  iapply BigSepL.bigSepL_nil.2; iempintro

/-- The number of digits as a `UInt32`, as `fmt_u128`'s sink sees it (`39 - (39 - len)`). -/
def kOf (N : Nat) : UInt32 := 39 - UInt32.ofNat (39 - (decDigits N).length)

/-- What `fmt::write` needs below its frame `sp` (owned through the call): `*dd = vec`, 256 bytes
of stack, the allocator, the heap, the empty `String` at `vec`, the `&u128` cell `vp ↦ p`, the
`u128` at `p`, the digit table. -/
def wIn (n maxP hl : Nat) (live : List (Nat × Nat)) (F : Nat) (ta a578 : Nat) (sp dd vec aidx vp p : UInt32)
    (lo hi : UInt64) : IProp GF :=
  iprop(n ↦[i32][ dd.toNat ] vec ∗ stk n (sp.toNat - 256) 256 ∗ vt n 1057464 aidx ta a578 ∗
    heapInv n maxP hl live F ∗ n ↦[i32][ vec.toNat ] 1 ∗ n ↦[i32][ vec.toNat + 4 ] 0 ∗
    n ↦[i32][ vec.toNat + 8 ] 0 ∗ n ↦[i32][ vp.toNat ] p ∗ n ↦[wms][ p.toNat ] u128Bytes lo hi ∗
    n ↦[wms][ 1070974 ] lut)

/-- After: the `String` at `vec` holds the decimal digits. -/
def wOut (n maxP hl : Nat) (live : List (Nat × Nat)) (F : Nat) (ta a578 : Nat) (sp dd vec aidx vp p : UInt32)
    (lo hi : UInt64) : IProp GF :=
  iprop(n ↦[i32][ dd.toNat ] vec ∗ stk n (sp.toNat - 256) 256 ∗ vt n 1057464 aidx ta a578 ∗
    strGrown n maxP hl live F vec (kOf (val lo hi)) (decDigits (val lo hi)) ∗ n ↦[i32][ vp.toNat ] p ∗
    n ↦[wms][ p.toNat ] u128Bytes lo hi ∗ n ↦[wms][ 1070974 ] lut)

theorem decDigits_le (lo hi : UInt64) : (decDigits (val lo hi)).length ≤ 39 :=
  FmtDigits.decDigits_length_le 39 (val lo hi) (by decide) (by
    unfold val; have := lo.toNat_lt; have := hi.toNat_lt; omega)

theorem kOf_toNat (lo hi : UInt64) : (kOf (val lo hi)).toNat = (decDigits (val lo hi)).length := by
  have h1 := decDigits_le lo hi
  have h2 := FmtDigits.decDigits_length_pos (val lo hi)
  unfold kOf
  rw [UInt32.toNat_sub_of_le]
  · simp; omega
  · simp [UInt32.le_iff_toNat_le]; omega

theorem stk_256_16 (n a : Nat) :
    stk (GF := GF) n a 256 ⊣⊢ stk n a 240 ∗ stk n (a + 240) 16 :=
  ⟨stk_split n a 240 16, stk_join n a 240 16⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- The empty piece's `write_str` (759 with `k = 0`) on `wIn`: nothing written. -/
theorem piece_room (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 5 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp dd vec aidx vp p ptr0 : UInt32) (maxP hl : Nat) (live : List (Nat × Nat))
    (lo hi : UInt64) (hsp : 256 ≤ sp.toNat) (hdd : dd.toNat + 4 ≤ 2 ^ 32) (hvec : vec.toNat + 12 ≤ 2 ^ 32) (F : Nat := 1) :
    sinkCode n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d types[15]! inst mi f759 Cg
        (fun args => iprop(⌜args = [.i32 dd, .i32 ptr0, .i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          wIn n maxP hl live F ta (A 578) sp dd vec aidx vp p lo hi))
        (fun _ => 138 * cfg.regularOpCost + MemCpy.cost 0 * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          wIn n maxP hl live F ta (A 578) sp dd vec aidx vp p lo hi)) := by
  iintro #Hk
  have hlt := sp.toNat_lt
  iapply AllocFresh.MFunSpec_frame
    (Fr := iprop(stk n (sp.toNat - 256) 240 ∗ vt n 1057464 aidx ta (A 578) ∗ heapInv n maxP hl live F ∗
      n ↦[i32][ vp.toNat ] p ∗ n ↦[wms][ p.toNat ] u128Bytes lo hi ∗ n ↦[wms][ 1070974 ] lut))
    (P := fun args => iprop(⌜args = [.i32 dd, .i32 ptr0, .i32 0]⌝ ∗ n ↦[i32][ dd.toNat ] vec ∗
      roomPre n g gt sp vec 1 0 0 ptr0 [] []))
    (Q := fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ n ↦[i32][ dd.toNat ] vec ∗
      roomPost n g gt sp vec 1 0 0 ptr0 0 []))
  · intro args
    iintro ⟨%ha, Hg, Hw⟩
    iunfold wIn at Hw
    icases Hw with ⟨Hdd, Hs, Hvt, Hh, V0, V4, V8, Hvp, Hp, Hl⟩
    icases (stk_256_16 n (sp.toNat - 256)).1 $$ Hs with ⟨Hs1, Hs2⟩
    iframe Hdd Hs1 Hvt Hh Hvp Hp Hl
    isplitr; · ipureintro; exact ha
    iunfold roomPre
    iframe Hg V0 V4 V8
    isplitl [Hs2]
    · iapply stk_addr (show sp.toNat - 256 + 240 = sp.toNat - 16 by omega) $$ Hs2
    isplitl; · iapply memBytes_nil
    iapply memBytes_nil
  · intro args rs
    iintro ⟨⟨Hs1, Hvt, Hh, Hvp, Hp, Hl⟩, %hrs, Hdd, HQ⟩
    iunfold roomPost at HQ
    icases HQ with ⟨Hg, Hs2, V0, V4, V8, -, -⟩
    iframe Hg
    isplitr; · ipureintro; exact hrs
    iunfold wIn
    iframe Hdd Hvt Hh Hvp Hp Hl V0 V4
    isplitl [Hs1 Hs2]
    · iapply (stk_256_16 n (sp.toNat - 256)).2
      iframe Hs1
      iapply stk_addr (show sp.toNat - 16 = sp.toNat - 256 + 240 by omega) $$ Hs2
    rw [show (0 : UInt32) + 0 = 0 from rfl]
    iexact V8
  rw [show MemCpy.cost 0 = MemCpy.cost (UInt32.toNat 0) from rfl]
  iapply f759_room cfg lim d types[15]! (by rfl) inst mi A n g ta hm hd Cg gt sp dd vec 1 0 0 ptr0 0 [] []
    (by omega) rfl rfl hdd hvec (by decide) (by decide) (by have := ptr0.toNat_lt; simp; omega)
  iexact Hk

/-- The cost of `<&u128 as Display>::fmt` (353) into the empty `String`. -/
noncomputable def cost353 (cfg : WasmConfig) (lo hi : UInt64) : Nat :=
  14 * cfg.regularOpCost + (23 * cfg.regularOpCost + (FmtU128.cost lo hi * cfg.regularOpCost +
    activationGas cfg.regularOpCost (entryLocals f759 [.i32 0, .i32 0, .i32 0]) + costGrow cfg (kOf (val lo hi))))

theorem stk_256_144 (n a : Nat) :
    stk (GF := GF) n a 256 ⊣⊢ stk n a 112 ∗ stk n (a + 112) 144 :=
  ⟨stk_split n a 112 144, stk_join n a 112 144⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- The argument's formatter (353 through table entry 92) on `wIn`: the digits of the `u128`
written to the empty `String` (`wOut`). -/
theorem arg_353 (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 21 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp dd vec aidx vp p : UInt32) (maxP hl : Nat) (live : List (Nat × Nat))
    (lo hi : UInt64) (hsp : 256 ≤ sp.toNat) (hsp2 : sp.toNat + 48 ≤ 2 ^ 32) (hdd : dd.toNat + 4 ≤ 2 ^ 32)
    (hvec : vec.toNat + 12 ≤ 2 ^ 32) (hvp : vp.toNat + 4 ≤ 2 ^ 32) (hp : p.toNat + 16 ≤ 2 ^ 32)
    (hr : roomFor hl maxP (newCap 0 (kOf (val lo hi)))) (F : Nat := 1) (hF : okF F := by exact Or.inl rfl) :
    fmtCode inst mi A (A 759) f759 ∗ A 901 ↪[wf] FuncInst.wasm types[13]! inst f901 ∗ sinkCode n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d types[13]! inst mi f353 Cg
        (fun args => iprop(⌜args = [.i32 vp, .i32 (sp + 8)]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          fmtr n ta (sp + 8) dd 1065404 157 (A 759) ∗ wIn n maxP hl live F ta (A 578) sp dd vec aidx vp p lo hi))
        (fun _ => cost353 cfg lo hi)
        (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          fmtr n ta (sp + 8) dd 1065404 157 (A 759) ∗ wOut n maxP hl live F ta (A 578) sp dd vec aidx vp p lo hi)) := by
  iintro ⟨#Hfc, #H901, #Hsc⟩
  have hlt := sp.toNat_lt
  have h144 : (sp - 144).toNat = sp.toNat - 144 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have hL1 := decDigits_le lo hi
  have hL2 := FmtDigits.decDigits_length_pos (val lo hi)
  have hcN : (UInt32.ofNat (39 - (decDigits (val lo hi)).length)).toNat = 39 - (decDigits (val lo hi)).length := by
    simp; omega
  ihave #Sw := sink_grow cfg lim (d + 4) inst mi A n g ta hm (by omega) Cg gt (sp - 144)
    (UInt32.ofNat (39 - (decDigits (val lo hi)).length)) dd vec aidx maxP hl live (decDigits (val lo hi))
    (by omega) (by omega) (by omega) (by omega) hdd hvec hr (F := F) (hF := hF) $$ Hsc
  ihave #S353 := f353_spec cfg lim d types[13]! (by rfl) inst mi A n g ta hm (by omega) Cg gt lo hi vp p sp
    (sp + 8) dd 1065404 157 hvp hp (by omega) (by rw [UInt32.toNat_add]; simp; omega) (by decide) (A 759) f759
    (skPre n maxP hl live F ta (A 578) (sp - 144) dd vec aidx)
    (skPost n maxP hl live F ta (A 578) (sp - 144) dd vec aidx (kOf (val lo hi)) (decDigits (val lo hi)))
    (costGrow cfg (kOf (val lo hi))) $$ [Hfc H901 Sw]
  · iframe Hfc H901; unfold kOf; iexact Sw
  iunfold cost353
  iapply AllocFresh.MFunSpec_frame (Fr := iprop(True)) ?_ ?_ $$ S353
  · intro args
    iintro ⟨%ha, Hg, HF, Hw⟩
    iunfold wIn at Hw
    icases Hw with ⟨Hdd, Hs, Hvt, Hh, V0, V4, V8, Hvp, Hp, Hl⟩
    icases (stk_256_144 n (sp.toNat - 256)).1 $$ Hs with ⟨Hs1, Hs2⟩
    isplitl; swap; · ipureintro; trivial
    iframe Hvp Hp
    isplitr; · ipureintro; exact ha
    iunfold FmtU128.pre
    iframe Hg HF Hl
    isplitr; · ipureintro; rfl
    isplitl [Hs2]
    · iapply stk_addr (show sp.toNat - 256 + 112 = sp.toNat - 144 by omega) $$ Hs2
    iunfold skPre
    iframe Hdd Hvt Hh V0 V4 V8
    iapply stk_addr (show sp.toNat - 256 = (sp - 144).toNat - 112 by omega) $$ Hs1
  · intro args rs
    iintro ⟨-, Hvp, Hp, HQ⟩
    iunfold FmtU128.post at HQ
    icases HQ with ⟨%hrs, Hg, Hs2, Hl, HF, Hsk⟩
    iunfold skPost at Hsk
    icases Hsk with ⟨Hdd, Hs1, Hvt, Hsg⟩
    iframe Hg HF
    isplitr; · ipureintro; exact hrs
    iunfold wOut
    iframe Hdd Hvt Hsg Hvp Hp Hl
    iapply (stk_256_144 n (sp.toNat - 256)).2
    isplitl [Hs1]
    · iapply stk_addr (show (sp - 144).toNat - 112 = sp.toNat - 256 by omega) $$ Hs1
    iapply stk_addr (show sp.toNat - 144 = sp.toNat - 256 + 112 by omega) $$ Hs2

/-- The cost of `core::fmt::write` (872) formatting the `u128` into the empty `String`. -/
noncomputable def cost872 (cfg : WasmConfig) (lo hi : UInt64) : Nat :=
  100 * cfg.regularOpCost + activationGas cfg.regularOpCost (entryLocals f759 [.i32 0, .i32 0, .i32 0]) +
    (138 * cfg.regularOpCost + MemCpy.cost 0 * cfg.regularOpCost) +
    activationGas cfg.regularOpCost (entryLocals f353 [.i32 0, .i32 0]) + cost353 cfg lo hi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **`core::fmt::write(dd, 1065404, ar)`** (872) on `Arguments { pieces: [""], fmt: None,
args: [(vp, 92)] }` with `*dd = vec` the empty `String`: its decimal digits written to it. -/
theorem f872_u128 (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 22 < lim.maxCallDepth) (Cg : Nat) (gt : GlobalType)
    (s dd vec aidx ar argp vp p ptr0 : UInt32) (maxP hl : Nat) (live : List (Nat × Nat))
    (lo hi : UInt64) (hs : 304 ≤ s.toNat) (hdd : dd.toNat + 4 ≤ 2 ^ 32) (hvec : vec.toNat + 12 ≤ 2 ^ 32)
    (har : ar.toNat + 24 ≤ 2 ^ 32) (hargp : argp.toNat + 8 ≤ 2 ^ 32) (hvp : vp.toNat + 4 ≤ 2 ^ 32)
    (hp : p.toNat + 16 ≤ 2 ^ 32) (hr : roomFor hl maxP (newCap 0 (kOf (val lo hi)))) (F : Nat := 1) (hF : okF F := by exact Or.inl rfl) :
    fmtCode inst mi A (A 759) f759 ∗ A 901 ↪[wf] FuncInst.wasm types[13]! inst f901 ∗
      A 353 ↪[wf] FuncInst.wasm types[13]! inst f353 ∗ sinkCode n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f872 Cg
        (fun args => iprop(⌜args = [.i32 dd, .i32 1065404, .i32 ar]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - 48) 48 ∗ argsAt n ar 1051836 argp ∗
          pieceArg n ta 1051836 ptr0 0 argp vp 92 (A 353) ∗
          n ↦[i32][ (1065404 : UInt32).toNat + 12 ] 157 ∗ ta ↦[wt][ (157 : UInt32).toNat ] Ref.func (A 759) ∗
          wIn n maxP hl live F ta (A 578) (s - 48) dd vec aidx vp p lo hi))
        (fun _ => cost872 cfg lo hi)
        (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - 48) 48 ∗ argsAt n ar 1051836 argp ∗
          pieceArg n ta 1051836 ptr0 0 argp vp 92 (A 353) ∗
          n ↦[i32][ (1065404 : UInt32).toNat + 12 ] 157 ∗ ta ↦[wt][ (157 : UInt32).toNat ] Ref.func (A 759) ∗
          wOut n maxP hl live F ta (A 578) (s - 48) dd vec aidx vp p lo hi)) := by
  iintro ⟨#Hfc, #H901, #H353, #Hsc⟩
  have hlt := s.toNat_lt
  have hsp : (s - 48).toNat = s.toNat - 48 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  ihave #Sa := piece_room cfg lim (d + 1) inst mi A n g ta hm (by omega) Cg gt (s - 48) dd vec aidx vp p ptr0
    maxP hl live lo hi (by omega) hdd hvec (F := F) $$ Hsc
  ihave #Sb := arg_353 cfg lim (d + 1) inst mi A n g ta hm (by omega) Cg gt (s - 48) dd vec aidx vp p
    maxP hl live lo hi (by omega) (by omega) hdd hvec hvp hp hr (F := F) (hF := hF) $$ [Hfc H901 Hsc]
  · iframe Hfc H901 Hsc
  iunfold fmtCode at Hfc
  icases Hfc with ⟨-, -, -, -, -, -, #Hi, #Ha⟩
  iunfold cost872
  iapply f872_one cfg lim d type htype inst mi A n g ta hm (by omega) Cg gt s dd 1065404 ar 1051836 argp ptr0 0
    vp 92 157 (by omega) (by decide) har (by decide) hargp (A 759) (A 353) f759 f353
    (wIn n maxP hl live F ta (A 578) (s - 48) dd vec aidx vp p lo hi)
    (wIn n maxP hl live F ta (A 578) (s - 48) dd vec aidx vp p lo hi)
    (wOut n maxP hl live F ta (A 578) (s - 48) dd vec aidx vp p lo hi)
    (138 * cfg.regularOpCost + MemCpy.cost 0 * cfg.regularOpCost) (cost353 cfg lo hi)
  iframe Hi Ha H353 Sa Sb

/-- What `Write::write_fmt` (746 at `s`) needs besides its frame and the `Arguments`: the 304
bytes of stack below its frame, the piece `""` and the argument `(vp, 92)`, the `String`
vtable's `write_str` slot, the allocator, the heap, the empty `String` at `vec`, the `u128`. -/
def fIn (n maxP hl : Nat) (live : List (Nat × Nat)) (F : Nat) (ta a578 a353 a759 : Nat) (s argp vp p ptr0 vec aidx : UInt32)
    (lo hi : UInt64) : IProp GF :=
  iprop(stk n ((s - 32).toNat - 304) 304 ∗ pieceArg n ta 1051836 ptr0 0 argp vp 92 a353 ∗
    n ↦[i32][ (1065404 : UInt32).toNat + 12 ] 157 ∗ ta ↦[wt][ (157 : UInt32).toNat ] Ref.func a759 ∗
    vt n 1057464 aidx ta a578 ∗ heapInv n maxP hl live F ∗ n ↦[i32][ vec.toNat ] 1 ∗
    n ↦[i32][ vec.toNat + 4 ] 0 ∗ n ↦[i32][ vec.toNat + 8 ] 0 ∗ n ↦[i32][ vp.toNat ] p ∗
    n ↦[wms][ p.toNat ] u128Bytes lo hi ∗ n ↦[wms][ 1070974 ] lut)

/-- After: the `String` at `vec` holds the decimal digits of the `u128`. -/
def fOut (n maxP hl : Nat) (live : List (Nat × Nat)) (F : Nat) (ta a578 a353 a759 : Nat) (s argp vp p ptr0 vec aidx : UInt32)
    (lo hi : UInt64) : IProp GF :=
  iprop(stk n ((s - 32).toNat - 304) 304 ∗ pieceArg n ta 1051836 ptr0 0 argp vp 92 a353 ∗
    n ↦[i32][ (1065404 : UInt32).toNat + 12 ] 157 ∗ ta ↦[wt][ (157 : UInt32).toNat ] Ref.func a759 ∗
    vt n 1057464 aidx ta a578 ∗ strGrown n maxP hl live F vec (kOf (val lo hi)) (decDigits (val lo hi)) ∗
    n ↦[i32][ vp.toNat ] p ∗ n ↦[wms][ p.toNat ] u128Bytes lo hi ∗ n ↦[wms][ 1070974 ] lut)

theorem stk_304 (n a : Nat) :
    stk (GF := GF) n a 304 ⊣⊢ stk n a 256 ∗ stk n (a + 256) 48 :=
  ⟨stk_split n a 256 48, stk_join n a 256 48⟩

/-- The cost of `Write::write_fmt` (746) formatting the `u128` into the empty `String`. -/
noncomputable def cost746 (cfg : WasmConfig) (lo hi : UInt64) : Nat :=
  60 * cfg.regularOpCost + activationGas cfg.regularOpCost (entryLocals f872 [.i32 0, .i32 0, .i32 0]) +
    cost872 cfg lo hi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **`Write::write_fmt(vec, ap)`** (746) on the `Arguments` of `u128::to_string` at `ap`, `vec` the
empty `String`: `Ok`, the `String` holding the decimal digits. -/
theorem f746_u128 (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 23 < lim.maxCallDepth) (Cg : Nat) (gt : GlobalType)
    (s ap vec aidx argp vp p ptr0 : UInt32) (junk : List UInt8) (hjunk : junk.length = 4)
    (maxP hl : Nat) (live : List (Nat × Nat)) (lo hi : UInt64) (hs : 336 ≤ s.toNat)
    (hap : ap.toNat + 24 ≤ 2 ^ 32) (hvec : vec.toNat + 12 ≤ 2 ^ 32)
    (hargp : argp.toNat + 8 ≤ 2 ^ 32) (hvp : vp.toNat + 4 ≤ 2 ^ 32)
    (hp : p.toNat + 16 ≤ 2 ^ 32) (hr : roomFor hl maxP (newCap 0 (kOf (val lo hi)))) (F : Nat := 1) (hF : okF F := by exact Or.inl rfl) :
    fmtCode inst mi A (A 759) f759 ∗ A 901 ↪[wf] FuncInst.wasm types[13]! inst f901 ∗
      A 353 ↪[wf] FuncInst.wasm types[13]! inst f353 ∗ A 872 ↪[wf] FuncInst.wasm types[15]! inst f872 ∗
      sinkCode n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f746 Cg
        (fun args => iprop(⌜args = [.i32 vec, .i32 ap]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - 32) 32 ∗ argsAt n ap 1051836 argp ∗ n ↦[wms][ ap.toNat + 12 ] junk ∗
          fIn n maxP hl live F ta (A 578) (A 353) (A 759) s argp vp p ptr0 vec aidx lo hi))
        (fun _ => cost746 cfg lo hi)
        (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - 32) 32 ∗ argsAt n ap 1051836 argp ∗ n ↦[wms][ ap.toNat + 12 ] junk ∗
          fOut n maxP hl live F ta (A 578) (A 353) (A 759) s argp vp p ptr0 vec aidx lo hi)) := by
  iintro ⟨#Hfc, #H901, #H353, #H872, #Hsc⟩
  have hlt := s.toNat_lt
  have hsp : (s - 32).toNat = s.toNat - 32 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have hsp2 : (s - 32 - 48).toNat = s.toNat - 80 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le, hsp] <;> omega
  have h4 : (s - 32 + 4).toNat = (s - 32).toNat + 4 := by rw [UInt32.toNat_add, hsp]; simp; omega
  have h8 : (s - 32 + 8).toNat = (s - 32).toNat + 8 := by rw [UInt32.toNat_add, hsp]; simp; omega
  ihave #S872 := f872_u128 cfg lim (d + 1) types[15]! (by rfl) inst mi A n g ta hm (by omega) Cg gt (s - 32)
    (s - 32 + 4) vec aidx (s - 32 + 8) argp vp p ptr0 maxP hl live lo hi (by omega) (by omega) hvec
    (by omega) hargp hvp hp hr (F := F) (hF := hF) $$ [Hfc H901 H353 Hsc]
  · iframe Hfc H901 H353 Hsc
  iunfold fmtCode at Hfc
  icases Hfc with ⟨-, -, -, -, -, -, #Hi, -⟩
  iunfold cost746
  iapply FmtWrite.f746_gen cfg lim d type htype inst mi A n g ta hm (by omega) Cg gt s vec ap 1051836 argp junk
    hjunk (by omega) hap (fIn n maxP hl live F ta (A 578) (A 353) (A 759) s argp vp p ptr0 vec aidx lo hi)
    (fOut n maxP hl live F ta (A 578) (A 353) (A 759) s argp vp p ptr0 vec aidx lo hi)
  iframe Hi H872
  iapply AllocFresh.MFunSpec_frame (Fr := iprop(True)) ?_ ?_ $$ S872
  · intro args
    iintro ⟨%ha, Hg, HA, Hdd, HI⟩
    iunfold fIn at HI
    icases HI with ⟨Hs, HPA, V12, Ht, Hvt, Hh, V0, V4, V8, Hvp, Hp, Hl⟩
    icases (stk_304 n ((s - 32).toNat - 304)).1 $$ Hs with ⟨Hs1, Hs2⟩
    isplitl; swap; · ipureintro; trivial
    iframe Hg HA HPA V12 Ht
    isplitr; · ipureintro; exact ha
    isplitl [Hs2]
    · iapply stk_addr (show (s - 32).toNat - 304 + 256 = (s - 32).toNat - 48 by omega) $$ Hs2
    iunfold wIn
    iframe Hdd Hvt Hh V0 V4 V8 Hvp Hp Hl
    iapply stk_addr (show (s - 32).toNat - 304 = (s - 32 - 48).toNat - 256 by omega) $$ Hs1
  · intro args rs
    iintro ⟨-, %hrs, Hg, Hs2, HA, HPA, V12, Ht, HW⟩
    iunfold wOut at HW
    icases HW with ⟨Hdd, Hs1, Hvt, Hsg, Hvp, Hp, Hl⟩
    iframe Hg HA Hdd
    isplitr; · ipureintro; exact hrs
    iunfold fOut
    iframe HPA V12 Ht Hvt Hsg Hvp Hp Hl
    iapply (stk_304 n ((s - 32).toNat - 304)).2
    isplitl [Hs1]
    · iapply stk_addr (show (s - 32 - 48).toNat - 256 = (s - 32).toNat - 304 by omega) $$ Hs1
    iapply stk_addr (show (s - 32).toNat - 48 = (s - 32).toNat - 304 + 256 by omega) $$ Hs2

end Compose

end WNear.Binary.FmtString
