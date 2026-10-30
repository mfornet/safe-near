import Bridge.Functions.SerializeStr

/-!
# `serialize_str` (383) of strings with no byte to escape, over any piece of `ESCAPE`

`SerializeStr.f346_esc`, `f344_esc` and `f383_esc` own a chunk of `ESCAPE` that is all zero
(`InRange lo m`). A string of letters, digits, spaces and punctuation spans entries that are
not zero (`"` at 34 and `\` at 92) without hitting them. Here the chunk is any list `et` from
`1061808 + lo`, and each byte of the string must land on a zero entry (`EscZero lo et`):
`f346_tab`, `f344_tab` and `f383_tab`, the same proofs, at the same costs.
-/

namespace WNear.Binary.SerializeStr

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_word stk_addr)
open WNear.Binary.U128From (memBytes_split memBytes_join)

/-- Every byte `b` of `ds` lands, in the piece `et` of `ESCAPE` from `1061808 + lo`, on a zero
entry: no escape. -/
def EscZero (lo : Nat) (et : List UInt8) (ds : List UInt8) : Prop :=
  ∀ b ∈ ds, lo ≤ b.toNat ∧ b.toNat < lo + et.length ∧ et[b.toNat - lo]? = some 0

theorem escZero_of_inRange {lo m : Nat} {ds : List UInt8} (h : InRange lo m ds) :
    EscZero lo (List.replicate m 0) ds := by
  intro b hb
  obtain ⟨h1, h2⟩ := h b hb
  refine ⟨h1, by simp; omega, ?_⟩
  rw [List.getElem?_replicate]; simp; omega

theorem escZero_append {lo : Nat} {et a b : List UInt8} (ha : EscZero lo et a) (hb : EscZero lo et b) :
    EscZero lo et (a ++ b) := by
  intro x hx
  rcases List.mem_append.1 hx with h | h
  · exact ha x h
  · exact hb x h

section Tab

variable {GF : BundledGFunctors} [WasmGS NearState GF]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **`format_escaped_str_contents(ser, ser1, p, k)`** (346) on `k > 0` ASCII digits `ds` at `p`: no
byte needs escaping (`ESCAPE[b] = 0`), the scan runs to the end and the whole slice is written with
`write_all` (345) into the `Vec` behind `*ser`; `Ok` (the `i64` 3). -/
theorem f346_tab (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 6 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s ser ser1 vec ptr cap len p k : UInt32) (ob ds : List UInt8) (hs : 48 ≤ s.toNat)
    (hob : ob.length = k.toNat) (hds : ds.length = k.toNat) (hk0 : 0 < k.toNat) (lo : Nat) (et : List UInt8) (hdig : EscZero lo et ds)
    (hser : ser.toNat + 4 ≤ 2 ^ 32) (hvec : vec.toNat + 12 ≤ 2 ^ 32) (hroom : len.toNat + k.toNat ≤ cap.toNat)
    (hptr : ptr.toNat + cap.toNat < 2 ^ 32) (hp : p.toNat + k.toNat ≤ 2 ^ 32) :
    escCode inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f346 Cg
        (fun args => iprop(⌜args = [.i32 ser, .i32 ser1, .i32 p, .i32 k]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - 48) 48 ∗ n ↦[wms][ 1061808 + lo ] et ∗ n ↦[i32][ ser.toNat ] vec ∗
          n ↦[i32][ vec.toNat ] ptr ∗ n ↦[i32][ vec.toNat + 4 ] cap ∗ n ↦[i32][ vec.toNat + 8 ] len ∗
          n ↦[wms][ ptr.toNat + len.toNat ] ob ∗ n ↦[wms][ p.toNat ] ds))
        (fun _ => (265 + 32 * k.toNat) * cfg.regularOpCost + MemCpy.cost k.toNat * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = [.i64 3]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - 48) 48 ∗ n ↦[wms][ 1061808 + lo ] et ∗ n ↦[i32][ ser.toNat ] vec ∗
          n ↦[i32][ vec.toNat ] ptr ∗ n ↦[i32][ vec.toNat + 4 ] cap ∗ n ↦[i32][ vec.toNat + 8 ] (len + k) ∗
          n ↦[wms][ ptr.toNat + len.toNat ] ds ∗ n ↦[wms][ p.toNat ] ds)) := by
  iintro #Hk
  have h32' : (s - 32).toNat = s.toNat - 32 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  ihave #S345 := VecAppend.f345_room (GF := GF) cfg lim (d + 1) types[31]! (by rfl) inst mi A n g ta hm
    (by omega) Cg gt (s - 32) ser vec ptr cap len p k ob ds (by omega) hob hds hser hvec hroom hptr hp $$ [Hk]
  · iunfold escCode at Hk; icases Hk with ⟨#H, -⟩; iexact H
  iunfold escCode at Hk
  icases Hk with ⟨#Happ, #H345, #H683, #H691, #H761⟩
  iunfold VecAppend.appCode at Happ
  icases Happ with ⟨-, -, -, -, -, -, #Hi⟩
  have hn := hm.mem
  have hg := hm.glob
  have ha345 := hm.funcs 345 (by decide)
  have ha683 := hm.funcs 683 (by decide)
  have ha691 := hm.funcs 691 (by decide)
  have ha761 := hm.funcs 761 (by decide)
  have t31 : types[31]!.params.length = 3 := by rfl
  have t14 : types[14]!.params.length = 2 := by rfl
  have t21 : types[21]!.params.length = 0 := by rfl
  have hlt := s.toNat_lt
  have h32 : (s - 32).toNat = s.toNat - 32 := h32'
  have h48 : (s - 32 + 16).toNat = s.toNat - 16 := by
    rw [UInt32.toNat_add, h32]; simp; omega
  generalize hM : MemCpy.cost k.toNat * cfg.regularOpCost = M
  simp only [Nat.add_mul]
  generalize hL : 32 * k.toNat * cfg.regularOpCost = L
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, He, Hser, Hptr, Hcap, Hlen, Ho, Hds⟩
  subst hargs
  icases stk_split n (s.toNat - 48) 16 32 $$ Hs with ⟨Hs16, Hs⟩
  icases stk_split n (s.toNat - 48 + 16) 12 20 $$ Hs with ⟨Dst, Hs⟩
  icases stk_split n (s.toNat - 48 + 16 + 12) 4 16 $$ Hs with ⟨Gap, Hs⟩
  icases stk_split n (s.toNat - 48 + 16 + 12 + 4) 12 4 $$ Hs with ⟨Src, Top⟩
  iunfold stk at Dst Src
  icases Dst with ⟨%db, %hdb, Dst⟩
  icases Src with ⟨%sb, %hsb, Src⟩
  ihave Dst := memBytes_addr (show s.toNat - 48 + 16 = (s - 32).toNat by omega) $$ Dst
  ihave Src := memBytes_addr (show s.toNat - 48 + 16 + 12 + 4 = (s - 32 + 16).toNat by omega) $$ Src
  simp only [f346]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  repeat mstep
  mcall (f683_spec cfg lim (d + 1) types[31]! (by rfl) inst mi n hn Cg (s - 32 + 16) p (p + k) sb hsb
      (by omega)) using [Src]
  · iframe Src
  icases HQ with ⟨%hrs, W0, W4, W8⟩
  subst hrs
  repeat mstep
  mcall (f691_spec cfg lim (d + 1) types[14]! (by rfl) inst mi n hn Cg (s - 32) (s - 32 + 16) p (p + k) 0 db hdb
      (by omega) (by omega)) using [Dst W0 W4 W8]
  · iframe Dst W0 W4 W8
  icases HQ with ⟨%hrs, D0, D4, D8, W0, W4, W8⟩
  subst hrs
  repeat mstep
  mstep [D8]
  repeat mstep
  mstep [D4]
  repeat mstep
  mstep [D0]
  repeat mstep
  -- the outer loop, entered once
  iapply MemCpy.mwpi_loop0 (Cg := Cg)
    (R := 32 * k.toNat * cfg.regularOpCost + (187 * cfg.regularOpCost + M) + R)
    (I := invOut n inst mi Cg cfg.regularOpCost (187 * cfg.regularOpCost + M) R ser ser1 p k (s - 32) (1061808 + lo) (et) ds
      iprop(g ↦[wg] ⟨gt, .i32 (s - 32)⟩ ∗ stk n (s.toNat - 48) 16 ∗ stk n (s.toNat - 48 + 16 + 12) 4 ∗
        stk n (s.toNat - 48 + 16 + 12 + 4 + 12) 4 ∗
        n ↦[i32][ (s - 32 + 16).toNat ] p ∗ n ↦[i32][ (s - 32 + 16).toNat + 4 ] (p + k) ∗
        n ↦[i32][ (s - 32 + 16).toNat + 8 ] 0 ∗
        n ↦[i32][ (s - 32).toNat ] p ∗ n ↦[i32][ (s - 32).toNat + 4 ] (p + k) ∗
        n ↦[i32][ (s - 32).toNat + 8 ] 0 ∗
        n ↦[i32][ ser.toNat ] vec ∗ n ↦[i32][ vec.toNat ] ptr ∗ n ↦[i32][ vec.toNat + 4 ] cap ∗
        n ↦[i32][ vec.toNat + 8 ] len ∗ n ↦[wms][ ptr.toNat + len.toNat ] ob)) _ _ rfl
  isplitr
  · imodintro
    iintro %X %l HI
    iunfold invOut at HI
    icases HI with ⟨%⟨hX, hfr⟩, Hc, He, Hds, HP⟩
    subst hX
    rw [hfr, hL]
    mstep; mstep; mstep
    rw [FmtSink.add_sub_left]
    repeat mstep
    -- the scan
    iapply mwpi_cons
    iapply MemCpy.mwpi_loop0 (Cg := Cg)
      (R := L + (180 * cfg.regularOpCost + M) + R)
      (I := invIn n inst mi Cg cfg.regularOpCost (180 * cfg.regularOpCost + M) R ser ser1 p k (s - 32) (1061808 + lo) (et) ds
        iprop(g ↦[wg] ⟨gt, .i32 (s - 32)⟩ ∗ stk n (s.toNat - 48) 16 ∗ stk n (s.toNat - 48 + 16 + 12) 4 ∗
          stk n (s.toNat - 48 + 16 + 12 + 4 + 12) 4 ∗
          n ↦[i32][ (s - 32 + 16).toNat ] p ∗ n ↦[i32][ (s - 32 + 16).toNat + 4 ] (p + k) ∗
          n ↦[i32][ (s - 32 + 16).toNat + 8 ] 0 ∗
          n ↦[i32][ (s - 32).toNat ] p ∗ n ↦[i32][ (s - 32).toNat + 4 ] (p + k) ∗
          n ↦[i32][ (s - 32).toNat + 8 ] 0 ∗
          n ↦[i32][ ser.toNat ] vec ∗ n ↦[i32][ vec.toNat ] ptr ∗ n ↦[i32][ vec.toNat + 4 ] cap ∗
          n ↦[i32][ vec.toNat + 8 ] len ∗ n ↦[wms][ ptr.toNat + len.toNat ] ob)) _ _ rfl
    isplitr
    · imodintro
      iintro %X2 %l2 HI
      iunfold invIn at HI
      icases HI with ⟨%j, %jj, %x13, %x14, %x15, %⟨hX2, hfr2, hj, hjj⟩, Hc, He, Hds, HP⟩
      subst hX2
      rw [hfr2]
      simp only [frIn]
      by_cases hjk : j < k.toNat
      · -- one byte: a digit, no escape
        have hne : jj ≠ k := by intro h; subst h; omega
        have hjl : j < ds.length := by omega
        ihave Hds := MemCpy.memBytes_pick n p.toNat j ds hjl $$ Hds
        icases Hds with ⟨Hd1, Hdk, Hd2⟩
        have hb := hdig ds[j] (List.getElem_mem hjl)
        obtain ⟨b, hbj⟩ : ∃ b, ds[j] = b := ⟨_, rfl⟩
        rw [hbj] at hb
        rw [hbj]
        ihave He := MemCpy.memBytes_pick n (1061808 + lo) (b.toNat - lo) et (by omega) $$ He
        icases He with ⟨He1, Hek, He2⟩
        have hesc : et[b.toNat - lo]'(by omega) = 0 := (List.getElem?_eq_some_iff.1 hb.2.2).2
        have hc1 : Numeric.bool (Numeric.irelop32 IRelOp.eq k jj) = 0 := by
          simp [Numeric.bool, Numeric.irelop32]; exact fun h => hne h.symm
        have hkl := k.toNat_lt
        have hc2 : Numeric.bool (Numeric.irelop32 IRelOp.lt_u (0 + jj + 1) (0 + jj)) = 0 := by
          simp [Numeric.bool, Numeric.irelop32, UInt32.lt_iff_toNat_lt, UInt32.toNat_add]; omega
        rw [hesc]
        rw [show 32 * (k.toNat - j) * cfg.regularOpCost =
          30 * cfg.regularOpCost + (2 * cfg.regularOpCost + 32 * (k.toNat - (j + 1)) * cfg.regularOpCost) by
            rw [show 32 * (k.toNat - j) = 30 + (2 + 32 * (k.toNat - (j + 1))) by omega, Nat.add_mul, Nat.add_mul]]
        generalize hZ : 32 * (k.toNat - (j + 1)) * cfg.regularOpCost = Z
        repeat mstep
        mstep [Hdk] with (simp [UInt32.toNat_add]; omega)
        repeat mstep
        have hb8 := b.toNat_lt
        mstep [Hek] with (simp [UInt32.toNat_add, Memory.decodeLE, Bool.false_eq_true]; omega)
        repeat mstep
        simp only [Post.mloop]
        iapply pure_pay_intro'
        isplitl [Hc]
        · iexact Hc
        isplitr
        · ipureintro; exact ⟨by simp, by omega⟩
        inext
        iintro Hc
        ihave Hds := MemCpy.memBytes_unpick n p.toNat j (List.take j ds) b (List.drop (j + 1) ds)
          (by simp; omega) $$ [Hd1 Hdk Hd2]
        · iframe Hd1 Hdk Hd2
        ihave He := MemCpy.memBytes_unpick n (1061808 + lo) (b.toNat - lo) (List.take (b.toNat - lo) (et)) 0
          (List.drop (b.toNat - lo + 1) (et)) (by simp; omega) $$ [He1 Hek He2]
        · iframe He1 Hek He2
        have eds : List.take j ds ++ b :: List.drop (j + 1) ds = ds := by
          rw [← hbj]; simp
        have ees : List.take (b.toNat - lo) et ++ 0 :: List.drop (b.toNat - lo + 1) et = et := by
          have e := List.take_append_drop (b.toNat - lo) et
          rw [← List.getElem_cons_drop_succ_eq_drop (by omega), hesc] at e
          exact e
        rw [eds, ees]
        iunfold invIn
        iexists j + 1
        iexists jj + 1
        iexists UInt32.ofNat 0
        iexists 0 + jj + 1
        iexists UInt32.ofNat b.toNat
        rw [hZ]
        iframe He Hds HP
        isplitr
        · ipureintro
          refine ⟨rfl, ?_, by omega, ?_⟩
          · simp [frIn, loadValue, Memory.decodeLE]
          · rw [UInt32.toNat_add]; simp; omega
        iapply credits_le
        iframe Hc
        ipureintro; omega
      · -- the end of the slice: write it all, `Ok`
        have hjk' : j = k.toNat := by omega
        have hjj' : jj = k := UInt32.toNat_inj.mp (by omega)
        subst hjj' hjk'
        have hc1 : Numeric.bool (Numeric.irelop32 IRelOp.eq jj jj) = 1 := by
          simp [Numeric.bool, Numeric.irelop32]
        rw [Nat.sub_self, Nat.mul_zero, Nat.zero_mul, Nat.zero_add]
        repeat mstep
        simp only [Post.mloop, Post.mseq_br, List.append_nil, Post.mblock_br_zero]
        mpay
        repeat mstep
        mcall (f761_spec cfg lim (d + 1) types[21]! (by rfl) inst mi Cg) using []
        · ipureintro; trivial
        icases HQ with %hrs
        subst hrs
        have hc3 : Numeric.bool (Numeric.irelop32 IRelOp.eq 0 jj) = 0 := by
          simp [Numeric.bool, Numeric.irelop32]; intro h; rw [← h] at hk0; simp at hk0
        repeat mstep
        rw [UInt32.add_zero, UInt32.sub_zero]
        icases HP with ⟨Hg, Hs16, Gap, Top, W0, W4, W8, D0, D4, D8, Hser, Hptr, Hcap, Hlen, Ho⟩
        ihave Hs16 := stk_addr (show s.toNat - 48 = (s - 32).toNat - 16 by omega) $$ Hs16
        mcall S345 using [Hser Hg Hs16 Hptr Hcap Hlen Ho Hds]
        · iframe Hser
          iunfold FmtSink.roomPre
          iframe Hg Hs16 Hptr Hcap Hlen Ho Hds
        icases HQ with ⟨%hrs, Hser, HQ⟩
        subst hrs
        iunfold FmtSink.roomPost at HQ
        icases HQ with ⟨Hg, Hs16, Hptr, Hcap, Hlen, Ho, Hds⟩
        repeat mstep
        mstep [Hg]
        repeat mstep
        rw [show s - 32 + 32 = s by simp]
        mcredits R
        iframe Hc He Hser Hptr Hcap Hlen Ho Hds Hg
        isplitr
        · ipureintro; simp [htype]
        ihave Dst := words12 n _ p (p + jj) 0 $$ [D0 D4 D8]
        · iframe D0 D4 D8
        ihave Src := words12 n _ p (p + jj) 0 $$ [W0 W4 W8]
        · iframe W0 W4 W8
        iapply frame48 n s.toNat hs
        iframe Gap Top
        isplitl [Hs16]
        · iapply stk_addr (show (s - 32).toNat - 16 = s.toNat - 48 by omega) $$ Hs16
        isplitl [Dst]
        · iapply stk_addr (show (s - 32).toNat = s.toNat - 32 by omega) $$ Dst
        iapply stk_addr (show (s - 32 + 16).toNat = s.toNat - 16 by omega) $$ Src
    isplitl [Hc]
    · iapply credits_le
      iframe Hc
      ipureintro; omega
    inext
    iintro Hc
    iunfold invIn
    iexists 0
    iexists 0
    iexists 0
    iexists 0
    iexists 0
    rw [Nat.sub_zero, hL]
    iframe Hc He Hds HP
    ipureintro
    exact ⟨rfl, rfl, by omega, rfl⟩
  isplitl [Hc]
  · iapply credits_le
    iframe Hc
    ipureintro; omega
  inext
  iintro Hc
  iunfold invOut
  iframe Hc He Hds
  isplitr
  · ipureintro; exact ⟨rfl, rfl⟩
  iframe Hg Hs16 Gap Top W0 W4 W8 D0 D4 D8 Hser Hptr Hcap Hlen Ho

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **`format_escaped_str(ser, ser1, p, k)`** (344) on `k` decimal digits `ds`: `"`, the digits,
`"` appended to the `Vec` behind `*ser`. -/
theorem f344_tab (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 7 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s ser ser1 vec ptr cap len p k : UInt32) (ob ds : List UInt8) (hs : 48 ≤ s.toNat)
    (hob : ob.length = k.toNat + 2) (hds : ds.length = k.toNat) (hk0 : 0 < k.toNat) (lo : Nat) (et : List UInt8) (hdig : EscZero lo et ds)
    (hser : ser.toNat + 4 ≤ 2 ^ 32) (hvec : vec.toNat + 12 ≤ 2 ^ 32)
    (hroom : len.toNat + k.toNat + 2 ≤ cap.toNat)
    (hptr : ptr.toNat + cap.toNat < 2 ^ 32) (hp : p.toNat + k.toNat ≤ 2 ^ 32) :
    serCode inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f344 Cg
        (fun args => iprop(⌜args = [.i32 ser, .i32 ser1, .i32 p, .i32 k]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - 48) 48 ∗ n ↦[wms][ 1051817 ] [34] ∗ n ↦[wms][ 1061808 + lo ] et ∗
          n ↦[i32][ ser.toNat ] vec ∗
          n ↦[i32][ vec.toNat ] ptr ∗ n ↦[i32][ vec.toNat + 4 ] cap ∗ n ↦[i32][ vec.toNat + 8 ] len ∗
          n ↦[wms][ ptr.toNat + len.toNat ] ob ∗ n ↦[wms][ p.toNat ] ds))
        (fun _ => cost344 k.toNat * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = [.i64 3]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - 48) 48 ∗ n ↦[wms][ 1051817 ] [34] ∗ n ↦[wms][ 1061808 + lo ] et ∗
          n ↦[i32][ ser.toNat ] vec ∗
          n ↦[i32][ vec.toNat ] ptr ∗ n ↦[i32][ vec.toNat + 4 ] cap ∗ n ↦[i32][ vec.toNat + 8 ] (len + k + 2) ∗
          n ↦[wms][ ptr.toNat + len.toNat ] ([34] ++ ds ++ [34]) ∗ n ↦[wms][ p.toNat ] ds)) := by
  obtain ⟨o0, rest, rfl⟩ : ∃ o0 rest, ob = o0 :: rest := by
    cases ob with
    | nil => simp at hob
    | cons a l => exact ⟨a, l, rfl⟩
  obtain ⟨mid, o2, rfl⟩ : ∃ mid o2, rest = mid ++ [o2] := by
    rcases List.eq_nil_or_concat rest with h | ⟨L, b, h⟩
    · subst h; simp at hob
    · exact ⟨L, b, by simpa using h⟩
  have hmid : mid.length = k.toNat := by simp at hob; omega
  iintro #Hk
  iunfold serCode at Hk
  icases Hk with ⟨#He, #H346, #H344, #H367⟩
  have hlt := s.toNat_lt
  have hlen := len.toNat_lt
  have hkl := k.toNat_lt
  have h1 : (len + 1).toNat = len.toNat + 1 := by rw [UInt32.toNat_add]; simp; omega
  have h2 : (len + 1 + k).toNat = len.toNat + 1 + k.toNat := by rw [UInt32.toNat_add, h1]; simp; omega
  have h16 : 16 ≤ s.toNat := by omega
  ihave #S1 := VecAppend.f345_room (GF := GF) cfg lim (d + 1) types[31]! (by rfl) inst mi A n g ta hm
    (by omega) Cg gt s ser vec ptr cap len 1051817 1 [o0] [34] h16 (by simp) (by simp)
    hser hvec (by simp; omega) hptr (by simp) $$ [He]
  · iunfold escCode at He; icases He with ⟨#H, -⟩; iexact H
  ihave #S2 := f346_tab (GF := GF) cfg lim (d + 1) types[48]! (by rfl) inst mi A n g ta hm
    (by omega) Cg gt s ser ser vec ptr cap (len + 1) p k mid ds hs hmid hds hk0
    lo et hdig hser hvec (by omega) hptr hp $$ [He]
  · iexact He
  ihave #S3 := VecAppend.f345_room (GF := GF) cfg lim (d + 1) types[31]! (by rfl) inst mi A n g ta hm
    (by omega) Cg gt s ser vec ptr cap (len + 1 + k) 1051817 1 [o2] [34] h16
    (by simp) (by simp) hser hvec (by simp; omega) hptr (by simp) $$ [He]
  · iunfold escCode at He; icases He with ⟨#H, -⟩; iexact H
  iunfold escCode at He
  icases He with ⟨#Happ, #H345, -, -, -⟩
  iunfold VecAppend.appCode at Happ
  icases Happ with ⟨-, -, -, -, -, -, #Hi⟩
  have hn := hm.mem
  have ha345 := hm.funcs 345 (by decide)
  have ha346 := hm.funcs 346 (by decide)
  have t31 : types[31]!.params.length = 3 := by rfl
  have t48 : types[48]!.params.length = 4 := by rfl
  generalize hM1 : MemCpy.cost (UInt32.toNat 1) * cfg.regularOpCost = M1
  generalize hMk : MemCpy.cost k.toNat * cfg.regularOpCost = Mk
  have hcost : cost344 k.toNat * cfg.regularOpCost = 600 * cfg.regularOpCost +
      32 * k.toNat * cfg.regularOpCost + M1 + M1 + Mk := by
    rw [← hM1, ← hMk, show (1 : UInt32).toNat = 1 from rfl]; unfold cost344
    simp only [Nat.add_mul, Nat.mul_assoc]; omega
  rw [hcost, Nat.add_mul 265]
  generalize 32 * k.toNat * cfg.regularOpCost = L
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, Hq, Hesc, Hser, Hptr, Hcap, Hlen, Ho, Hds⟩
  subst hargs
  ihave Ho := (MemCpy.memBytes_cons n _ o0 (mid ++ [o2])).1 $$ Ho
  icases Ho with ⟨O0, Ho⟩
  icases (memBytes_append (GF := GF) (H := NearState) n _ mid [o2]).1 $$ Ho with ⟨Om, O2⟩
  icases stk_split n (s.toNat - 48) 32 16 $$ Hs with ⟨Hs32, Hs16⟩
  ihave Hs16 := stk_addr (show s.toNat - 48 + 32 = s.toNat - 16 by omega) $$ Hs16
  simp only [f344]
  repeat mstep
  mcall S1 using [Hser Hg Hs16 Hptr Hcap Hlen O0 Hq]
  · iframe Hser
    iunfold FmtSink.roomPre
    iframe Hg Hs16 Hptr Hcap Hlen O0
    iapply memBytes_addr (show (1051817 : Nat) = UInt32.toNat 1051817 by decide) $$ Hq
  icases HQ with ⟨%hrs, Hser, HQ⟩
  subst hrs
  iunfold FmtSink.roomPost at HQ
  icases HQ with ⟨Hg, Hs16, Hptr, Hcap, Hlen, O0, Hq⟩
  ihave Hs16 := stk_addr (show s.toNat - 16 = s.toNat - 48 + 32 by omega) $$ Hs16
  ihave Hs := stk_join n (s.toNat - 48) 32 16 $$ [Hs32 Hs16]
  · iframe Hs32 Hs16
  ihave Om := memBytes_addr (show ptr.toNat + len.toNat + 1 = ptr.toNat + (len + 1).toNat by omega) $$ Om
  repeat mstep
  mcall S2 using [Hg Hs Hesc Hser Hptr Hcap Hlen Om Hds]
  · iframe Hg Hs Hesc Hser Hptr Hcap Hlen Om Hds
  icases HQ with ⟨%hrs, Hg, Hs, Hesc, Hser, Hptr, Hcap, Hlen, Om, Hds⟩
  subst hrs
  repeat mstep
  ihave O2 := memBytes_addr (show ptr.toNat + len.toNat + 1 + mid.length = ptr.toNat + (len + 1 + k).toNat by
    omega) $$ O2
  icases stk_split n (s.toNat - 48) 32 16 $$ Hs with ⟨Hs32, Hs16⟩
  ihave Hs16 := stk_addr (show s.toNat - 48 + 32 = s.toNat - 16 by omega) $$ Hs16
  mcall S3 using [Hser Hg Hs16 Hptr Hcap Hlen O2 Hq]
  · iframe Hser
    iunfold FmtSink.roomPre
    iframe Hg Hs16 Hptr Hcap Hlen O2
    iapply memBytes_addr (show (1051817 : Nat) = UInt32.toNat 1051817 by decide) $$ Hq
  icases HQ with ⟨%hrs, Hser, HQ⟩
  subst hrs
  iunfold FmtSink.roomPost at HQ
  icases HQ with ⟨Hg, Hs16, Hptr, Hcap, Hlen, O2, Hq⟩
  repeat mstep
  mcredits R
  have elen : len + 1 + k + 1 = len + k + 2 := by
    apply UInt32.toNat_inj.mp; simp [UInt32.toNat_add]; omega
  rw [elen]
  iframe Hc Hg Hesc Hser Hptr Hcap Hlen Hds
  isplitr
  · ipureintro; simp [htype]
  isplitl [Hs32 Hs16]
  · iapply stk_join n (s.toNat - 48) 32 16
    iframe Hs32
    iapply stk_addr (show s.toNat - 16 = s.toNat - 48 + 32 by omega) $$ Hs16
  iframe Hq
  iapply (MemCpy.memBytes_cons n _ 34 (ds ++ [34])).2
  iframe O0
  iapply (memBytes_append (GF := GF) (H := NearState) n _ ds [34]).2
  isplitl [Om]
  · iapply memBytes_addr (show ptr.toNat + (len + 1).toNat = ptr.toNat + len.toNat + 1 by
      omega) $$ Om
  iapply memBytes_addr (show ptr.toNat + (len + 1 + k).toNat = ptr.toNat + len.toNat + 1 + ds.length by
    omega) $$ O2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **`serialize_str(ser, p, k)`** (383) on `0 < k` ASCII decimal digits `ds` at `p`, into the
`Vec<u8>` `(ptr, cap, len)` behind `*ser` with room for `k + 2` bytes: the JSON string
`"` ++ `ds` ++ `"` appended, `Ok` (0). -/
theorem f383_tab (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 8 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s ser vec ptr cap len p k : UInt32) (ob ds : List UInt8) (hs : 48 ≤ s.toNat)
    (hob : ob.length = k.toNat + 2) (hds : ds.length = k.toNat) (hk0 : 0 < k.toNat) (lo : Nat) (et : List UInt8) (hdig : EscZero lo et ds)
    (hser : ser.toNat + 4 ≤ 2 ^ 32) (hvec : vec.toNat + 12 ≤ 2 ^ 32)
    (hroom : len.toNat + k.toNat + 2 ≤ cap.toNat)
    (hptr : ptr.toNat + cap.toNat < 2 ^ 32) (hp : p.toNat + k.toNat ≤ 2 ^ 32) :
    serCode inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f383 Cg
        (fun args => iprop(⌜args = [.i32 ser, .i32 p, .i32 k]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - 48) 48 ∗ n ↦[wms][ 1051817 ] [34] ∗ n ↦[wms][ 1061808 + lo ] et ∗
          n ↦[i32][ ser.toNat ] vec ∗
          n ↦[i32][ vec.toNat ] ptr ∗ n ↦[i32][ vec.toNat + 4 ] cap ∗ n ↦[i32][ vec.toNat + 8 ] len ∗
          n ↦[wms][ ptr.toNat + len.toNat ] ob ∗ n ↦[wms][ p.toNat ] ds))
        (fun _ => cost383 k.toNat * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - 48) 48 ∗ n ↦[wms][ 1051817 ] [34] ∗ n ↦[wms][ 1061808 + lo ] et ∗
          n ↦[i32][ ser.toNat ] vec ∗
          n ↦[i32][ vec.toNat ] ptr ∗ n ↦[i32][ vec.toNat + 4 ] cap ∗ n ↦[i32][ vec.toNat + 8 ] (len + k + 2) ∗
          n ↦[wms][ ptr.toNat + len.toNat ] ([34] ++ ds ++ [34]) ∗ n ↦[wms][ p.toNat ] ds)) := by
  iintro #Hk
  ihave #S344 := f344_tab (GF := GF) cfg lim (d + 1) types[48]! (by rfl) inst mi A n g ta hm (by omega) Cg
    gt s ser ser vec ptr cap len p k ob ds hs hob hds hk0 lo et hdig hser hvec hroom hptr hp $$ Hk
  iunfold serCode at Hk
  icases Hk with ⟨#He, -, #H344, #H367⟩
  iunfold escCode at He
  icases He with ⟨#Happ, -, -, -, -⟩
  iunfold VecAppend.appCode at Happ
  icases Happ with ⟨-, -, -, -, -, -, #Hi⟩
  have ha344 := hm.funcs 344 (by decide)
  have ha367 := hm.funcs 367 (by decide)
  have t48 : types[48]!.params.length = 4 := by rfl
  have t35 : types[35]!.params.length = 1 := by rfl
  unfold cost383
  rw [Nat.add_mul]
  generalize cost344 k.toNat * cfg.regularOpCost = C
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, HP⟩
  subst hargs
  simp only [f383]
  repeat mstep
  mcall S344 using [HP]
  · iframe HP
  icases HQ with ⟨%hrs, HP⟩
  subst hrs
  mcall (f367_ok cfg lim (d + 1) types[35]! (by rfl) inst mi Cg) using []
  · ipureintro; trivial
  icases HQ with %hrs
  subst hrs
  repeat mstep
  mstep_post
  mcredits R
  iframe Hc HP
  ipureintro; simp [htype]

end Tab

end WNear.Binary.SerializeStr
