import Bridge.Functions.WriteSink
import Bridge.Functions.MetadataFields

/-!
# The struct pieces of `serde_json` on a sink (M5)

`SerializeStrTab` and `SerdeStructTab` write strings and keys into `outV` with room. Here the
same pieces are proved over any sink `S` with a `write_all` specification
(`WriteSink.WaSpec C S B K`): the bytes written so far are `S w`, each `write_all` appends at
`K k`. With `WriteSink.vsink` the output may outgrow the `Vec`'s capacity once, the writes of a
piece below the bound `B`.

* `f346_s`, `f344_s`, `strFn_s`: `format_escaped_str_contents`, `format_escaped_str` and
  `serialize_str` of bytes landing on zero entries of `ESCAPE`.
* `piece_s`, `keyRest_s`: a one-byte piece and the key of a later field.
* `f105_s`: the `u8` field (105) holding a two-digit value: the key, `:`, the digits.

Each needs 112 bytes of stack below the call (the 80 of `write_all` and the frames above it).
-/

namespace WNear.Binary.SerdeSink

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_word stk_addr)
open WNear.Binary.U128From (memBytes_split memBytes_join)
open WNear.Binary.BorshFT (splitB joinB stkJ stkSp stkA)
open WNear.Binary.SerializeStr
open WNear.Binary.WriteSink (WaSpec)

section Sink

variable {GF : BundledGFunctors} [WasmGS NearState GF]


set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **`format_escaped_str_contents(ser, ser1, p, k)`** (346) on `k > 0` ASCII digits `ds` at `p`: no
byte needs escaping (`ESCAPE[b] = 0`), the scan runs to the end and the whole slice is written with
`write_all` (345) into the `Vec` behind `*ser`; `Ok` (the `i64` 3). -/
theorem f346_s (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 17 < lim.maxCallDepth) (Cg : Nat) (gt : GlobalType)
    (C : IProp GF) [Persistent C] (ser : UInt32) (S : List UInt8 → IProp GF) (B : Nat) (K : Nat → Nat)
    (hW : WaSpec cfg lim inst mi Cg n g gt C ser S B K)
    (s ser1 p k : UInt32) (w ds : List UInt8) (hs : 112 ≤ s.toNat)
    (hds : ds.length = k.toNat) (hk0 : 0 < k.toNat) (lo : Nat) (et : List UInt8) (hdig : EscZero lo et ds)
    (hp : p.toNat + k.toNat ≤ 2 ^ 32) (hB : w.length + k.toNat ≤ B) :
    escCode inst mi A ∗ C
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f346 Cg
        (fun args => iprop(⌜args = [.i32 ser, .i32 ser1, .i32 p, .i32 k]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - 112) 112 ∗ n ↦[wms][ 1061808 + lo ] et ∗ S w ∗ n ↦[wms][ p.toNat ] ds))
        (fun _ => (130 + 32 * k.toNat) * cfg.regularOpCost + K k.toNat)
        (fun _ rs => iprop(⌜rs = [.i64 3]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - 112) 112 ∗ n ↦[wms][ 1061808 + lo ] et ∗ S (w ++ ds) ∗ n ↦[wms][ p.toNat ] ds)) := by
  iintro ⟨#Hk, #C⟩
  have h32' : (s - 32).toNat = s.toNat - 32 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  ihave #S345 := hW (d + 1) (s - 32) p k w ds (by omega) (by omega) hds hp hB $$ C
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
  generalize hM : K k.toNat = M
  simp only [Nat.add_mul]
  generalize hL : 32 * k.toNat * cfg.regularOpCost = L
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, He, HS, Hds⟩
  icases stk_split n (s.toNat - 112) 64 48 $$ Hs with ⟨Lo, Hs⟩
  ihave Hs := stk_addr (show s.toNat - 112 + 64 = s.toNat - 48 by omega) $$ Hs
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
    (R := 32 * k.toNat * cfg.regularOpCost + (52 * cfg.regularOpCost + M) + R)
    (I := invOut n inst mi Cg cfg.regularOpCost (52 * cfg.regularOpCost + M) R ser ser1 p k (s - 32) (1061808 + lo) (et) ds
      iprop(g ↦[wg] ⟨gt, .i32 (s - 32)⟩ ∗ stk n (s.toNat - 48) 16 ∗ stk n (s.toNat - 48 + 16 + 12) 4 ∗
        stk n (s.toNat - 48 + 16 + 12 + 4 + 12) 4 ∗
        n ↦[i32][ (s - 32 + 16).toNat ] p ∗ n ↦[i32][ (s - 32 + 16).toNat + 4 ] (p + k) ∗
        n ↦[i32][ (s - 32 + 16).toNat + 8 ] 0 ∗
        n ↦[i32][ (s - 32).toNat ] p ∗ n ↦[i32][ (s - 32).toNat + 4 ] (p + k) ∗
        n ↦[i32][ (s - 32).toNat + 8 ] 0 ∗
        stk n (s.toNat - 112) 64 ∗ S w)) _ _ rfl
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
      (R := L + (45 * cfg.regularOpCost + M) + R)
      (I := invIn n inst mi Cg cfg.regularOpCost (45 * cfg.regularOpCost + M) R ser ser1 p k (s - 32) (1061808 + lo) (et) ds
        iprop(g ↦[wg] ⟨gt, .i32 (s - 32)⟩ ∗ stk n (s.toNat - 48) 16 ∗ stk n (s.toNat - 48 + 16 + 12) 4 ∗
          stk n (s.toNat - 48 + 16 + 12 + 4 + 12) 4 ∗
          n ↦[i32][ (s - 32 + 16).toNat ] p ∗ n ↦[i32][ (s - 32 + 16).toNat + 4 ] (p + k) ∗
          n ↦[i32][ (s - 32 + 16).toNat + 8 ] 0 ∗
          n ↦[i32][ (s - 32).toNat ] p ∗ n ↦[i32][ (s - 32).toNat + 4 ] (p + k) ∗
          n ↦[i32][ (s - 32).toNat + 8 ] 0 ∗
          stk n (s.toNat - 112) 64 ∗ S w)) _ _ rfl
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
        icases HP with ⟨Hg, Hs16, Gap, Top, W0, W4, W8, D0, D4, D8, Lo, HS⟩
        ihave Hs80 := stkJ (a := s.toNat - 112) (b := s.toNat - 48) (k1 := 64) (k2 := 16) (k := 80) (by omega) rfl $$ [Lo Hs16]
        · iframe Lo Hs16
        ihave Hs80 := stk_addr (show s.toNat - 112 = (s - 32).toNat - 80 by omega) $$ Hs80
        mcall S345 using [Hg Hs80 HS Hds]
        · iframe Hg Hs80 HS Hds
        icases HQ with ⟨%hrs, Hg, Hs80, HS, Hds⟩
        subst hrs
        ihave Hs80 := stk_addr (show (s - 32).toNat - 80 = s.toNat - 112 by omega) $$ Hs80
        icases stkSp 64 16 rfl $$ Hs80 with ⟨Lo, Hs16⟩
        repeat mstep
        mstep [Hg]
        repeat mstep
        rw [show s - 32 + 32 = s by simp]
        mcredits R
        iframe Hc He HS Hds Hg
        isplitr
        · ipureintro; simp [htype]
        ihave Dst := words12 n _ p (p + jj) 0 $$ [D0 D4 D8]
        · iframe D0 D4 D8
        ihave Src := words12 n _ p (p + jj) 0 $$ [W0 W4 W8]
        · iframe W0 W4 W8
        iapply stkJ (a := s.toNat - 112) (b := s.toNat - 48) (k1 := 64) (k2 := 48) (by omega) rfl
        iframe Lo
        iapply frame48 n s.toNat (by omega)
        iframe Gap Top
        isplitl [Hs16]
        · iapply stk_addr (show s.toNat - 112 + 64 = s.toNat - 48 by omega) $$ Hs16
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
  iframe Hg Hs16 Gap Top W0 W4 W8 D0 D4 D8 Lo HS

/-- The cost of `format_escaped_str` on a sink: 344's own, 346's and the three writes. -/
def cost344s (cfg : WasmConfig) (K : Nat → Nat) (k : Nat) : Nat :=
  (195 + 32 * k) * cfg.regularOpCost + K 1 + K 1 + K k

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **`format_escaped_str(ser, ser1, p, k)`** (344) on a sink: `"`, the bytes `ds` (on zero entries
of `ESCAPE`), `"`. -/
theorem f344_s (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 18 < lim.maxCallDepth) (Cg : Nat) (gt : GlobalType)
    (C : IProp GF) [Persistent C] (ser : UInt32) (S : List UInt8 → IProp GF) (B : Nat) (K : Nat → Nat)
    (hW : WaSpec cfg lim inst mi Cg n g gt C ser S B K)
    (s ser1 p k : UInt32) (w ds : List UInt8) (hs : 112 ≤ s.toNat)
    (hds : ds.length = k.toNat) (hk0 : 0 < k.toNat) (lo : Nat) (et : List UInt8) (hdig : EscZero lo et ds)
    (hp : p.toNat + k.toNat ≤ 2 ^ 32) (hB : w.length + k.toNat + 2 ≤ B) :
    serCode inst mi A ∗ C
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f344 Cg
        (fun args => iprop(⌜args = [.i32 ser, .i32 ser1, .i32 p, .i32 k]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - 112) 112 ∗ n ↦[wms][ 1051817 ] [34] ∗ n ↦[wms][ 1061808 + lo ] et ∗ S w ∗
          n ↦[wms][ p.toNat ] ds))
        (fun _ => cost344s cfg K k.toNat)
        (fun _ rs => iprop(⌜rs = [.i64 3]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - 112) 112 ∗ n ↦[wms][ 1051817 ] [34] ∗ n ↦[wms][ 1061808 + lo ] et ∗
          S (w ++ ([34] ++ ds ++ [34])) ∗ n ↦[wms][ p.toNat ] ds)) := by
  iintro ⟨#Hk, #C⟩
  iunfold serCode at Hk
  icases Hk with ⟨#He, #H346, #H344, #H367⟩
  have hlt := s.toNat_lt
  ihave #S1 := hW (d + 1) s 1051817 1 w [34] (by omega) (by omega) rfl (by decide) (by simp; omega) $$ C
  have S2' := f346_s (GF := GF) cfg lim (d + 1) types[48]! (by rfl) inst mi A n g ta hm (by omega) Cg gt C ser S
    B K hW s ser p k (w ++ [34]) ds hs hds hk0 lo et hdig hp (by simp; omega)
  rw [Nat.add_mul 130] at S2'
  ihave #S2 := S2' $$ [He C]
  · iframe He C
  ihave #S3 := hW (d + 1) s 1051817 1 (w ++ [34] ++ ds) [34] (by omega) (by omega) rfl (by decide)
    (by simp; omega) $$ C
  iunfold escCode at He
  icases He with ⟨#Happ, #H345, -, -, -⟩
  iunfold VecAppend.appCode at Happ
  icases Happ with ⟨-, -, -, -, -, -, #Hi⟩
  have hn := hm.mem
  have ha345 := hm.funcs 345 (by decide)
  have ha346 := hm.funcs 346 (by decide)
  have t31 : types[31]!.params.length = 3 := by rfl
  have t48 : types[48]!.params.length = 4 := by rfl
  unfold cost344s
  rw [Nat.add_mul 195]
  generalize 32 * k.toNat * cfg.regularOpCost = L
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, Hq, Hesc, HS, Hds⟩
  subst hargs
  icases stkSp 32 80 rfl $$ Hs with ⟨Hs32, Hs80⟩
  ihave Hs80 := stk_addr (show s.toNat - 112 + 32 = s.toNat - 80 by omega) $$ Hs80
  ihave Hq := memBytes_addr (show (1051817 : Nat) = UInt32.toNat 1051817 by decide) $$ Hq
  simp only [f344]
  repeat mstep
  mcall S1 using [Hg Hs80 HS Hq]
  · iframe Hg Hs80 HS Hq
  icases HQ with ⟨%hrs, Hg, Hs80, HS, Hq⟩
  subst hrs
  ihave Hs80 := stk_addr (show s.toNat - 80 = s.toNat - 112 + 32 by omega) $$ Hs80
  ihave Hs := stkJ (a := s.toNat - 112) (b := s.toNat - 112 + 32) (k1 := 32) (k2 := 80) (k := 112) rfl rfl
    $$ [Hs32 Hs80]
  · iframe Hs32 Hs80
  repeat mstep
  mcall S2 using [Hg Hs Hesc HS Hds]
  · iframe Hg Hs Hesc HS Hds
  icases HQ with ⟨%hrs, Hg, Hs, Hesc, HS, Hds⟩
  subst hrs
  repeat mstep
  icases stkSp 32 80 rfl $$ Hs with ⟨Hs32, Hs80⟩
  ihave Hs80 := stk_addr (show s.toNat - 112 + 32 = s.toNat - 80 by omega) $$ Hs80
  mcall S3 using [Hg Hs80 HS Hq]
  · iframe Hg Hs80 HS Hq
  icases HQ with ⟨%hrs, Hg, Hs80, HS, Hq⟩
  subst hrs
  repeat mstep
  mcredits R
  iframe Hc Hg Hesc Hds
  isplitr
  · ipureintro; simp [htype]
  isplitl [Hs32 Hs80]
  · iapply stkJ (a := s.toNat - 112) (b := s.toNat - 80) (k1 := 32) (k2 := 80) (k := 112) (by omega) rfl
    iframe Hs32 Hs80
  iframe Hq
  simp only [List.append_assoc, List.cons_append, List.nil_append] at *
  iexact HS

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **`serialize_str`** (`strFn ce`, `ce` with 367's code) on a sink: the JSON string `"ds"`. -/
theorem strFn_s (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 19 < lim.maxCallDepth) (Cg : Nat) (gt : GlobalType)
    (C : IProp GF) [Persistent C] (ser : UInt32) (S : List UInt8 → IProp GF) (B : Nat) (K : Nat → Nat)
    (hW : WaSpec cfg lim inst mi Cg n g gt C ser S B K) (ce : Nat) (hce : ce < 955)
    (s p k : UInt32) (w ds : List UInt8) (hs : 112 ≤ s.toNat)
    (hds : ds.length = k.toNat) (hk0 : 0 < k.toNat) (lo : Nat) (et : List UInt8) (hdig : EscZero lo et ds)
    (hp : p.toNat + k.toNat ≤ 2 ^ 32) (hB : w.length + k.toNat + 2 ≤ B) :
    serCode inst mi A ∗ A ce ↪[wf] FuncInst.wasm types[35]! inst f367 ∗ C
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi (SerdeStruct.strFn ce) Cg
        (fun args => iprop(⌜args = [.i32 ser, .i32 p, .i32 k]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - 112) 112 ∗ n ↦[wms][ 1051817 ] [34] ∗ n ↦[wms][ 1061808 + lo ] et ∗ S w ∗
          n ↦[wms][ p.toNat ] ds))
        (fun _ => 44 * cfg.regularOpCost + cost344s cfg K k.toNat)
        (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - 112) 112 ∗ n ↦[wms][ 1051817 ] [34] ∗ n ↦[wms][ 1061808 + lo ] et ∗
          S (w ++ ([34] ++ ds ++ [34])) ∗ n ↦[wms][ p.toNat ] ds)) := by
  iintro ⟨#Hk, #H367, #C⟩
  ihave #S344 := f344_s (GF := GF) cfg lim (d + 1) types[48]! (by rfl) inst mi A n g ta hm (by omega) Cg gt C ser
    S B K hW s ser p k w ds hs hds hk0 lo et hdig hp hB $$ [Hk C]
  · iframe Hk C
  iunfold serCode at Hk
  icases Hk with ⟨#He, -, #H344, -⟩
  iunfold escCode at He
  icases He with ⟨#Happ, -, -, -, -⟩
  iunfold VecAppend.appCode at Happ
  icases Happ with ⟨-, -, -, -, -, -, #Hi⟩
  have ha344 := hm.funcs 344 (by decide)
  have hace := hm.funcs ce hce
  have t48 : types[48]!.params.length = 4 := by rfl
  have t35 : types[35]!.params.length = 1 := by rfl
  generalize cost344s cfg K k.toNat = X
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, HP⟩
  subst hargs
  simp only [SerdeStruct.strFn]
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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **A one-byte piece** (`pieceFn cw a`, `cw` with 345's code) on a sink: the byte `b` at `a`. -/
theorem piece_s (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 17 < lim.maxCallDepth) (Cg : Nat) (gt : GlobalType)
    (C : IProp GF) [Persistent C] (ser : UInt32) (S : List UInt8 → IProp GF) (B : Nat) (K : Nat → Nat)
    (hW : WaSpec cfg lim inst mi Cg n g gt C ser S B K) (cw : Nat) (hcw : cw < 955) (a : UInt32)
    (s : UInt32) (w : List UInt8) (b : UInt8) (hs : 80 ≤ s.toNat) (ha : a.toNat + 1 ≤ 2 ^ 32)
    (hB : w.length + 1 ≤ B) :
    A cw ↪[wf] FuncInst.wasm types[31]! inst f345 ∗ inst ↪[inst] mi ∗ C
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi (SerdeStruct.pieceFn cw a) Cg
        (fun args => iprop(⌜args = [.i32 ser]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 80) 80 ∗ S w ∗
          n ↦[wms][ a.toNat ] [b]))
        (fun _ => 15 * cfg.regularOpCost + K 1)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 80) 80 ∗ S (w ++ [b]) ∗
          n ↦[wms][ a.toNat ] [b])) := by
  iintro ⟨#Hw, #Hi, #C⟩
  ihave #SW := hW (d + 1) s a 1 w [b] (by omega) hs rfl ha (by simpa using hB) $$ C
  have hcw' := hm.funcs cw hcw
  have t31 : types[31]!.params.length = 3 := by rfl
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, HP⟩
  subst hargs
  simp only [SerdeStruct.pieceFn]
  repeat mstep
  mcall SW using [HP]
  · iframe HP
  icases HQ with ⟨%hrs, HQ⟩
  subst hrs
  mcredits R
  iframe Hc HQ
  ipureintro; simp [htype]

/-- What a key writer reads on a sink besides the `Compound`: the quote, the `ESCAPE` piece, the
key's bytes. -/
def keyInS (n : Nat) (lo : Nat) (et : List UInt8) (p : UInt32) (ds : List UInt8) : IProp GF :=
  iprop(n ↦[wms][ 1051817 ] [34] ∗ n ↦[wms][ 1061808 + lo ] et ∗ n ↦[wms][ p.toNat ] ds)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **The key of a struct's later field** (`keyFn cw a ck`, the state `Rest`) on a sink: the comma
`cb` at `a` through `cw`, then the key `"ds"` (`ck = strFn ce`). -/
theorem keyRest_s (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 20 < lim.maxCallDepth) (Cg : Nat) (gt : GlobalType)
    (C : IProp GF) [Persistent C] (ser : UInt32) (S : List UInt8 → IProp GF) (B : Nat) (K : Nat → Nat)
    (hW : WaSpec cfg lim inst mi Cg n g gt C ser S B K) (cw ck ce : Nat) (a : UInt32)
    (hcw : cw < 955) (hck : ck < 955) (hce : ce < 955) (cb : UInt8)
    (s c p k : UInt32) (w ds : List UInt8) (hs : 112 ≤ s.toNat)
    (hc : c.toNat + 8 ≤ 2 ^ 32) (hds : ds.length = k.toNat) (hk0 : 0 < k.toNat) (lo : Nat) (et : List UInt8)
    (hdig : EscZero lo et ds) (hp : p.toNat + k.toNat ≤ 2 ^ 32) (ha : a.toNat + 1 ≤ 2 ^ 32)
    (hB : w.length + 1 + k.toNat + 2 ≤ B) :
    serCode inst mi A ∗ A cw ↪[wf] FuncInst.wasm types[31]! inst f345 ∗
      A ck ↪[wf] FuncInst.wasm types[15]! inst (SerdeStruct.strFn ce) ∗
      A ce ↪[wf] FuncInst.wasm types[35]! inst f367 ∗ C
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi (SerdeStruct.keyFn cw a ck) Cg
        (fun args => iprop(⌜args = [.i32 c, .i32 p, .i32 k]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - 112) 112 ∗ n ↦[i32][ c.toNat ] ser ∗ n ↦[wms][ c.toNat + 4 ] [2] ∗
          n ↦[wms][ a.toNat ] [cb] ∗ keyInS n lo et p ds ∗ S w))
        (fun _ => 120 * cfg.regularOpCost + K 1 + cost344s cfg K k.toNat)
        (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - 112) 112 ∗ n ↦[i32][ c.toNat ] ser ∗ n ↦[wms][ c.toNat + 4 ] [2] ∗
          n ↦[wms][ a.toNat ] [cb] ∗ keyInS n lo et p ds ∗ S (w ++ [cb] ++ ([34] ++ ds ++ [34])))) := by
  iintro ⟨#Hk, #Hcw, #Hck, #Hce, #C⟩
  ihave #SS := strFn_s (GF := GF) cfg lim (d + 1) types[15]! rfl inst mi A n g ta hm (by omega) Cg gt C ser S B
    K hW ce hce s p k (w ++ [cb]) ds hs hds hk0 lo et hdig hp (by simp; omega) $$ [Hk Hce C]
  · iframe Hk Hce C
  ihave #SW := hW (d + 1) s a 1 w [cb] (by omega) (by omega) rfl ha (by simp; omega) $$ C
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold serCode, escCode, VecAppend.appCode at Hk; icases Hk with ⟨⟨⟨-, -, -, -, -, -, #Hi⟩, -⟩, -⟩; iexact Hi
  have hn := hm.mem
  have hack := hm.funcs ck hck
  have hacw := hm.funcs cw hcw
  have t15 : types[15]!.params.length = 3 := by rfl
  have t31 : types[31]!.params.length = 3 := by rfl
  have hlt := s.toNat_lt
  generalize cost344s cfg K k.toNat = X
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, Hcs, Hst, Hcb, HK, HS⟩
  subst hargs
  iunfold keyInS at HK
  icases HK with ⟨Hq, He, Hds⟩
  icases stkSp 32 80 rfl $$ Hs with ⟨Hs32, Hs80⟩
  ihave Hs80 := stk_addr (show s.toNat - 112 + 32 = s.toNat - 80 by omega) $$ Hs80
  simp only [SerdeStruct.keyFn]
  repeat mstep
  mstep [Hst]
  repeat mstep
  mstep [Hcs]
  repeat mstep
  mcall SW using [Hg Hs80 HS Hcb]
  · iframe Hg Hs80 HS Hcb
  icases HQ with ⟨%hrs, Hg, Hs80, HS, Hcb⟩
  subst hrs
  repeat mstep
  mstep [Hst]
  repeat mstep
  mstep [Hcs]
  repeat mstep
  ihave Hs80 := stk_addr (show s.toNat - 80 = s.toNat - 112 + 32 by omega) $$ Hs80
  ihave Hs := stkJ (a := s.toNat - 112) (b := s.toNat - 112 + 32) (k1 := 32) (k2 := 80) (k := 112) rfl rfl
    $$ [Hs32 Hs80]
  · iframe Hs32 Hs80
  have hloc : actSize ((SerdeStruct.strFn ce).locals.map ValType.default) = 0 := rfl
  mcall SS using [Hg Hs Hq He HS Hds]
    with (mstep_norm_full; simp only [hloc, Nat.reduceAdd, Nat.reduceDiv] at *; omega)
  · iframe Hg Hs Hq He HS Hds
  icases HQ with ⟨%hrs, Hg, Hs, Hq, He, HS, Hds⟩
  subst hrs
  repeat mstep
  mstep_post
  simp only [hloc, Nat.reduceAdd, Nat.reduceDiv, show storeBytes (Value.i32 2) 1 = ([2] : List UInt8) from rfl]
  mcredits R
  iframe Hc Hg Hs Hcs Hst Hcb HS
  isplitr
  · ipureintro; simp [htype]
  iunfold keyInS
  iframe Hq He Hds

/-- The cost of the `u8` field (105) on a sink. -/
def cost105s (cfg : WasmConfig) (K : Nat → Nat) (k : Nat) : Nat :=
  360 * cfg.regularOpCost + K 1 + K 1 + K 2 + cost344s cfg K k

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **A struct's later field, a two-digit `u8`** (105, the state `Rest`) on a sink: `,` (at
1048759), the key `"ds"`, `:` (at 1048760), the value's digits (160, in 105's frame). -/
theorem f105_s (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 22 < lim.maxCallDepth) (Cg : Nat) (gt : GlobalType)
    (C : IProp GF) [Persistent C] (ser : UInt32) (S : List UInt8 → IProp GF) (B : Nat) (K : Nat → Nat)
    (hW : WaSpec cfg lim inst mi Cg n g gt C ser S B K)
    (s c p k v : UInt32) (x : UInt8) (w ds et : List UInt8) (lo : Nat) (hs : 160 ≤ s.toNat)
    (hc : c.toNat + 8 ≤ 2 ^ 32) (hv : v.toNat + 1 ≤ 2 ^ 32) (hx1 : 10 ≤ x.toNat) (hx2 : x.toNat < 100)
    (hds : ds.length = k.toNat) (hk0 : 0 < k.toNat) (hkey : EscZero lo et ds) (hp : p.toNat + k.toNat ≤ 2 ^ 32)
    (hB : w.length + 1 + (k.toNat + 2) + 1 + 2 ≤ B) :
    MetadataFields.mfCode inst mi A ∗ C
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f105 Cg
        (fun args => iprop(⌜args = [.i32 c, .i32 p, .i32 k, .i32 v]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - 160) 160 ∗ n ↦[i32][ c.toNat ] ser ∗ n ↦[wms][ c.toNat + 4 ] [2] ∗
          n ↦[wms][ 1048759 ] [44] ∗ n ↦[wms][ 1048760 ] [58] ∗ n ↦[wms][ 1049500 ] FmtDigits.lut ∗
          keyInS n lo et p ds ∗ S w ∗ n ↦[wms][ v.toNat ] [x]))
        (fun _ => cost105s cfg K k.toNat)
        (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - 160) 160 ∗ n ↦[i32][ c.toNat ] ser ∗ n ↦[wms][ c.toNat + 4 ] [2] ∗
          n ↦[wms][ 1048759 ] [44] ∗ n ↦[wms][ 1048760 ] [58] ∗ n ↦[wms][ 1049500 ] FmtDigits.lut ∗
          keyInS n lo et p ds ∗
          S (w ++ [44] ++ ([34] ++ ds ++ [34]) ++ [58] ++ FmtDigits.padDigits 2 x.toNat) ∗
          n ↦[wms][ v.toNat ] [x])) := by
  iintro ⟨#Hk, #C⟩
  iunfold MetadataFields.mfCode at Hk
  icases Hk with ⟨#Hsc, -, -, #H173, #H176, #H159, -, -, #H99, #H98, -, -, -, #H160⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold serCode, escCode, VecAppend.appCode at Hsc; icases Hsc with ⟨⟨⟨-, -, -, -, -, -, #Hi⟩, -⟩, -⟩; iexact Hi
  have hlt := s.toNat_lt
  have e48 : (s - 48).toNat = s.toNat - 48 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have S173 := keyRest_s (GF := GF) cfg lim (d + 1) types[15]! rfl inst mi A n g ta hm (by omega) Cg gt C ser S B K
    hW 98 176 159 1048759 (by decide) (by decide) (by decide) 44 (s - 48) c p k w ds (by omega) hc hds hk0 lo et
    hkey hp (by decide) (by omega)
  rw [← SerdeStruct.f173_eq, ← SerdeStruct.f176_eq, ← SerdeStruct.f98_eq, ← SerdeStruct.f159_eq] at S173
  ihave #S173 := S173 $$ [Hsc H98 H176 H159 C]
  · iframe Hsc H98 H176 H159 C
  have S99 := piece_s (GF := GF) cfg lim (d + 1) types[0]! rfl inst mi A n g ta hm (by omega) Cg gt C ser S B K hW
    98 (by decide) 1048760 (s - 48) (w ++ [44] ++ ([34] ++ ds ++ [34])) 58 (by omega) (by decide) (by simp; omega)
  rw [← SerdeStruct.f99_eq, ← SerdeStruct.f98_eq] at S99
  ihave #S99 := S99 $$ [H98 Hi C]
  · iframe H98 Hi C
  have hn := hm.mem
  have hg := hm.glob
  have ha173 := hm.funcs 173 (by decide)
  have ha99 := hm.funcs 99 (by decide)
  have ha160 := hm.funcs 160 (by decide)
  have ha98 := hm.funcs 98 (by decide)
  have t15 : types[15]!.params.length = 3 := by rfl
  have t31 : types[31]!.params.length = 3 := by rfl
  have t0 : types[0]!.params.length = 1 := by rfl
  have hxv : (UInt32.ofNat x.toNat).toNat = x.toNat := by
    have := x.toNat_lt; simp only [UInt32.toNat_ofNat']; omega
  unfold cost105s
  generalize cost344s cfg K k.toNat = X
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, Hcs, Hst, Hcom, Hcol, Hlut, HK, HS, Hv⟩
  subst hargs
  icases stkSp 112 48 rfl $$ Hs with ⟨Lo, Fr⟩
  ihave Lo := stk_addr (show s.toNat - 160 = (s - 48).toNat - 112 by omega) $$ Lo
  icases stkSp 8 40 rfl $$ Fr with ⟨O, Fr⟩
  icases stkSp 1 39 rfl $$ Fr with ⟨G1, Fr⟩
  icases stkSp 2 37 rfl $$ Fr with ⟨D, G2⟩
  iunfold stk at O D
  icases O with ⟨%ob, %hob, O⟩
  icases D with ⟨%db, %hdb, D⟩
  ihave O := memBytes_addr (show s.toNat - 160 + 112 = (s - 48).toNat by omega) $$ O
  ihave D := memBytes_addr (show s.toNat - 160 + 112 + 8 + 1 = (s - 48 + 8).toNat + 1 by
    simp [UInt32.toNat_add, e48]; omega) $$ D
  simp only [f105]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  repeat mstep
  -- the key
  mcall S173 using [Hg Lo Hcs Hst Hcom HK HS]
  · iframe Hg Lo Hcs Hst Hcom HK HS
  icases HQ with ⟨%hrs, Hg, Lo, Hcs, Hst, Hcom, HK, HS⟩
  subst hrs
  mcredits (200 * cfg.regularOpCost + K 1 + K 2 + R)
  repeat mstep
  mstep [Hcs]
  repeat mstep
  -- `:`
  icases stkSp 32 80 rfl $$ Lo with ⟨Lo32, Lo80⟩
  ihave Lo80 := stk_addr (show (s - 48).toNat - 112 + 32 = (s - 48).toNat - 80 by omega) $$ Lo80
  mcall S99 using [Hg Lo80 HS Hcol]
  · iframe Hg Lo80 HS Hcol
  icases HQ with ⟨%hrs, Hg, Lo80, HS, Hcol⟩
  subst hrs
  repeat mstep
  mstep [Hcs]
  repeat mstep
  -- the digits (160)
  mstep [Hv]
  have hld : loadValue NumType.i32 (some { bits := 8, signed := false }) (Memory.decodeLE [x]) =
      Value.i32 (UInt32.ofNat x.toNat) := by
    simp [loadValue, Memory.decodeLE]
  rw [hld]
  have hpd : (FmtDigits.padDigits 2 x.toNat).length = 2 := by simp [FmtDigits.padDigits]
  have S160 := MetadataFields.f160_two (GF := GF) cfg lim (d + 1) types[31]! rfl inst mi n hn Cg (s - 48) (s - 48 + 8)
    (UInt32.ofNat x.toNat) ob db hob hdb (by omega) (by omega) (by omega) (by simp [UInt32.toNat_add, e48]; omega)
  rw [hxv] at S160
  mcall S160 using [O D Hlut]
  · iframe O D Hlut
  icases HQ with ⟨%hrs, O0, O4, D, Hlut⟩
  subst hrs
  have hb1 : (s - 48 + 8 + 1).toNat = (s - 48 + 8).toNat + 1 := by simp [UInt32.toNat_add, e48]; omega
  have e40 : (s - 48 + 8).toNat = s.toNat - 40 := by simp [UInt32.toNat_add, e48]; omega
  ihave D := memBytes_addr (show (s - 48 + 8).toNat + 1 = (s - 48 + 8 + 1).toNat by omega) $$ D
  ihave Lo80 := stk_addr (show (s - 48).toNat - 80 = (s - 48).toNat - 80 by rfl) $$ Lo80
  have SW := hW (d + 1) (s - 48) (s - 48 + 8 + 1) 2 (w ++ [44] ++ ([34] ++ ds ++ [34]) ++ [58])
    (FmtDigits.padDigits 2 x.toNat) (by omega) (by omega) hpd (by simp [UInt32.toNat_add, e48]; omega)
    (by simp; omega)
  rw [← SerdeStruct.f98_eq] at SW
  ihave #SW := SW $$ C
  repeat mstep
  mstep [O0]
  repeat mstep
  mstep [O4]
  repeat mstep
  mcall SW using [Hg Lo80 HS D]
  · iframe Hg Lo80 HS D
    ipureintro; rfl
  icases HQ with ⟨%hrs, Hg, Lo80, HS, D⟩
  subst hrs
  repeat mstep
  mstep [Hg]
  rw [show s - 48 + 48 = s by simp]
  repeat mstep
  mcredits R
  iframe Hc Hg Hcs Hst Hcom Hcol Hlut HK Hv
  isplitr
  · ipureintro; simp [htype]
  isplitl [Lo32 Lo80 O0 O4 G1 D G2]
  · ihave Lo := stkJ (a := (s - 48).toNat - 112) (b := (s - 48).toNat - 80) (k1 := 32) (k2 := 80) (k := 112)
      (by omega) rfl $$ [Lo32 Lo80]
    · iframe Lo32 Lo80
    ihave O0 := stk_word n _ _ $$ O0
    ihave O4 := stk_word n _ _ $$ O4
    ihave O := stkJ (a := (s - 48).toNat) (b := (s - 48).toNat + 4) (k1 := 4) (k2 := 4) (k := 8) rfl rfl $$ [O0 O4]
    · iframe O0 O4
    ihave D := (show (n ↦[wms][ (s - 48 + 8 + 1).toNat ] FmtDigits.padDigits 2 x.toNat : IProp GF) ⊢
      stk n (s.toNat - 160 + 112 + 8 + 1) 2 by
        iintro H; iunfold stk; iexists FmtDigits.padDigits 2 x.toNat; iframe %hpd
        iapply memBytes_addr (by omega) $$ H) $$ D
    ihave F := stkJ (a := s.toNat - 160 + 112 + 8 + 1) (b := s.toNat - 160 + 112 + 8 + 1 + 2) (k1 := 2) (k2 := 37)
      (k := 39) rfl rfl $$ [D G2]
    · iframe D G2
    ihave F := stkJ (a := s.toNat - 160 + 112 + 8) (b := s.toNat - 160 + 112 + 8 + 1) (k1 := 1) (k2 := 39)
      (k := 40) rfl rfl $$ [G1 F]
    · iframe G1 F
    ihave F := stkJ (a := (s - 48).toNat) (b := s.toNat - 160 + 112 + 8) (k1 := 8) (k2 := 40)
      (k := 48) (by omega) rfl $$ [O F]
    · iframe O F
    iapply stkJ (a := s.toNat - 160) (b := (s - 48).toNat) (k1 := 112) (k2 := 48) (k := 160) (by omega) rfl
    iframe F
    iapply stk_addr (show (s - 48).toNat - 112 = s.toNat - 160 by omega) $$ Lo
  simp only [List.append_assoc, List.cons_append, List.nil_append] at *
  iexact HS

end Sink

end WNear.Binary.SerdeSink
