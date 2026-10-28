import Bridge.Functions.ReadRegister
import Bridge.Functions.VecFromElemF

/-!
# `env::read_register` (523) on `heapInv … F`, any `F ≥ 1`

`ReadRegister.f523_spec` on any free-list bound `F ≥ 1` (`okG F`), with
`VecFromElemF.f687_specZ` (the zeroed `vec![0; len]` on `heapInv … F`) in place of
`VecFromElem.f687_spec`. The register's bytes land in a fresh block; the bound is kept
(`optVecAtF`). The cost is `cost523F cfg F h r`: `ReadRegister.cost523` with
`VecFromElemF.cost687Z cfg F len` for the allocation (`cost523F_one`: at `F = 1` it is `cost523`).

The code is `rrCodeF`: `rrCode` and the merge 575.
-/

namespace WNear.Binary.ReadRegisterF

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary.Interface WNear.Binary.RegisterLen WNear.Binary.ValueReturn
open WNear.Binary.ReadRegister
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_word stk_addr vecCode roomFor grownLen cost687)
open WNear.Binary.VecFromElemF (vecCodeF vecAfterF cost687Z cost687Z_one pre687F post687F f687_specZ)
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.AllocInv (heapInv)
open WNear.Binary.VecWithCap (okG)

section Spec

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- `rrCode` and the merge 575 (persistent). -/
def rrCodeF (e inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n maxP : Nat) (mx : Option Nat) : IProp GF :=
  iprop(rrCode e inst mi A n maxP mx ∗ A 575 ↪[wf] FuncInst.wasm types[0]! inst f575)

instance (e inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n maxP : Nat) (mx : Option Nat) :
    Persistent (rrCodeF (GF := GF) e inst mi A n maxP mx) := by
  unfold rrCodeF; infer_instance

theorem vecAfterF_pos {n maxP len : Nat} {live : List (Nat × Nat)} {F : Nat} {c p : UInt32} {b : UInt8}
    (hc : 0 < c.toNat) :
    vecAfterF (GF := GF) n maxP len live F c p b ⊢
      ∃ len', ⌜p ≠ 0 ∧ (len' = len ∨ len' = grownLen len c)⌝ ∗
        heapInv n maxP len' ((p.toNat, c.toNat) :: live) F ∗ n ↦[wms][ p.toNat ] List.replicate c.toNat b := by
  iintro H
  iunfold vecAfterF at H
  icases H with ⟨%len', %h, H1, H2⟩
  have hc0 : c.toNat ≠ 0 := by omega
  simp only [hc0, ite_false]
  iexists len'
  iframe H1 H2
  ipureintro
  rcases h with ⟨h0, -, -⟩ | ⟨-, hp, hl⟩
  · omega
  · exact ⟨hp, hl⟩

/-- `ReadRegister.optVecAt` on `heapInv … F`. -/
def optVecAtF (n maxP len : Nat) (live : List (Nat × Nat)) (F : Nat) (out : UInt32) :
    Option (List UInt8) → IProp GF
  | none => iprop(n ↦[i32][ out.toNat ] 0 ∗ (∃ bs : List UInt8, ⌜bs.length = 8⌝ ∗ n ↦[wms][ out.toNat + 4 ] bs) ∗
      heapInv n maxP len live F)
  | some data => iprop(∃ p : UInt32, n ↦[i32][ out.toNat ] p ∗
      n ↦[i32][ out.toNat + 4 ] UInt32.ofNat data.length ∗ n ↦[i32][ out.toNat + 8 ] UInt32.ofNat data.length ∗
      ∃ len', ⌜p ≠ 0 ∧ (len' = len ∨ len' = grownLen len (UInt32.ofNat data.length))⌝ ∗
        heapInv n maxP len' ((p.toNat, data.length) :: live) F ∗ n ↦[wms][ p.toNat ] data)

/-- The cost of `read_register` past `register_len`, on `heapInv … F`. -/
def costRestF (cfg : WasmConfig) (F : Nat) (h : NearState) : Option (List UInt8) → Nat
    | none => 50 * cfg.regularOpCost
    | some data => 95 * cfg.regularOpCost + cost687Z cfg F (UInt32.ofNat data.length) +
        (237 * cfg.regularOpCost + readRegisterUse h data.length)

/-- The cost of `read_register` on `heapInv … F`. -/
def cost523F (cfg : WasmConfig) (F : Nat) (h : NearState) (r : UInt64) : Nat :=
  281 * cfg.regularOpCost + registerLenUse h + costRestF cfg F h (h.registers r.toNat)

theorem costRestF_ge (cfg : WasmConfig) (F : Nat) (h : NearState) (v : Option (List UInt8)) :
    40 * cfg.regularOpCost ≤ costRestF cfg F h v := by
  cases v <;> simp only [costRestF] <;> omega

theorem cost523F_one (cfg : WasmConfig) (h : NearState) (r : UInt64) :
    cost523F cfg 1 h r = cost523 cfg h r := by
  unfold cost523F cost523
  rcases h.registers r.toNat with _ | data
  · rfl
  · simp only [costRestF, costRest, cost687Z_one cfg 0 _ (by decide)]

def pre523F (n g ta : Nat) (A : Nat → Nat) (gt : GlobalType) (s out : UInt32) (r : UInt64) (idx : UInt32)
    (maxP len : Nat) (live : List (Nat × Nat)) (F : Nat) (ob : List UInt8) (h : NearState) (args : List Value) :
    IProp GF :=
  iprop(⌜args = [.i32 out, .i64 r]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ ifaceR n ta A ∗ stk n (s.toNat - 160) 160 ∗
    vt n 1057464 idx ta (A 578) ∗ heapInv n maxP len live F ∗ n ↦[wms][ out.toNat ] ob ∗ mhostPt h)

def post523F (n g ta : Nat) (A : Nat → Nat) (gt : GlobalType) (s out : UInt32) (r : UInt64) (idx : UInt32)
    (maxP len : Nat) (live : List (Nat × Nat)) (F : Nat) (h : NearState) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ ifaceR n ta A ∗ stk n (s.toNat - 160) 160 ∗
    vt n 1057464 idx ta (A 578) ∗ optVecAtF n maxP len live F out (h.registers r.toNat) ∗ mhostPt h)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **`env::read_register(id)`** (523) on `heapInv … F`, `okG F`: `None` if the register is unset,
else `Some(vec)` with the register's bytes in a fresh heap block, the bound `F` kept
(`optVecAtF`), at `cost523F cfg F h r`. -/
theorem f523_specF (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (e : Nat) (A : Nat → Nat)
    (n g ta : Nat) (mx : Option Nat) (hm : IfaceMod mi A n g ta) (hd : d + 13 < lim.maxCallDepth)
    (Cg : Nat) (gt : GlobalType) (s out : UInt32) (hs : 160 ≤ s.toNat) (hal : s.toNat % 8 = 0)
    (hout : out.toNat + 12 ≤ 2 ^ 32) (r : UInt64) (idx : UInt32) (maxP len : Nat)
    (live : List (Nat × Nat)) (F : Nat) (hF : okG F) (ob : List UInt8) (hob : ob.length = 12) (h : NearState)
    (hok : RegOk maxP len (h.registers r.toNat)) :
    rrCodeF e inst mi A n maxP mx
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f523 Cg
        (pre523F n g ta A gt s out r idx maxP len live F ob h)
        (fun _ => cost523F cfg F h r)
        (post523F n g ta A gt s out r idx maxP len live F h) := by
  iintro #HrrF
  iunfold rrCodeF at HrrF
  icases HrrF with ⟨#Hrr, #H575⟩
  iunfold rrCode at Hrr
  icases Hrr with ⟨#HcR, #Hv, #F524, #F440, #F435, #F761⟩
  ihave #HvF : vecCodeF (GF := GF) n maxP inst mi A $$ []
  · iunfold vecCodeF
    isplitr
    · iexact Hv
    · iexact H575
  ihave #Hcode : ifaceCode e inst mi A n mx $$ []
  · iunfold ifaceCodeR at HcR
    icases HcR with ⟨#H, -⟩
    iexact H
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold ifaceCode at Hcode
    icases Hcode with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩
    iexact Hi
  ihave #F687 : A 687 ↪[wf] FuncInst.wasm types[31]! inst f687 $$ []
  · iunfold vecCode at Hv
    icases Hv with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, #H⟩
    iexact H
  have hn := hm.mem
  have hg := hm.glob
  have ha524 := hm.funcs 524 (by decide)
  have ha687 := hm.funcs 687 (by decide)
  have ha435 := hm.funcs 435 (by decide)
  have ha761 := hm.funcs 761 (by decide)
  have t5 : types[5]!.params.length = 2 := by rfl
  have t31 : types[31]!.params.length = 3 := by rfl
  have t21 : types[21]!.params.length = 0 := by rfl
  have hlt := s.toNat_lt
  have h48 : (s - 48).toNat = s.toNat - 48 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have e8 : (s - 48 + 8).toNat = s.toNat - 40 := by simp [UInt32.toNat_add, h48]; omega
  have e24 : (s - 48 + 24).toNat = s.toNat - 24 := by simp [UInt32.toNat_add, h48]; omega
  have e32 : (s - 48 + 32).toNat = s.toNat - 16 := by simp [UInt32.toNat_add, h48]; omega
  have e64 : (s - 48 - 16).toNat = s.toNat - 64 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le, h48] <;> omega
  have e80 : (s - 48 - 16 - 16).toNat = s.toNat - 80 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le, e64] <;> omega
  have hob0 : (ob.take 4).length = 4 := by simp; omega
  have hob4 : (ob.drop 4).length = 8 := by simp; omega
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold pre523F at HP
  icases HP with ⟨%hargs, Hg, HI, Hs, Hvt, Hinv, Ho, Hhost⟩
  subst hargs
  ihave HI := iface_of_ifaceR n ta A $$ HI
  icases HI with ⟨HI, HS12⟩
  -- the stack: P (80) Q1 (16) Q2 (8) Q3 (8) Q4 (8) T (8) V (8) I (8) W (16)
  icases stk_split n (s.toNat - 160) 80 80 $$ Hs with ⟨P, Hs⟩
  icases stk_split n (s.toNat - 160 + 80) 16 64 $$ Hs with ⟨Q1, Hs⟩
  icases stk_split n (s.toNat - 160 + 80 + 16) 8 56 $$ Hs with ⟨Q2, Hs⟩
  icases stk_split n (s.toNat - 160 + 80 + 16 + 8) 8 48 $$ Hs with ⟨Q3, Hs⟩
  icases stk_split n (s.toNat - 160 + 80 + 16 + 8 + 8) 8 40 $$ Hs with ⟨Q4, Hs⟩
  icases stk_split n (s.toNat - 160 + 80 + 16 + 8 + 8 + 8) 8 32 $$ Hs with ⟨T, Hs⟩
  icases stk_split n (s.toNat - 160 + 80 + 16 + 8 + 8 + 8 + 8) 8 24 $$ Hs with ⟨V, Hs⟩
  icases stk_split n (s.toNat - 160 + 80 + 16 + 8 + 8 + 8 + 8 + 8) 8 16 $$ Hs with ⟨I, W⟩
  rw [show s.toNat - 160 + 80 = s.toNat - 80 by omega] at *
  rw [show s.toNat - 80 + 16 = s.toNat - 64 by omega, show s.toNat - 64 + 8 = s.toNat - 56 by omega,
    show s.toNat - 56 + 8 = s.toNat - 48 by omega, show s.toNat - 48 + 8 = s.toNat - 40 by omega,
    show s.toNat - 40 + 8 = s.toNat - 32 by omega, show s.toNat - 32 + 8 = s.toNat - 24 by omega,
    show s.toNat - 24 + 8 = s.toNat - 16 by omega]
  iunfold stk at Q3 T V I
  icases Q3 with ⟨%q3, %hq3, Q3⟩
  icases T with ⟨%tb, %htb, T⟩
  icases V with ⟨%vb, %hvb, V⟩
  icases I with ⟨%ib, %hib, I⟩
  icases stk_frame4 n (s.toNat - 80) (s - 48 - 16 - 16) e80 $$ Q1 with ⟨%w0, %w4, %w8, %w12, Q1⟩
  simp only [f523, cost523F]
  have hge := costRestF_ge cfg F h (h.registers r.toNat)
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep; mstep [I]
  mstep; mstep; mstep; mstep
  mcall (f524_spec cfg lim (d + 1) types[5]! (by rfl) inst mi e A n g ta mx hm (by omega) Cg
      ⟨gt, .i32 (s - 48)⟩ (s - 48) rfl (by omega) (by omega) (s - 48 + 8) r q3 tb vb hq3 htb hvb
      w0 w4 w8 w12 h) using [Hg HI Q3 Q1 T V Hhost]
  · iunfold RegisterLen.pre
    ihave Q3 := memBytes_addr (show s.toNat - 56 = (s - 48 - 16).toNat + 8 by omega) $$ Q3
    ihave T := memBytes_addr (show s.toNat - 40 = (s - 48 + 8).toNat by omega) $$ T
    ihave V := memBytes_addr (show s.toNat - 32 = (s - 48 + 8).toNat + 8 by omega) $$ V
    iframe Hg HI Q3 Q1 T V Hhost
    ipureintro; rfl
  iunfold RegisterLen.post at HQ
  icases HQ with ⟨%hrs, Hg, HI, Q3, Q1, T, V, Hhost⟩
  subst hrs
  rw [e8, show (s - 48 - 16).toNat + 8 = s.toNat - 56 by omega]
  have ho4 : (ob.take 4).length = 4 := by simp; omega
  rcases hrc : h.registers r.toNat with _ | data
  · ---------------------------------------------------------------- None
    try rw [hrc]
    simp only [costRestF]
    rw [lenU64_none hrc, show optTag u64Max = 0 by decide]
    mcredits (27 * cfg.regularOpCost + R)
    ihave Ho := U128From.memBytes_split n out.toNat 4 ob (by omega) $$ Ho
    icases Ho with ⟨Ho0, Ho4⟩
    mstep; mstep; mstep; mstep [T]
    simp only [decodeLE_storeBytes_i64, UInt64.ofNat_toNat]
    mstep; mstep; mstep
    mcall (f761_spec cfg lim (d + 1) types[21]! (by rfl) inst mi Cg) using []
    · ipureintro; simp
    icases HQ with %hrs
    subst hrs
    mstep; mstep; mstep [Ho0]
    mstep; mstep; mstep; mstep [Hg]
    rw [show s - 48 + 48 = s by simp]
    mcredits R
    iframe Hc
    iunfold post523F
    try rw [hrc]
    simp only [optVecAtF]
    isplitr
    · ipureintro; simp [htype]
    iframe Hg Hvt Hhost Ho0 Hinv
    isplitl [HI HS12]
    · iunfold ifaceR; iframe HI HS12
    isplitr [Ho4]
    · iapply stk160_join n s.toNat hs
      ihave Q1 := frame4_stk n (s.toNat - 80) _ e80 _ _ _ _ $$ Q1
      ihave Q3 := stk_bytes n _ _ 8 (by simp) $$ Q3
      ihave T := stk_bytes n _ _ 8 (by simp) $$ T
      ihave V := stk_bytes n _ _ 8 (by simp) $$ V
      ihave I := stk_bytes n _ _ 8 (by simp) $$ I
      rw [show s.toNat - 40 + 8 = s.toNat - 32 by omega]
      iframe P Q1 Q2 Q3 Q4 T V I W
    iexists ob.drop 4; iframe Ho4; ipureintro; simp; omega
  · ---------------------------------------------------------------- Some
    try rw [hrc] at hok
    obtain ⟨hdpos, hd28, hroom⟩ := hok
    try rw [hrc]
    simp only [costRestF]
    have hcN : (UInt32.ofNat data.length).toNat = data.length := by simp; omega
    rw [lenU64_some hrc, tag_some data.length (by omega)]
    mcredits (65 * cfg.regularOpCost + cost687Z cfg F (UInt32.ofNat data.length) +
      (237 * cfg.regularOpCost + readRegisterUse h data.length) + R)
    mstep; mstep; mstep; mstep [T]
    simp only [decodeLE_storeBytes_i64, UInt64.ofNat_toNat]
    mstep; mstep; mstep
    mstep; mstep; mstep; mstep; mstep; mstep [V]
    simp only [decodeLE_storeBytes_i64, UInt64.ofNat_toNat]
    mstep
    rw [wrap_ofNat]
    icases stk_split n (s.toNat - 16) 12 4 $$ W with ⟨W, W12⟩
    iunfold stk at W
    icases W with ⟨%wb, %hwb, W⟩
    mcall (f687_specZ cfg lim (d + 1) types[31]! (by rfl) inst mi A n g ta hm (by omega) Cg gt (s - 48)
        (s - 48 + 32) 0 (UInt32.ofNat data.length) (by decide) idx maxP len live F hF wb hwb (by omega)
        (by omega) (fun _ => hroom) (by omega)) using [Hg P Q1 Q2 Q3 Hvt Hinv W]
    · iunfold pre687F
      ihave Q1 := frame4_stk n (s.toNat - 80) _ e80 _ _ _ _ $$ Q1
      ihave Q3 := stk_bytes n _ _ 8 (by simp) $$ Q3
      ihave P := stk112_join' n s.toNat hs $$ [P Q1 Q2 Q3]
      · iframe P Q1 Q2 Q3
      ihave P := stk_addr (show s.toNat - 160 = (s - 48).toNat - 112 by omega) $$ P
      ihave W := memBytes_addr (show s.toNat - 16 = (s - 48 + 32).toNat by omega) $$ W
      iframe Hg P Hvt Hinv W
      ipureintro; rfl
    iunfold post687F at HQ
    icases HQ with ⟨%hrs, %p, Hg, P, Hvt, W0, W4, W8, HA⟩
    subst hrs
    ihave HA := vecAfterF_pos (by omega) $$ HA
    icases HA with ⟨%len', %⟨hp0, hl'⟩, Hinv, Hb⟩
    ihave P := stk_addr (show (s - 48).toNat - 112 = s.toNat - 160 by omega) $$ P
    icases stk_split n (s.toNat - 160) 96 16 $$ P with ⟨P, PQ⟩
    icases stk_frame4 n (s.toNat - 160 + 96) (s - 48 - 16) (by omega) $$ PQ with ⟨%v0, %v4, %v8, %v12, PQ⟩
    mcredits (40 * cfg.regularOpCost + (237 * cfg.regularOpCost + readRegisterUse h data.length) + R)
    mstep; mstep; mstep; mstep; mstep; mstep; mstep
    mcall (f435_spec cfg lim (d + 1) types[31]! (by rfl) inst mi e A n g ta mx hm (by omega) Cg
        ⟨gt, .i32 (s - 48)⟩ (s - 48) rfl (by omega) (by omega) h (s - 48 + 24) (s - 48 + 32) p r
        (List.replicate (UInt32.ofNat data.length).toNat 0) data hrc (by simp; omega) hdpos v0 v4 v8 v12)
      using [Hg HI HS12 I W0 PQ Hb Hhost]
    · iunfold ReadRegister.withPre
      iunfold ifaceR
      ihave I := memBytes_addr (show s.toNat - 24 = (s - 48 + 24).toNat by omega) $$ I
      iframe Hg HI HS12 I W0 PQ Hb Hhost
      ipureintro; rfl
    iunfold ReadRegister.withPost at HQ
    icases HQ with ⟨%hrs, Hg, HI, I, W0, PQ, Hb, Hhost⟩
    subst hrs
    mcredits (19 * cfg.regularOpCost + R)
    ihave Ho := U128From.memBytes_split n out.toNat 8 ob (by omega) $$ Ho
    icases Ho with ⟨Ho0, Ho8⟩
    have ho8 : (ob.take 8).length = 8 := by simp; omega
    have ho8' : (ob.drop 8).length = 4 := by simp; omega
    mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep [W8]; mstep [Ho8]
    ihave W := KeyGet.join64 n (s - 48 + 32).toNat p (UInt32.ofNat data.length) $$ [W0 W4]
    · iframe W0 W4
    mstep; mstep; mstep [W]
    rw [VecFromElem.ofNat_decode_pair]
    mstep [Ho0]
    rw [VecFromElem.storeBytes_pair64]
    mstep
    mstep; mstep; mstep; mstep [Hg]
    rw [show s - 48 + 48 = s by simp]
    mcredits R
    iframe Hc
    iunfold post523F
    try rw [hrc]
    simp only [optVecAtF]
    isplitr
    · ipureintro; simp [htype]
    iframe Hg Hvt Hhost
    isplitl [HI]
    · iexact HI
    isplitr [Ho0 Ho8 Hinv Hb]
    · iapply stk160_join n s.toNat hs
      ihave PQ := frame4_stk n (s.toNat - 64) _ (by omega) _ _ _ _ $$ PQ
      icases stk_split n (s.toNat - 64) 8 8 $$ PQ with ⟨Q2, Q3⟩
      icases stk_split n (s.toNat - 160) 80 16 $$ P with ⟨P, Q1⟩
      ihave T := stk_bytes n _ _ 8 (by simp) $$ T
      ihave V := stk_bytes n _ _ 8 (by simp) $$ V
      ihave I := stk_bytes n _ _ 8 (by simp) $$ I
      ihave W := KeyGet.split64 n _ p _ $$ W
      icases W with ⟨W0, W4⟩
      ihave W0 := stk_word n _ p $$ W0
      ihave W4 := stk_word n _ _ $$ W4
      ihave W8 := stk_word n _ _ $$ W8
      ihave W := stk_join n _ 4 4 $$ [W0 W4]
      · iframe W0 W4
      ihave W := stk_join n _ 8 4 $$ [W W8]
      · iframe W W8
      ihave W := stk_join n _ 12 4 $$ [W W12]
      · rw [e32]; iframe W W12
      rw [show s.toNat - 160 + 80 = s.toNat - 80 by omega, show s.toNat - 64 + 8 = s.toNat - 56 by omega,
        show s.toNat - 40 + 8 = s.toNat - 32 by omega, e24]
      iframe P Q1 Q2 Q3 Q4 T V I
      iexact W
    iexists p
    ihave Ho0 := KeyGet.split64 n out.toNat p _ $$ Ho0
    icases Ho0 with ⟨Ho0, Ho4⟩
    iframe Ho0 Ho4 Ho8
    iexists len'
    rw [hcN]
    iframe Hinv Hb
    ipureintro; exact ⟨hp0, hl'⟩

end Spec

end WNear.Binary.ReadRegisterF
