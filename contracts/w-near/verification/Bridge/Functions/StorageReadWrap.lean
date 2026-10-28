import Bridge.Functions.ReadRegister
import Bridge.Functions.StorageRead

/-!
# `env::storage_read` (function 548), through the blockchain interface

```wat
;; 548 storage_read(out, key_ptr, key_len) -> Option<Vec<u8>> at out
sp -= 32;  [sp+8] := (key_ptr, key_len)          ;; the slice &[u8]
v := call 459(1055020, sp + 8)                    ;; storage_read(key, register 0) through the interface
v > 1 → panic                                     ;; (unreachable: the host returns 0 or 1)
v = 0: out.ptr := 0                               ;; None
v = 1: read_register(sp + 16, 0)                  ;; 523: Some(vec) (the register was just written)
       Option::expect(out, sp + 16, ..)           ;; 498: out := vec
sp += 32
```

* `f498_spec`: `Option::<Vec<u8>>::expect` on `Some`: the three words copied.
* `f548_spec`: `env::storage_read(key)` for any read contract `hc` of the host whose
  postcondition `Q` writes the value to register 0 and keeps the fee tables (`QOk`);
  `storageReadPost_ok` shows `StorageReadPost` (`storageRead_readContract`) is one. The
  result at `out` is `optVecAt … (h.storage key)` (ReadRegister.lean): `None`, or a fresh
  heap block holding the value. The value must be nonempty and `< 2^28` bytes, with room
  for its allocation (`RegOk`).
-/

namespace WNear.Binary.StorageReadWrap

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary.Interface WNear.Binary.RegisterLen WNear.Binary.ReadRegister
open WNear.Binary.StorageRead (foundU64 storageReadResult_eq f459_spec)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_word stk_addr vecCode roomFor)
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.AllocInv (heapInv)

/-! ## The host's postcondition -/

/-- What `read_register` after `storage_read` needs of the host's postcondition `Q`: the value
(if any) in register 0, the fee tables kept (so the gas of the later calls is `h`'s). -/
def QOk (h : NearState) (key : List UInt8) (Q : NearState → Prop) : Prop :=
  ∀ h', Q h' → (∀ v, h.storage key = some v → h'.registers 0 = some v) ∧
    (∀ cs, chargesUse h' cs = chargesUse h cs)

theorem chargesUse_congr' {a b : NearState} (hf : a.fees = b.fees) (hx : a.extCosts = b.extCosts)
    (cs : List Charge) : chargesUse a cs = chargesUse b cs := by
  unfold chargesUse
  congr 1
  exact List.map_congr_left fun c _ => chargeUse_congr hf hx c

/-- `storage_read`'s postcondition (register 0) is `QOk`. -/
theorem storageReadPost_ok (h : NearState) (key : List UInt8) (s : Near.TrieOverlay.State) :
    QOk h key (StorageReadPost h key 0 s) := by
  rintro h' ⟨s2, -, he⟩
  have hr := erase_field he NearState.registers fun _ => rfl
  have hf := erase_field he NearState.fees fun _ => rfl
  have hx := erase_field he NearState.extCosts fun _ => rfl
  refine ⟨fun v hv => ?_, fun cs => ?_⟩
  · rw [hr]; simp [storageReadRegs, hv, u64Max, NearState.setRegister]
  · rw [chargesUse_congr' hf hx]
    unfold storageReadRegs
    split
    · split <;> rfl
    · rfl

/-! ## `Option::expect` (498) on `Some` -/

section L498

variable {GF : BundledGFunctors} [WasmGS NearState GF]

def pre498 (n : Nat) (out opt p c1 c2 : UInt32) (ob : List UInt8) (args : List Value) : IProp GF :=
  iprop(⌜∃ m l loc : UInt32, args = [.i32 out, .i32 opt, .i32 m, .i32 l, .i32 loc]⌝ ∗
    n ↦[i32][ opt.toNat ] p ∗ n ↦[i32][ opt.toNat + 4 ] c1 ∗ n ↦[i32][ opt.toNat + 8 ] c2 ∗
    n ↦[wms][ out.toNat ] ob)

def post498 (n : Nat) (out opt p c1 c2 : UInt32) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = []⌝ ∗ n ↦[i32][ opt.toNat ] p ∗ n ↦[i32][ opt.toNat + 4 ] c1 ∗
    n ↦[i32][ opt.toNat + 8 ] c2 ∗ n ↦[i32][ out.toNat ] p ∗ n ↦[i32][ out.toNat + 4 ] c1 ∗
    n ↦[i32][ out.toNat + 8 ] c2)

/-- `Option::<Vec<u8>>::expect(msg)` (498) on `Some((p, c1, c2))` (`p ≠ 0`): the `Vec` copied to
`out`. -/
theorem f498_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (n : Nat)
    (hn : mi.memAddrs[0]? = some n) (Cg : Nat) (out opt p c1 c2 : UInt32) (ob : List UInt8)
    (hob : ob.length = 12) (hp : p ≠ 0) (hout : out.toNat + 12 ≤ 2 ^ 32) (hopt : opt.toNat + 12 ≤ 2 ^ 32) :
    ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f498 Cg (pre498 n out opt p c1 c2 ob)
        (fun _ => 16 * cfg.regularOpCost) (post498 n out opt p c1 c2) := by
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold pre498 at HP
  icases HP with ⟨%⟨m, l, loc, hargs⟩, O0, O4, O8, Ho⟩
  subst hargs
  have ho0 : (ob.take 8).length = 8 := by simp; omega
  have ho8 : (ob.drop 8).length = 4 := by simp; omega
  ihave Ho := U128From.memBytes_split n out.toNat 8 ob (by omega) $$ Ho
  icases Ho with ⟨Ho0, Ho8⟩
  simp only [f498]
  mstep; mstep; mstep [O0]; mstep
  ihave O := KeyGet.join64 n opt.toNat p c1 $$ [O0 O4]
  · iframe O0 O4
  mstep; mstep; mstep [O]
  rw [VecFromElem.ofNat_decode_pair]
  mstep [Ho0]
  rw [VecFromElem.storeBytes_pair64]
  mstep; mstep; mstep; mstep; mstep; mstep; mstep [O8]; mstep [Ho8]
  mcredits R
  iframe Hc
  iunfold post498
  ihave O := KeyGet.split64 n opt.toNat p c1 $$ O
  icases O with ⟨O0, O4⟩
  ihave Ho0 := KeyGet.split64 n out.toNat p c1 $$ Ho0
  icases Ho0 with ⟨Ho0, Ho4⟩
  iframe O0 O4 O8 Ho0 Ho4 Ho8
  ipureintro; simp [htype]

end L498

/-! ## `env::storage_read` (548) -/

section Spec

variable {GF : BundledGFunctors} [WasmGS NearState GF]

theorem cost523_eq (cfg : WasmConfig) {h h' : NearState} {val : List UInt8}
    (hr : h'.registers 0 = some val) (hch : ∀ cs, chargesUse h' cs = chargesUse h cs) :
    cost523 cfg h' 0 = 281 * cfg.regularOpCost + registerLenUse h + costRest cfg h (some val) := by
  unfold cost523 costRest registerLenUse readRegisterUse
  rw [show (0 : UInt64).toNat = 0 from rfl, hr]
  simp only [hch]

/-- The cost of `storage_read` past the host call: `None`, or `read_register` and `expect`. -/
def costS (cfg : WasmConfig) (h : NearState) : Option (List UInt8) → Nat
  | none => 20 * cfg.regularOpCost
  | some val => 70 * cfg.regularOpCost + (281 * cfg.regularOpCost + registerLenUse h + costRest cfg h (some val))

theorem costS_ge (cfg : WasmConfig) (h : NearState) (v : Option (List UInt8)) :
    20 * cfg.regularOpCost ≤ costS cfg h v := by
  cases v <;> simp only [costS] <;> omega

/-- The code `storage_read` runs (persistent). -/
def srCode (e inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n maxP : Nat) (mx : Option Nat) : IProp GF :=
  iprop(rrCode e inst mi A n maxP mx ∗ A 459 ↪[wf] FuncInst.wasm types[30]! inst f459 ∗
    A 523 ↪[wf] FuncInst.wasm types[5]! inst f523 ∗ A 498 ↪[wf] FuncInst.wasm types[39]! inst f498)

instance (e inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n maxP : Nat) (mx : Option Nat) :
    Persistent (srCode (GF := GF) e inst mi A n maxP mx) := by
  unfold srCode; infer_instance

def pre548 (n g ta : Nat) (A : Nat → Nat) (gt : GlobalType) (s out kp kl : UInt32) (key : List UInt8)
    (idx : UInt32) (maxP len : Nat) (live : List (Nat × Nat)) (ob : List UInt8) (h : NearState)
    (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 out, .i32 kp, .i32 kl]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ ifaceR n ta A ∗
    stk n (s.toNat - 192) 192 ∗ vt n 1057464 idx ta (A 578) ∗ heapInv n maxP len live 1 ∗
    n ↦[wms][ out.toNat ] ob ∗ n ↦[wms][ kp.toNat ] key ∗ mhostPt h)

def post548 (n g ta : Nat) (A : Nat → Nat) (gt : GlobalType) (s out kp : UInt32) (key : List UInt8)
    (idx : UInt32) (maxP len : Nat) (live : List (Nat × Nat)) (h : NearState) (Q : NearState → Prop)
    (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ ifaceR n ta A ∗ stk n (s.toNat - 192) 192 ∗
    vt n 1057464 idx ta (A 578) ∗ n ↦[wms][ kp.toNat ] key ∗
    optVecAt n maxP len live out (h.storage key) ∗ (∃ h', ⌜Q h'⌝ ∗ mhostPt h'))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **`env::storage_read(key)`** (function 548 of `contract.wasm`) on the installed interface,
for a read contract `hc` of the host (`storageRead_readContract`, with `kh = storageReadUse h key
len`) whose postcondition is `QOk` (`storageReadPost_ok`): `None` at `out` if the key is absent,
else `Some(vec)` with the value in a fresh heap block (`optVecAt`), the host some `h'` with
`Q h'`. -/
theorem f548_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (e : Nat) (A : Nat → Nat)
    (n g ta : Nat) (mx : Option Nat) (hm : IfaceMod mi A n g ta) (hd : d + 14 < lim.maxCallDepth)
    (Cg : Nat) (gt : GlobalType) (s out kp kl : UInt32) (hs : 192 ≤ s.toNat) (hal : s.toNat % 8 = 0)
    (hout : out.toNat + 12 ≤ 2 ^ 32) (key : List UInt8) (idx : UInt32) (maxP len : Nat)
    (live : List (Nat × Nat)) (ob : List UInt8) (hob : ob.length = 12) (h : NearState)
    (Q : NearState → Prop) (kh : Nat)
    (hc : ReadContractP (metered e "storage_read" storageReadFn).toHostFn h Q
      [.i64 (UInt64.ofNat kl.toNat), .i64 (UInt64.ofNat kp.toNat), .i64 0] (storageReadResult (h.storage key))
      kp.toNat key kh Cg)
    (hQ : QOk h key Q) (hok : RegOk maxP len (h.storage key)) :
    srCode e inst mi A n maxP mx
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f548 Cg
        (pre548 n g ta A gt s out kp kl key idx maxP len live ob h)
        (fun _ => 40 * cfg.regularOpCost + (249 * cfg.regularOpCost + kh) + costS cfg h (h.storage key))
        (post548 n g ta A gt s out kp key idx maxP len live h Q) := by
  iintro #Hsr
  iunfold srCode at Hsr
  icases Hsr with ⟨#Hrr, #F459, #F523, #F498⟩
  ihave #HcR : ifaceCodeR e inst mi A n mx $$ []
  · iunfold rrCode at Hrr
    icases Hrr with ⟨#H, -⟩
    iexact H
  ihave #Hcode : ifaceCode e inst mi A n mx $$ []
  · iunfold ifaceCodeR at HcR
    icases HcR with ⟨#H, -⟩
    iexact H
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold ifaceCode at Hcode
    icases Hcode with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩
    iexact Hi
  rw [storageReadResult_eq] at hc
  have hn := hm.mem
  have hg := hm.glob
  have ha459 := hm.funcs 459 (by decide)
  have ha523 := hm.funcs 523 (by decide)
  have ha498 := hm.funcs 498 (by decide)
  have t30 : types[30]!.params.length = 2 := by rfl
  have t5 : types[5]!.params.length = 2 := by rfl
  have t39 : types[39]!.params.length = 5 := by rfl
  have hlt := s.toNat_lt
  have h32 : (s - 32).toNat = s.toNat - 32 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have e8 : (s - 32 + 8).toNat = s.toNat - 24 := by simp [UInt32.toNat_add, h32]; omega
  have e16 : (s - 32 + 16).toNat = s.toNat - 16 := by simp [UInt32.toNat_add, h32]; omega
  have e48 : (s - 32 - 16).toNat = s.toNat - 48 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le, h32] <;> omega
  have hge := costS_ge cfg h (h.storage key)
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold pre548 at HP
  icases HP with ⟨%hargs, Hg, HI, Hs, Hvt, Hinv, Ho, Hk, Hhost⟩
  subst hargs
  ihave HI := iface_of_ifaceR n ta A $$ HI
  icases HI with ⟨HI, HS12⟩
  -- the stack: R (144) F (16) U (8) SL (8) O (16)
  icases stk_split n (s.toNat - 192) 144 48 $$ Hs with ⟨Rg, Hs⟩
  icases stk_split n (s.toNat - 192 + 144) 16 32 $$ Hs with ⟨Fr, Hs⟩
  icases stk_split n (s.toNat - 192 + 144 + 16) 8 24 $$ Hs with ⟨U, Hs⟩
  icases stk_split n (s.toNat - 192 + 144 + 16 + 8) 8 16 $$ Hs with ⟨SL, O⟩
  rw [show s.toNat - 192 + 144 = s.toNat - 48 by omega, show s.toNat - 48 + 16 = s.toNat - 32 by omega,
    show s.toNat - 32 + 8 = s.toNat - 24 by omega, show s.toNat - 24 + 8 = s.toNat - 16 by omega]
  icases VecFromElem.stk_split n (s.toNat - 24) 4 4 $$ SL with ⟨SL0, SL4⟩
  icases stk4_word n _ $$ SL0 with ⟨%x0, SL0⟩
  icases stk4_word n _ $$ SL4 with ⟨%x4, SL4⟩
  icases stk_frame4 n (s.toNat - 48) (s - 32 - 16) e48 $$ Fr with ⟨%w0, %w4, %w8, %w12, Fr⟩
  simp only [f548]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep; mstep [SL4]
  mstep; mstep; mstep [SL0]
  mstep; mstep; mstep; mstep
  mstep; mstep; mstep; mstep
  mcall (f459_spec cfg lim (d + 1) types[30]! (by rfl) inst mi e A n g ta mx hm (by omega) Cg
      ⟨gt, .i32 (s - 32)⟩ (s - 32) rfl (by omega) (by omega) h Q (s - 32 + 8) kp kl key
      (foundU64 (h.storage key)) kh hc w0 w4 w8 w12) using [Hg HI SL0 SL4 Fr Hk Hhost]
  · iunfold StorageRead.withPre
    ihave SL0 := memBytes_addr (show s.toNat - 24 = (s - 32 + 8).toNat by omega) $$ SL0
    ihave SL4 := memBytes_addr (show s.toNat - 24 + 4 = (s - 32 + 8).toNat + 4 by omega) $$ SL4
    iframe Hg HI SL0 SL4 Fr Hk Hhost
    ipureintro; rfl
  iunfold StorageRead.withPost at HQ
  icases HQ with ⟨%hrs, Hg, HI, SL0, SL4, Fr, Hk, ⟨%h', %hq, Hhost⟩⟩
  subst hrs
  obtain ⟨hreg, hch⟩ := hQ h' hq
  rcases hsk : h.storage key with _ | val
  · ---------------------------------------------------------------- None
    simp only [costS, foundU64]
    mcredits (20 * cfg.regularOpCost + R)
    have ho4 : (ob.take 4).length = 4 := by simp; omega
    ihave Ho := U128From.memBytes_split n out.toNat 4 ob (by omega) $$ Ho
    icases Ho with ⟨Ho0, Ho4⟩
    mstep; mstep; mstep; mstep
    mstep; mstep
    simp only [show UInt64.toUInt32 0 = 0 from rfl]
    mstep
    try mpay
    mstep; mstep; mstep [Ho0]; mstep
    try mpay
    mstep; mstep; mstep; mstep [Hg]
    rw [show s - 32 + 32 = s by simp]
    mcredits R
    iframe Hc
    iunfold post548
    rw [hsk]
    simp only [optVecAt]
    isplitr
    · ipureintro; simp [htype]
    iframe Hg Hvt Hk Ho0 Hinv
    isplitl [HI HS12]
    · iunfold ifaceR; iframe HI HS12
    isplitr [Ho4 Hhost]
    · ihave Fr := frame4_stk n (s.toNat - 48) _ e48 _ _ _ _ $$ Fr
      ihave SL0 := stk_word n _ _ $$ SL0
      ihave SL4 := stk_word n _ _ $$ SL4
      ihave SL := stk_join n _ 4 4 $$ [SL0 SL4]
      · iframe SL0 SL4
      ihave SL := stk_addr (show (s - 32 + 8).toNat = s.toNat - 24 by omega) $$ SL
      ihave U := stk_join n (s.toNat - 32) 8 8 $$ [U SL]
      · rw [show s.toNat - 32 + 8 = s.toNat - 24 by omega]; iframe U SL
      ihave U := stk_join n (s.toNat - 32) 16 16 $$ [U O]
      · rw [show s.toNat - 32 + 16 = s.toNat - 16 by omega]; iframe U O
      ihave Fr := stk_join n (s.toNat - 48) 16 32 $$ [Fr U]
      · rw [show s.toNat - 48 + 16 = s.toNat - 32 by omega]; iframe Fr U
      iapply stk_join n (s.toNat - 192) 144 48
      rw [show s.toNat - 192 + 144 = s.toNat - 48 by omega]
      iframe Rg Fr
    isplitl [Ho4]
    · iexists ob.drop 4; iframe Ho4; ipureintro; simp; omega
    iexists h'
    iframe Hhost
    ipureintro; exact hq
  · ---------------------------------------------------------------- Some
    simp only [costS, foundU64]
    have hr0 := hreg val hsk
    rw [hsk] at hok
    icases stk_split n (s.toNat - 16) 12 4 $$ O with ⟨O, O12⟩
    iunfold stk at O
    icases O with ⟨%obb, %hobb, O⟩
    have hr0' : h'.registers (UInt64.toNat 0) = some val := hr0
    have h523 := f523_spec (GF := GF) cfg lim (d + 1) types[5]! (by rfl) inst mi e A n g ta mx hm (by omega) Cg
      gt (s - 32) (s - 32 + 16) (by omega) (by omega) (by omega) 0 idx maxP len live obb hobb h'
      (by rw [hr0']; exact hok)
    rw [cost523_eq cfg hr0 hch] at h523
    have hvl : val.length < 2 ^ 28 := hok.2.1
    mcredits (70 * cfg.regularOpCost + (281 * cfg.regularOpCost + registerLenUse h + costRest cfg h (some val)) + R)
    mstep; mstep; mstep; mstep
    mstep; mstep
    simp only [show UInt64.toUInt32 1 = 1 from rfl]
    mstep
    try mpay
    mstep; mstep; mstep; mstep
    mcall h523 using [Hg HI HS12 Rg Fr Hvt Hinv O Hhost]
    · iunfold pre523
      ihave Fr := frame4_stk n (s.toNat - 48) _ e48 _ _ _ _ $$ Fr
      ihave Rg := stk_join n (s.toNat - 192) 144 16 $$ [Rg Fr]
      · rw [show s.toNat - 192 + 144 = s.toNat - 48 by omega]; iframe Rg Fr
      ihave Rg := stk_addr (show s.toNat - 192 = (s - 32).toNat - 160 by omega) $$ Rg
      ihave O := memBytes_addr (show s.toNat - 16 = (s - 32 + 16).toNat by omega) $$ O
      iunfold ifaceR
      iframe Hg HI HS12 Rg Hvt Hinv O Hhost
      ipureintro; rfl
    iunfold post523 at HQ
    icases HQ with ⟨%hrs, Hg, HI, Rg, Hvt, HO, Hhost⟩
    subst hrs
    rw [hr0']
    simp only [optVecAt]
    icases HO with ⟨%p, P0, P4, P8, %len', %⟨hp0, hl'⟩, Hinv, Hb⟩
    mcredits (40 * cfg.regularOpCost + R)
    mstep; mstep; mstep; mstep; mstep; mstep; mstep
    mcall (f498_spec cfg lim (d + 1) types[39]! (by rfl) inst mi n hn Cg out (s - 32 + 16) p
        (UInt32.ofNat val.length) (UInt32.ofNat val.length) ob hob hp0 hout (by omega)) using [P0 P4 P8 Ho]
    · iunfold pre498
      iframe P0 P4 P8 Ho
      ipureintro; exact ⟨_, _, _, rfl⟩
    iunfold post498 at HQ
    icases HQ with ⟨%hrs, P0, P4, P8, Ho0, Ho4, Ho8⟩
    subst hrs
    mstep; mstep; mstep; mstep [Hg]
    rw [show s - 32 + 32 = s by simp]
    mcredits R
    iframe Hc
    iunfold post548
    rw [hsk]
    simp only [optVecAt]
    isplitr
    · ipureintro; simp [htype]
    iframe Hg Hvt Hk
    isplitl [HI]
    · iexact HI
    isplitr [Ho0 Ho4 Ho8 Hinv Hb Hhost]
    · ihave Rg := stk_addr (show (s - 32).toNat - 160 = s.toNat - 192 by omega) $$ Rg
      icases stk_split n (s.toNat - 192) 144 16 $$ Rg with ⟨Rg, Fr⟩
      ihave Fr := stk_addr (show s.toNat - 192 + 144 = s.toNat - 48 by omega) $$ Fr
      ihave SL0 := stk_word n _ _ $$ SL0
      ihave SL4 := stk_word n _ _ $$ SL4
      ihave SL := stk_join n _ 4 4 $$ [SL0 SL4]
      · iframe SL0 SL4
      ihave SL := stk_addr (show (s - 32 + 8).toNat = s.toNat - 24 by omega) $$ SL
      ihave P0 := stk_word n _ _ $$ P0
      ihave P4 := stk_word n _ _ $$ P4
      ihave P8 := stk_word n _ _ $$ P8
      ihave P := stk_join n _ 4 4 $$ [P0 P4]
      · iframe P0 P4
      ihave P := stk_join n _ 8 4 $$ [P P8]
      · iframe P P8
      ihave P := stk_addr (show (s - 32 + 16).toNat = s.toNat - 16 by omega) $$ P
      ihave O := stk_join n (s.toNat - 16) 12 4 $$ [P O12]
      · iframe P O12
      ihave U := stk_join n (s.toNat - 32) 8 8 $$ [U SL]
      · rw [show s.toNat - 32 + 8 = s.toNat - 24 by omega]; iframe U SL
      ihave U := stk_join n (s.toNat - 32) 16 16 $$ [U O]
      · rw [show s.toNat - 32 + 16 = s.toNat - 16 by omega]; iframe U O
      ihave Fr := stk_join n (s.toNat - 48) 16 32 $$ [Fr U]
      · rw [show s.toNat - 48 + 16 = s.toNat - 32 by omega]; iframe Fr U
      iapply stk_join n (s.toNat - 192) 144 48
      rw [show s.toNat - 192 + 144 = s.toNat - 48 by omega]
      iframe Rg Fr
    isplitr [Hhost]
    · iexists p
      iframe Ho0 Ho4 Ho8
      iexists len'
      iframe Hinv Hb
      ipureintro; exact ⟨hp0, hl'⟩
    iexists h'
    iframe Hhost
    ipureintro; exact hq

open Near.TrieAccounting Near.TrieConstruction Near.TrieOverlay in
/-- `f548_spec` with the host's `storageRead_readContract` (register 0): the host ends in some
`h'` with `StorageReadPost h key 0 st`, the gas `storageReadUse h key kl`. -/
theorem f548_spec_host (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (e : Nat) (A : Nat → Nat)
    (n g ta : Nat) (mx : Option Nat) (hm : IfaceMod mi A n g ta) (hd : d + 14 < lim.maxCallDepth)
    (Cg : Nat) (gt : GlobalType) (s out kp kl : UInt32) (hs : 192 ≤ s.toNat) (hal : s.toNat % 8 = 0)
    (hout : out.toNat + 12 ≤ 2 ^ 32) (key : List UInt8) (idx : UInt32) (maxP len : Nat)
    (live : List (Nat × Nat)) (ob : List UInt8) (hob : ob.length = 12) (h : NearState)
    (st : Near.TrieOverlay.State) (hkl : key.length = kl.toNat) (hpos : 0 < kl.toNat)
    (hacc : h.storageAccounting = some st)
    (hlim : withinLimit h.config.maxStorageKeyLen key.length = true)
    (hb : build st.entries = .ok st.base) (hz : zeroHash ∉ st.base.witness.map Prod.fst)
    (hp : ∀ x ∈ st.prospective, x.1 ≠ contractKey h.context.currentAccountId key)
    (hcm : ∀ x ∈ st.committed, x.1 ≠ contractKey h.context.currentAccountId key)
    (hlink : h.storage key = (st.entries.find? (·.1 == contractKey h.context.currentAccountId key)).map (·.2))
    (hproof : ProofBudget h st (lookupProofBound (contractKey h.context.currentAccountId key)))
    (hreg : ∀ v, h.storage key = some v → withinLimit h.config.maxRegisterLen v.length = true)
    (hok : RegOk maxP len (h.storage key)) :
    srCode e inst mi A n maxP mx
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f548 Cg
        (pre548 n g ta A gt s out kp kl key idx maxP len live ob h)
        (fun _ => 40 * cfg.regularOpCost + (249 * cfg.regularOpCost + storageReadUse h key kl.toNat) +
          costS cfg h (h.storage key))
        (post548 n g ta A gt s out kp key idx maxP len live h (StorageReadPost h key 0 st)) := by
  have hlen : UInt64.ofNat kl.toNat ≠ u64Max := by
    have := kl.toNat_lt
    intro h'
    have h'' := congrArg UInt64.toNat h'
    simp [u64Max] at h''
    omega
  have hc := storageRead_readContract (C := Cg) e h (UInt64.ofNat kl.toNat) (UInt64.ofNat kp.toNat) 0 key st
    hlen (by rw [ValueReturn.toNat_ofNat32]; exact hkl) (by rw [ValueReturn.toNat_ofNat32]; exact hpos) hacc hlim
    hb hz hp hcm hlink hproof (Nat.le_refl _) (fun v hv _ => hreg v hv)
  rw [ValueReturn.toNat_ofNat32, ValueReturn.toNat_ofNat32] at hc
  exact f548_spec cfg lim d type htype inst mi e A n g ta mx hm hd Cg gt s out kp kl hs hal hout key idx maxP len
    live ob hob h _ _ hc (storageReadPost_ok h key st) hok

end Spec

end WNear.Binary.StorageReadWrap
