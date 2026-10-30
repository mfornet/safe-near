import Bridge.Functions.BorshInt
import Bridge.Functions.BorshVecF

/-!
# Borsh's `Vec<u8>` reader (316, and its wrapper 315)

```wat
;; 316 Vec<u8>::deserialize_reader (out, r): sp -= 64
;;     m := r.len; m < 4 → Err
;;     362(sp + 40, q, m, 4); v := 765([sp+40], [sp+44])     ;; the u32 length, tag in bit 0
;;     v & 1 → panic (unreachable); 361(sp + 32, q, m, 4); r := [sp+32] (i64)
;;     L := v >> 8; L = 0 → out := Vec::new() (not on our paths)
;;     764(sp + 24, L); [sp+24] ≠ 0 → Err;  r.len < L → Err
;;     362(sp + 16, r.ptr, r.len, L); 374(sp + 48, [sp+16], [sp+20])      ;; to_vec
;;     361(sp + 8, r.ptr, r.len, L); out := (0, [sp+48] (i64), [sp+56]); r := [sp+8] (i64)
;; 315 (out, r): sp -= 16; 316(sp, r); [sp] = 1 → Err; out := (0, [sp+4] (i64), [sp+12])
```

* `f316_spec`, `f315_spec`: on `u32 L ++ data` at `q` (`L = |data|`, `0 < L < 2^28`, with room
  for the allocation, `4 + L ≤ m`), `Ok` (tag word 0) at `out` and the `Vec` `(p, L, L)` at
  `out + 4` (`vecAt`), `p` a fresh live block holding `data`; the reader advanced past it.
-/

namespace WNear.Binary.BorshBytesF

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.BorshLeaves WNear.Binary.BorshInt WNear.Binary.BorshVecF
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_word stk_addr stk_intro pair64 storeBytes_pair64
  ofNat_decode_pair roomFor)
open WNear.Binary.VecWithCap (vecCode2 okG)
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.AllocInv (heapInv)
open WNear.Binary.Interface (IfaceMod)

theorem r765_and (bs : List UInt8) (h : bs.length = 4) : r765 bs &&& 1 = 0 := by
  have hl := decodeLE_lt4 bs h
  apply UInt64.toNat_inj.mp
  simp only [r765, UInt64.toNat_and, UInt64.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega)]
  simp
  omega

theorem r765_shr (bs : List UInt8) (h : bs.length = 4) :
    (r765 bs >>> (8 % 64)).toUInt32 = UInt32.ofNat (Memory.decodeLE bs) := by
  have hl := decodeLE_lt4 bs h
  apply UInt32.toNat_inj.mp
  simp only [r765, UInt64.toNat_toUInt32, UInt64.toNat_shiftRight, UInt64.toNat_ofNat']
  simp [Nat.shiftRight_eq_div_pow]
  omega

section Spec

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The code the `Vec<u8>` reader runs (persistent). -/
def bytesCode (n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) : IProp GF :=
  iprop(rdCode inst mi A ∗ vecCode2 n maxP inst mi A ∗ A 374 ↪[wf] FuncInst.wasm types[31]! inst f374 ∗
    A 316 ↪[wf] FuncInst.wasm types[14]! inst f316)

instance (n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) :
    Persistent (bytesCode (GF := GF) n maxP inst mi A) := by
  unfold bytesCode; infer_instance

def pre316 (n g : Nat) (gt : GlobalType) (s out r q m : UInt32) (idx : UInt32) (ta a578 maxP len : Nat)
    (live : List (Nat × Nat)) (F : Nat) (ob hd data : List UInt8) (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 out, .i32 r]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 144) 144 ∗
    vt n 1057464 idx ta a578 ∗ heapInv n maxP len live F ∗ rdr n r q m ∗ n ↦[wms][ out.toNat ] ob ∗
    n ↦[wms][ q.toNat ] hd ∗ n ↦[wms][ q.toNat + 4 ] data)

def post316 (n g : Nat) (gt : GlobalType) (s out r q m : UInt32) (idx : UInt32) (ta a578 maxP len : Nat)
    (live : List (Nat × Nat)) (F : Nat) (hd data : List UInt8) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 144) 144 ∗ vt n 1057464 idx ta a578 ∗
    rdr n r (q + 4 + UInt32.ofNat data.length) (m - 4 - UInt32.ofNat data.length) ∗
    n ↦[i32][ out.toNat ] 0 ∗ vecAt n maxP len live F (out.toNat + 4) data ∗
    n ↦[wms][ q.toNat ] hd ∗ n ↦[wms][ q.toNat + 4 ] data)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **`Vec<u8>::deserialize_reader`** (316) on `hd ++ data` at `q`, `hd` the `u32` length of
`data`. -/
theorem f316_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 12 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s out r q m : UInt32) (idx : UInt32) (maxP len : Nat) (live : List (Nat × Nat)) (F : Nat) (hF : okG F)
    (ob hd4 data : List UInt8) (hob : ob.length = 16) (hhd : hd4.length = 4)
    (hL : Memory.decodeLE hd4 = data.length) (hL0 : 0 < data.length) (hL28 : data.length < 2 ^ 28)
    (hroom : roomFor len maxP (UInt32.ofNat data.length))
    (hs : 144 ≤ s.toNat) (hmL : 4 + data.length ≤ m.toNat)
    (hq : q.toNat + 4 + data.length ≤ 2 ^ 32) (hout : out.toNat + 16 ≤ 2 ^ 32) (hr : r.toNat + 8 ≤ 2 ^ 32) :
    bytesCode n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f316 Cg
        (pre316 n g gt s out r q m idx ta (A 578) maxP len live F ob hd4 data)
        (fun _ => 260 * cfg.regularOpCost + cost374 cfg F (UInt32.ofNat data.length))
        (post316 n g gt s out r q m idx ta (A 578) maxP len live F hd4 data) := by
  iintro #Hcode
  iunfold bytesCode at Hcode
  icases Hcode with ⟨#Hrd, #Hv, #H374, -⟩
  ihave #Hrd' := Hrd
  iunfold rdCode at Hrd'
  icases Hrd' with ⟨#Hi, #H361, #H362, -, -, #H764, #H765⟩
  have hn := hm.mem
  have hg := hm.glob
  have ha361 := hm.funcs 361 (by decide)
  have ha362 := hm.funcs 362 (by decide)
  have ha764 := hm.funcs 764 (by decide)
  have ha765 := hm.funcs 765 (by decide)
  have ha374 := hm.funcs 374 (by decide)
  have t39 : types[39]!.params.length = 5 := by rfl
  have t31 : types[31]!.params.length = 3 := by rfl
  have t14 : types[14]!.params.length = 2 := by rfl
  have t30 : types[30]!.params.length = 2 := by rfl
  have hlt := s.toNat_lt
  have hmlt := m.toNat_lt
  have hqlt := q.toNat_lt
  have h64 : (s - 64).toNat = s.toNat - 64 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have hLlt : data.length < 2 ^ 32 := by omega
  have hLn : (UInt32.ofNat data.length).toNat = data.length := by simp; omega
  have hm4 : ¬ m < 4 := by rw [UInt32.lt_iff_toNat_lt]; simp; omega
  have hm4' : (m - 4).toNat = m.toNat - 4 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have hq4 : (q + 4).toNat = q.toNat + 4 := by simp [UInt32.toNat_add]; omega
  have hge : UInt32.ofNat data.length ≤ m - 4 := by rw [UInt32.le_iff_toNat_le, hm4', hLn]; omega
  have hL0' : UInt32.ofNat data.length ≠ 0 := by
    intro h; have := congrArg UInt32.toNat h; rw [hLn] at this; simp only [UInt32.toNat_zero] at this; omega
  have hand := r765_and hd4 hhd
  have hshr := r765_shr hd4 hhd
  rw [hL] at hshr
  generalize hK : cost374 cfg F (UInt32.ofNat data.length) = K
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold pre316 at HP
  icases HP with ⟨%hargs, Hg, Hs, Hvt, Hinv, Hr, Ho, Hd4, Hdata⟩
  subst hargs
  iunfold rdr at Hr
  ihave Hr := KeyGet.split64 n r.toNat q m $$ Hr
  icases Hr with ⟨Rq, Rm⟩
  ihave Ho := U128From.memBytes_split n out.toNat 4 ob (by omega) $$ Ho
  icases Ho with ⟨Ho0, Ho⟩
  ihave Ho := U128From.memBytes_split n (out.toNat + 4) 8 (ob.drop 4) (by simp; omega) $$ Ho
  icases Ho with ⟨Ho4, Ho12⟩
  -- the stack: 80 below the frame, then [sp, 8) [8, 8) [16, 8) [24, 8) [32, 8) [40, 8) [48, 12) [60, 4)
  icases stk_split n (s.toNat - 144) 80 64 $$ Hs with ⟨Lo, Hs⟩
  rw [show s.toNat - 144 + 80 = s.toNat - 64 by omega]
  icases stk_split n (s.toNat - 64) 8 56 $$ Hs with ⟨S0, Hs⟩
  icases stk_split n (s.toNat - 64 + 8) 8 48 $$ Hs with ⟨S8, Hs⟩
  icases stk_split n (s.toNat - 64 + 8 + 8) 8 40 $$ Hs with ⟨S16, Hs⟩
  icases stk_split n (s.toNat - 64 + 8 + 8 + 8) 8 32 $$ Hs with ⟨S24, Hs⟩
  icases stk_split n (s.toNat - 64 + 8 + 8 + 8 + 8) 8 24 $$ Hs with ⟨S32, Hs⟩
  icases stk_split n (s.toNat - 64 + 8 + 8 + 8 + 8 + 8) 8 16 $$ Hs with ⟨S40, Hs⟩
  icases stk_split n (s.toNat - 64 + 8 + 8 + 8 + 8 + 8 + 8) 12 4 $$ Hs with ⟨S48, S60⟩
  rw [show s.toNat - 64 + 8 = s.toNat - 56 by omega, show s.toNat - 56 + 8 = s.toNat - 48 by omega,
    show s.toNat - 48 + 8 = s.toNat - 40 by omega, show s.toNat - 40 + 8 = s.toNat - 32 by omega,
    show s.toNat - 32 + 8 = s.toNat - 24 by omega, show s.toNat - 24 + 8 = s.toNat - 16 by omega,
    show s.toNat - 16 + 12 = s.toNat - 4 by omega]
  icases stk_bytes' $$ S8 with ⟨%c8, %hc8, S8⟩
  icases stk_bytes' $$ S16 with ⟨%c16, %hc16, S16⟩
  icases stk_bytes' $$ S24 with ⟨%c24, %hc24, S24⟩
  icases stk_bytes' $$ S32 with ⟨%c32, %hc32, S32⟩
  icases stk_bytes' $$ S40 with ⟨%c40, %hc40, S40⟩
  icases stk_bytes' $$ S48 with ⟨%c48, %hc48, S48⟩
  simp only [f316]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep; mstep; mstep; mstep [Rm]; mstep; mstep; mstep
  mstep with simp [Numeric.bool, Numeric.irelop32, hm4]
  mstep; mstep; mstep; mstep; mstep [Rq]; mstep; mstep; mstep
  mcall (f362_spec cfg lim (d + 1) types[39]! (by rfl) inst mi n hn Cg (s - 64 + 40) q m 4 c40 hc40 (by simp; omega))
    using [S40]
  · iunfold pre36x
    ihave S40 := memBytes_addr (show s.toNat - 24 = (s - 64 + 40).toNat by simp [UInt32.toNat_add, h64]; omega) $$ S40
    iframe S40
    ipureintro; exact ⟨_, rfl⟩
  iunfold post36x at HQ
  icases HQ with ⟨%hrs, S40, S44⟩
  subst hrs
  mstep; mstep; mstep [S40]; mstep; mstep [S44]
  mcall (f765_spec cfg lim (d + 1) types[30]! (by rfl) inst mi n hn Cg q hd4 hhd) using [Hd4]
  · iunfold pre765
    iframe Hd4
    ipureintro; rfl
  iunfold post765 at HQ
  icases HQ with ⟨%hrs, Hd4⟩
  subst hrs
  mstep; mstep; mstep
  rw [hand]
  mstep; mstep; mstep
  mstep; mstep; mstep; mstep; mstep [Rq]; mstep; mstep [Rm]; mstep; mstep
  mcall (f361_spec cfg lim (d + 1) types[39]! (by rfl) inst mi n hn Cg (s - 64 + 32) q m 4 c32 hc32 (by simp; omega))
    using [S32]
  · iunfold pre36x
    ihave S32 := memBytes_addr (show s.toNat - 32 = (s - 64 + 32).toNat by simp [UInt32.toNat_add, h64]; omega) $$ S32
    iframe S32
    ipureintro; exact ⟨_, rfl⟩
  iunfold post36x at HQ
  icases HQ with ⟨%hrs, S32, S36⟩
  subst hrs
  ihave S32 := KeyGet.join64 n (s - 64 + 32).toNat (q + 4) (m - 4) $$ [S32 S36]
  · iframe S32 S36
  ihave Rr := KeyGet.join64 n r.toNat q m $$ [Rq Rm]
  · iframe Rq Rm
  mstep; mstep; mstep [S32]
  rw [ofNat_decode_pair]
  mstep [Rr]
  rw [storeBytes_pair64]
  ihave Rr := KeyGet.split64 n r.toNat (q + 4) (m - 4) $$ Rr
  icases Rr with ⟨Rq, Rm⟩
  mstep; mstep; mstep; mstep
  mstep
  rw [hshr]
  mstep
  mstep with simp [hL0']
  mstep; mstep; mstep; mstep
  mcall (f764_spec cfg lim (d + 1) types[14]! (by rfl) inst mi n hn Cg (s - 64 + 24) (UInt32.ofNat data.length)
      c24 hc24) using [S24]
  · iunfold pre764
    ihave S24 := memBytes_addr (show s.toNat - 40 = (s - 64 + 24).toNat by simp [UInt32.toNat_add, h64]; omega) $$ S24
    iframe S24
    ipureintro; rfl
  iunfold post36x at HQ
  icases HQ with ⟨%hrs, S24, S28⟩
  subst hrs
  mstep; mstep [S24]; mstep
  mstep; mstep; mstep [Rm]; mstep; mstep; mstep [S28]; mstep; mstep
  mstep with simp [Numeric.bool, Numeric.irelop32, hge]
  mstep; mstep; mstep; mstep; mstep [Rq]; mstep; mstep; mstep
  mcall (f362_spec cfg lim (d + 1) types[39]! (by rfl) inst mi n hn Cg (s - 64 + 16) (q + 4) (m - 4)
      (UInt32.ofNat data.length) c16 hc16 (by rw [hLn, hm4']; omega)) using [S16]
  · iunfold pre36x
    ihave S16 := memBytes_addr (show s.toNat - 48 = (s - 64 + 16).toNat by simp [UInt32.toNat_add, h64]; omega) $$ S16
    iframe S16
    ipureintro; exact ⟨_, rfl⟩
  iunfold post36x at HQ
  icases HQ with ⟨%hrs, S16, S20⟩
  subst hrs
  mstep; mstep; mstep; mstep; mstep [S16]; mstep; mstep [S20]
  have S374 := f374_spec (GF := GF) cfg lim (d + 1) types[31]! (by rfl) inst mi A n g ta hm (by omega) Cg gt (s - 64)
    (s - 64 + 48) (q + 4) (UInt32.ofNat data.length) idx maxP len live F hF c48 data hc48 hLn.symm (by omega)
    (by rw [hLn]; omega) (by rw [hLn]; omega) hroom (by rw [hLn, hq4]; omega)
    (by simp [UInt32.toNat_add, h64]; omega)
  rw [hK] at S374
  mcall S374 using [Hg Lo Hvt Hinv S48 Hdata]
  · iunfold pre374
    ihave Lo := stk_addr (show s.toNat - 144 = (s - 64).toNat - 80 by omega) $$ Lo
    ihave S48 := memBytes_addr (show s.toNat - 16 = (s - 64 + 48).toNat by simp [UInt32.toNat_add, h64]; omega) $$ S48
    ihave Hdata := memBytes_addr (show q.toNat + 4 = (q + 4).toNat by omega) $$ Hdata
    iframe Hg Lo Hvt Hinv S48 Hdata
    ipureintro; rfl
  iunfold post374 at HQ
  icases HQ with ⟨%hrs, Hg, Lo, Hvt, Hdata, V⟩
  subst hrs
  mcredits (59 * cfg.regularOpCost + R)
  iunfold vecAt at V
  icases V with ⟨%p, V0, V4, V8, %len', %hl', Hinv, Hb⟩
  mstep; mstep; mstep; mstep; mstep [Rq]; mstep; mstep [Rm]; mstep; mstep
  mcall (f361_spec cfg lim (d + 1) types[39]! (by rfl) inst mi n hn Cg (s - 64 + 8) (q + 4) (m - 4)
      (UInt32.ofNat data.length) c8 hc8 (by rw [hLn, hm4']; omega)) using [S8]
  · iunfold pre36x
    ihave S8 := memBytes_addr (show s.toNat - 56 = (s - 64 + 8).toNat by simp [UInt32.toNat_add, h64]; omega) $$ S8
    iframe S8
    ipureintro; exact ⟨_, rfl⟩
  iunfold post36x at HQ
  icases HQ with ⟨%hrs, S8, S12⟩
  subst hrs
  ihave S8 := KeyGet.join64 n (s - 64 + 8).toNat _ _ $$ [S8 S12]
  · iframe S8 S12
  mstep; mstep [S8]
  rw [ofNat_decode_pair]
  mstep
  mstep; mstep; mstep; mstep; mstep [V8]; mstep [Ho12]
  ihave V0 := KeyGet.join64 n (s - 64 + 48).toNat p _ $$ [V0 V4]
  · iframe V0 V4
  mstep; mstep; mstep [V0]
  rw [ofNat_decode_pair]
  mstep [Ho4]
  rw [storeBytes_pair64]
  mstep; mstep; mstep [Ho0]
  ihave Rr := KeyGet.join64 n r.toNat (q + 4) (m - 4) $$ [Rq Rm]
  · iframe Rq Rm
  mstep; mstep; mstep [Rr]
  rw [storeBytes_pair64]
  mstep
  mstep; mstep; mstep; mstep [Hg]
  rw [show s - 64 + 64 = s by simp]
  mcredits R
  ihave Hdata := memBytes_addr hq4 $$ Hdata
  ihave VV : vecAt n maxP len live F (out.toNat + 4) data $$ [Ho4 Ho12 Hinv Hb]
  · iunfold vecAt
    iexists p
    ihave Ho4 := KeyGet.split64 n (out.toNat + 4) p _ $$ Ho4
    icases Ho4 with ⟨Ho4, Ho8⟩
    iframe Ho4 Ho8 Ho12
    iexists len'
    iframe Hinv Hb
    ipureintro; exact hl'
  -- the stack
  ihave S8 := KeyGet.split64 n (s - 64 + 8).toNat _ _ $$ S8
  icases S8 with ⟨S8, S12⟩
  ihave S8 := stk_word n _ _ $$ S8
  ihave S12 := stk_word n _ _ $$ S12
  ihave S8 := stk_join n _ 4 4 $$ [S8 S12]
  · iframe S8 S12
  ihave S8 := stk_addr (show (s - 64 + 8).toNat = s.toNat - 56 by simp [UInt32.toNat_add, h64]; omega) $$ S8
  ihave S16 := stk_word n _ _ $$ S16
  ihave S20 := stk_word n _ _ $$ S20
  ihave S16 := stk_join n _ 4 4 $$ [S16 S20]
  · iframe S16 S20
  ihave S16 := stk_addr (show (s - 64 + 16).toNat = s.toNat - 48 by simp [UInt32.toNat_add, h64]; omega) $$ S16
  ihave S24 := stk_word n _ _ $$ S24
  ihave S28 := stk_word n _ _ $$ S28
  ihave S24 := stk_join n _ 4 4 $$ [S24 S28]
  · iframe S24 S28
  ihave S24 := stk_addr (show (s - 64 + 24).toNat = s.toNat - 40 by simp [UInt32.toNat_add, h64]; omega) $$ S24
  ihave S32 := ReadRegister.stk_bytes n _ _ 8 (by simp) $$ S32
  ihave S32 := stk_addr (show (s - 64 + 32).toNat = s.toNat - 32 by simp [UInt32.toNat_add, h64]; omega) $$ S32
  ihave S40 := stk_word n _ _ $$ S40
  ihave S44 := stk_word n _ _ $$ S44
  ihave S40 := stk_join n _ 4 4 $$ [S40 S44]
  · iframe S40 S44
  ihave S40 := stk_addr (show (s - 64 + 40).toNat = s.toNat - 24 by simp [UInt32.toNat_add, h64]; omega) $$ S40
  ihave V0 := ReadRegister.stk_bytes n _ _ 8 (by simp) $$ V0
  ihave V8 := stk_word n _ _ $$ V8
  ihave V0 := stk_join n _ 8 4 $$ [V0 V8]
  · iframe V0 V8
  ihave V0 := stk_addr (show (s - 64 + 48).toNat = s.toNat - 16 by simp [UInt32.toNat_add, h64]; omega) $$ V0
  ihave V0 := stk_join n (s.toNat - 16) 12 4 $$ [V0 S60]
  · rw [show s.toNat - 16 + 12 = s.toNat - 4 by omega]; iframe V0 S60
  ihave S40 := stk_join n (s.toNat - 24) 8 16 $$ [S40 V0]
  · rw [show s.toNat - 24 + 8 = s.toNat - 16 by omega]; iframe S40 V0
  ihave S32 := stk_join n (s.toNat - 32) 8 24 $$ [S32 S40]
  · rw [show s.toNat - 32 + 8 = s.toNat - 24 by omega]; iframe S32 S40
  ihave S24 := stk_join n (s.toNat - 40) 8 32 $$ [S24 S32]
  · rw [show s.toNat - 40 + 8 = s.toNat - 32 by omega]; iframe S24 S32
  ihave S16 := stk_join n (s.toNat - 48) 8 40 $$ [S16 S24]
  · rw [show s.toNat - 48 + 8 = s.toNat - 40 by omega]; iframe S16 S24
  ihave S8 := stk_join n (s.toNat - 56) 8 48 $$ [S8 S16]
  · rw [show s.toNat - 56 + 8 = s.toNat - 48 by omega]; iframe S8 S16
  ihave S0 := stk_join n (s.toNat - 64) 8 56 $$ [S0 S8]
  · rw [show s.toNat - 64 + 8 = s.toNat - 56 by omega]; iframe S0 S8
  ihave Lo := stk_addr (show (s - 64).toNat - 80 = s.toNat - 144 by omega) $$ Lo
  ihave Stk := stk_join n (s.toNat - 144) 80 64 $$ [Lo S0]
  · rw [show s.toNat - 144 + 80 = s.toNat - 64 by omega]; iframe Lo S0
  iframe Hc
  iunfold post316, rdr
  iframe Hg Hvt Rr Ho0 Hd4 Stk VV Hdata
  ipureintro; rfl

/-! ## The wrapper (315) -/

def pre315 (n g : Nat) (gt : GlobalType) (s out r q m : UInt32) (idx : UInt32) (ta a578 maxP len : Nat)
    (live : List (Nat × Nat)) (F : Nat) (ob hd data : List UInt8) (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 out, .i32 r]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 160) 160 ∗
    vt n 1057464 idx ta a578 ∗ heapInv n maxP len live F ∗ rdr n r q m ∗ n ↦[wms][ out.toNat ] ob ∗
    n ↦[wms][ q.toNat ] hd ∗ n ↦[wms][ q.toNat + 4 ] data)

def post315 (n g : Nat) (gt : GlobalType) (s out r q m : UInt32) (idx : UInt32) (ta a578 maxP len : Nat)
    (live : List (Nat × Nat)) (F : Nat) (hd data : List UInt8) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 160) 160 ∗ vt n 1057464 idx ta a578 ∗
    rdr n r (q + 4 + UInt32.ofNat data.length) (m - 4 - UInt32.ofNat data.length) ∗
    n ↦[i32][ out.toNat ] 0 ∗ vecAt n maxP len live F (out.toNat + 4) data ∗
    n ↦[wms][ q.toNat ] hd ∗ n ↦[wms][ q.toNat + 4 ] data)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **`Vec<u8>::deserialize`** (315): 316 into its frame, the result copied to `out`. -/
theorem f315_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 13 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s out r q m : UInt32) (idx : UInt32) (maxP len : Nat) (live : List (Nat × Nat)) (F : Nat) (hF : okG F)
    (ob hd4 data : List UInt8) (hob : ob.length = 16) (hhd : hd4.length = 4)
    (hL : Memory.decodeLE hd4 = data.length) (hL0 : 0 < data.length) (hL28 : data.length < 2 ^ 28)
    (hroom : roomFor len maxP (UInt32.ofNat data.length))
    (hs : 160 ≤ s.toNat) (hmL : 4 + data.length ≤ m.toNat)
    (hq : q.toNat + 4 + data.length ≤ 2 ^ 32) (hout : out.toNat + 16 ≤ 2 ^ 32) (hr : r.toNat + 8 ≤ 2 ^ 32) :
    bytesCode n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f315 Cg
        (pre315 n g gt s out r q m idx ta (A 578) maxP len live F ob hd4 data)
        (fun _ => 53 * cfg.regularOpCost + (260 * cfg.regularOpCost + cost374 cfg F (UInt32.ofNat data.length)))
        (post315 n g gt s out r q m idx ta (A 578) maxP len live F hd4 data) := by
  iintro #Hcode
  ihave #Hcode' := Hcode
  iunfold bytesCode, rdCode at Hcode'
  icases Hcode' with ⟨⟨#Hi, -⟩, -, -, #H316⟩
  have hn := hm.mem
  have hg := hm.glob
  have ha316 := hm.funcs 316 (by decide)
  have t14 : types[14]!.params.length = 2 := by rfl
  have hlt := s.toNat_lt
  have h16 : (s - 16).toNat = s.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold pre315 at HP
  icases HP with ⟨%hargs, Hg, Hs, Hvt, Hinv, Hr, Ho, Hd4, Hdata⟩
  subst hargs
  ihave Ho := U128From.memBytes_split n out.toNat 4 ob (by omega) $$ Ho
  icases Ho with ⟨Ho0, Ho⟩
  ihave Ho := U128From.memBytes_split n (out.toNat + 4) 8 (ob.drop 4) (by simp; omega) $$ Ho
  icases Ho with ⟨Ho4, Ho12⟩
  icases stk_split n (s.toNat - 160) 144 16 $$ Hs with ⟨Lo, Fr⟩
  rw [show s.toNat - 160 + 144 = s.toNat - 16 by omega]
  icases stk_bytes' $$ Fr with ⟨%fb, %hfb, Fr⟩
  simp only [f315]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep
  mcall (f316_spec cfg lim (d + 1) types[14]! (by rfl) inst mi A n g ta hm (by omega) Cg gt (s - 16) (s - 16) r q m
      idx maxP len live F hF fb hd4 data hfb hhd hL hL0 hL28 hroom (by omega) hmL hq (by omega) hr)
    using [Hg Lo Hvt Hinv Hr Fr Hd4 Hdata]
  · iunfold pre316
    ihave Lo := stk_addr (show s.toNat - 160 = (s - 16).toNat - 144 by omega) $$ Lo
    ihave Fr := memBytes_addr (show s.toNat - 16 = (s - 16).toNat by omega) $$ Fr
    iframe Hg Lo Hvt Hinv Hr Fr Hd4 Hdata
    ipureintro; rfl
  iunfold post316 at HQ
  icases HQ with ⟨%hrs, Hg, Lo, Hvt, Hr, V0, VV, Hd4, Hdata⟩
  subst hrs
  iunfold vecAt at VV
  icases VV with ⟨%p, V4, V8, V12, %len', %hl', Hinv, Hb⟩
  mcredits (33 * cfg.regularOpCost + R)
  ihave V4 := KeyGet.join64 n ((s - 16).toNat + 4) p _ $$ [V4 V8]
  · iframe V4 V8
  mstep; mstep; mstep; mstep [V4]
  rw [ofNat_decode_pair]
  mstep
  mstep; mstep; mstep; mstep [V0]; mstep; mstep
  mstep
  mstep; mstep; mstep; mstep [V12]; mstep
  mstep; mstep; mstep [Ho4]
  rw [storeBytes_pair64]
  mstep; mstep; mstep; mstep; mstep [Ho12]
  mstep; mstep; mstep
  mstep; mstep; mstep [Ho0]
  mstep; mstep; mstep; mstep [Hg]
  rw [show s - 16 + 16 = s by simp]
  mcredits R
  ihave VV : vecAt n maxP len live F (out.toNat + 4) data $$ [Ho4 Ho12 Hinv Hb]
  · iunfold vecAt
    iexists p
    ihave Ho4 := KeyGet.split64 n (out.toNat + 4) p _ $$ Ho4
    icases Ho4 with ⟨Ho4, Ho8⟩
    iframe Ho4 Ho8 Ho12
    iexists len'
    iframe Hinv Hb
    ipureintro; exact hl'
  ihave V0 := stk_word n _ _ $$ V0
  ihave V4 := ReadRegister.stk_bytes n _ _ 8 (by simp) $$ V4
  ihave V12 := stk_word n _ _ $$ V12
  ihave V4 := stk_join n _ 8 4 $$ [V4 V12]
  · rw [show (s - 16).toNat + 4 + 8 = (s - 16).toNat + 4 + 8 from rfl]; iframe V4 V12
  ihave V0 := stk_join n _ 4 12 $$ [V0 V4]
  · iframe V0 V4
  ihave V0 := stk_addr (show (s - 16).toNat = s.toNat - 16 by omega) $$ V0
  ihave Lo := stk_addr (show (s - 16).toNat - 144 = s.toNat - 160 by omega) $$ Lo
  ihave Stk := stk_join n (s.toNat - 160) 144 16 $$ [Lo V0]
  · rw [show s.toNat - 160 + 144 = s.toNat - 16 by omega]; iframe Lo V0
  iframe Hc
  iunfold post315
  iframe Hg Hvt Hr Ho0 Hd4 Stk VV Hdata
  ipureintro; rfl

end Spec

end WNear.Binary.BorshBytesF
