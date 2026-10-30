import Bridge.Functions.BorshLeaves
import Bridge.Functions.VecFromElem
import Bridge.Functions.ReadRegister

/-!
# Borsh's `u128` (372) and `u64` (371) readers

The reader is a `&mut &[u8]` at `r`: the slice `(q, m)` (pointer, remaining length), held as
`rdr n r q m` (eight bytes). Each reader takes the next `k` bytes (16 or 8), checks the length
(`m ≥ k`, else an `Err`, not on our paths), copies them through the `[u8; k]` conversion (694 /
710) and advances the slice (361):

```wat
;; 372 u128::deserialize_reader (out, r): sp -= 48
;;     m := r.len; m ≤ 15 → Err
;;     362(sp + 8, q, m, 16); 694(sp + 16, [sp+8], [sp+12]); [sp+16] = 1 → panic (unreachable)
;;     hi := [sp+25] (i64); lo := [sp+17] (i64); 361(sp, q, m, 16)
;;     out+16 := hi; out+8 := lo; r := [sp] (i64); out := 0 (Ok)
;; 371 u64::deserialize_reader (out, r): sp -= 48
;;     m := r.len; m ≤ 7 → Err
;;     362(sp + 16, q, m, 8); 710(sp + 24, [sp+16], [sp+20]); [sp+24] = 1 → panic
;;     v := [sp+25] (i64); 361(sp + 8, q, m, 8); out+8 := v; r := [sp+8] (i64); out := 0 (Ok)
```

* `f372_spec`: the 16 bytes `b0 ++ b1` at `q` copied to `out + 8`, `Ok` (tag word 0) at `out`,
  the reader advanced to `(q + 16, m - 16)`;
* `f371_spec`: the same for the 8 bytes `b0`.
-/

namespace WNear.Binary.BorshInt

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.BorshLeaves
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_word stk_addr stk_intro pair64 storeBytes_pair64
  ofNat_decode_pair)
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.Interface (IfaceMod)

section Code

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The reader `&mut &[u8]` at `r`: the slice `(q, m)`. -/
def rdr (n : Nat) (r q m : UInt32) : IProp GF := iprop(n ↦[wms][ r.toNat ] (bytes32 q ++ bytes32 m))

/-- The code the readers run (persistent). -/
def rdCode (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) : IProp GF :=
  iprop(inst ↪[inst] mi ∗ A 361 ↪[wf] FuncInst.wasm types[39]! inst f361 ∗
    A 362 ↪[wf] FuncInst.wasm types[39]! inst f362 ∗ A 694 ↪[wf] FuncInst.wasm types[31]! inst f694 ∗
    A 710 ↪[wf] FuncInst.wasm types[31]! inst f710 ∗ A 764 ↪[wf] FuncInst.wasm types[14]! inst f764 ∗
    A 765 ↪[wf] FuncInst.wasm types[30]! inst f765)

instance (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) : Persistent (rdCode (GF := GF) inst mi A) := by
  unfold rdCode; infer_instance

theorem stk_bytes' {n a k : Nat} : stk (GF := GF) n a k ⊢ ∃ bs : List UInt8, ⌜bs.length = k⌝ ∗ n ↦[wms][ a ] bs := by
  iintro H; iunfold stk at H; iexact H

end Code

/-! ## `u128` (372) -/

section U128

variable {GF : BundledGFunctors} [WasmGS NearState GF]

def pre372 (n g : Nat) (gt : GlobalType) (s out r q m : UInt32) (ob0 ob8 ob16 b0 b1 : List UInt8)
    (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 out, .i32 r]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 48) 48 ∗ rdr n r q m ∗
    n ↦[wms][ out.toNat ] ob0 ∗ n ↦[wms][ out.toNat + 8 ] ob8 ∗ n ↦[wms][ out.toNat + 16 ] ob16 ∗
    n ↦[wms][ q.toNat ] b0 ∗ n ↦[wms][ q.toNat + 8 ] b1)

def post372 (n g : Nat) (gt : GlobalType) (s out r q m : UInt32) (b0 b1 : List UInt8)
    (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 48) 48 ∗ rdr n r (q + 16) (m - 16) ∗
    n ↦[i32][ out.toNat ] 0 ∗ n ↦[wms][ out.toNat + 8 ] b0 ∗ n ↦[wms][ out.toNat + 16 ] b1 ∗
    n ↦[wms][ q.toNat ] b0 ∗ n ↦[wms][ q.toNat + 8 ] b1)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **`u128::deserialize_reader`** (372) on the 16 bytes `b0 ++ b1` at `q` (`16 ≤ m`). -/
theorem f372_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 1 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s out r q m : UInt32) (ob0 ob8 ob16 b0 b1 : List UInt8)
    (hob0 : ob0.length = 4) (hob8 : ob8.length = 8) (hob16 : ob16.length = 8)
    (hb0 : b0.length = 8) (hb1 : b1.length = 8) (hs : 48 ≤ s.toNat) (hm16 : 16 ≤ m.toNat)
    (hq : q.toNat + 16 ≤ 2 ^ 32) (hout : out.toNat + 24 ≤ 2 ^ 32) (hr : r.toNat + 8 ≤ 2 ^ 32) :
    rdCode inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f372 Cg
        (pre372 n g gt s out r q m ob0 ob8 ob16 b0 b1)
        (fun _ => 154 * cfg.regularOpCost)
        (post372 n g gt s out r q m b0 b1) := by
  iintro #Hcode
  iunfold rdCode at Hcode
  icases Hcode with ⟨#Hi, #H361, #H362, #H694, -⟩
  have hn := hm.mem
  have hg := hm.glob
  have ha361 := hm.funcs 361 (by decide)
  have ha362 := hm.funcs 362 (by decide)
  have ha694 := hm.funcs 694 (by decide)
  have t39 : types[39]!.params.length = 5 := by rfl
  have t31 : types[31]!.params.length = 3 := by rfl
  have hlt := s.toNat_lt
  have h48 : (s - 48).toNat = s.toNat - 48 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have e8 : (s - 48 + 8).toNat = s.toNat - 40 := by simp [UInt32.toNat_add, h48]; omega
  have e16 : (s - 48 + 16).toNat = s.toNat - 32 := by simp [UInt32.toNat_add, h48]; omega
  have hm15 : (15 : UInt32) < m := UInt32.lt_iff_toNat_lt.mpr (by simp; omega)
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold pre372 at HP
  icases HP with ⟨%hargs, Hg, Hs, Hr, Ho0, Ho8, Ho16, B0, B1⟩
  subst hargs
  iunfold rdr at Hr
  ihave Hr := KeyGet.split64 n r.toNat q m $$ Hr
  icases Hr with ⟨Rq, Rm⟩
  -- the frame: [sp, 8) [sp+8, 8) [sp+16, 1) [sp+17, 8) [sp+25, 8) [sp+33, 15)
  icases stk_split n (s.toNat - 48) 8 40 $$ Hs with ⟨S0, Hs⟩
  icases stk_split n (s.toNat - 48 + 8) 8 32 $$ Hs with ⟨S8, Hs⟩
  icases stk_split n (s.toNat - 48 + 8 + 8) 1 31 $$ Hs with ⟨S16, Hs⟩
  icases stk_split n (s.toNat - 48 + 8 + 8 + 1) 8 23 $$ Hs with ⟨S17, Hs⟩
  icases stk_split n (s.toNat - 48 + 8 + 8 + 1 + 8) 8 15 $$ Hs with ⟨S25, S33⟩
  rw [show s.toNat - 48 + 8 = s.toNat - 40 by omega, show s.toNat - 40 + 8 = s.toNat - 32 by omega,
    show s.toNat - 32 + 1 = s.toNat - 31 by omega, show s.toNat - 31 + 8 = s.toNat - 23 by omega,
    show s.toNat - 23 + 8 = s.toNat - 15 by omega]
  icases stk_bytes' $$ S0 with ⟨%c0, %hc0, S0⟩
  icases stk_bytes' $$ S8 with ⟨%c8, %hc8, S8⟩
  icases stk_bytes' $$ S16 with ⟨%c16, %hc16, S16⟩
  icases stk_bytes' $$ S17 with ⟨%c17, %hc17, S17⟩
  icases stk_bytes' $$ S25 with ⟨%c25, %hc25, S25⟩
  simp only [f372]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep; mstep; mstep; mstep [Rm]; mstep; mstep; mstep
  mstep with simp [Numeric.bool, Numeric.irelop32, hm15]
  mstep; mstep; mstep; mstep; mstep [Rq]; mstep; mstep; mstep
  mcall (f362_spec cfg lim (d + 1) types[39]! (by rfl) inst mi n hn Cg (s - 48 + 8) q m 16 c8 hc8 (by simp; omega))
    using [S8]
  · iunfold pre36x
    ihave S8 := memBytes_addr (show s.toNat - 40 = (s - 48 + 8).toNat by omega) $$ S8
    iframe S8
    ipureintro; exact ⟨_, rfl⟩
  iunfold post36x at HQ
  icases HQ with ⟨%hrs, S8, S12⟩
  subst hrs
  mstep; mstep; mstep; mstep; mstep [S8]; mstep; mstep [S12]
  mcall (f694_spec cfg lim (d + 1) types[31]! (by rfl) inst mi n hn Cg (s - 48 + 16) q c16 c17 c25 b0 b1
      hc16 hc17 hc25 hb0 hb1 (by omega) hq) using [S16 S17 S25 B0 B1]
  · iunfold pre694
    ihave S16 := memBytes_addr (show s.toNat - 32 = (s - 48 + 16).toNat by omega) $$ S16
    ihave S17 := memBytes_addr (show s.toNat - 31 = (s - 48 + 16).toNat + 1 by omega) $$ S17
    ihave S25 := memBytes_addr (show s.toNat - 23 = (s - 48 + 16).toNat + 9 by omega) $$ S25
    iframe S16 S17 S25 B0 B1
    ipureintro; rfl
  iunfold post694 at HQ
  icases HQ with ⟨%hrs, S16, S17, S25, B0, B1⟩
  subst hrs
  mstep; mstep [S16]
  mstep; mstep; mstep
  mstep; mstep; mstep; mstep [S25]; mstep
  mstep; mstep [S17]; mstep
  mstep; mstep; mstep [Rq]; mstep; mstep [Rm]; mstep; mstep
  mcall (f361_spec cfg lim (d + 1) types[39]! (by rfl) inst mi n hn Cg (s - 48) q m 16 c0 hc0 (by simp; omega))
    using [S0]
  · iunfold pre36x
    ihave S0 := memBytes_addr (show s.toNat - 48 = (s - 48).toNat by omega) $$ S0
    iframe S0
    ipureintro; exact ⟨_, rfl⟩
  iunfold post36x at HQ
  icases HQ with ⟨%hrs, S0, S4⟩
  subst hrs
  ihave S0 := KeyGet.join64 n (s - 48).toNat (q + 16) (m - 16) $$ [S0 S4]
  · iframe S0 S4
  mstep; mstep [S0]
  rw [ofNat_decode_pair]
  mstep
  mstep; mstep; mstep; mstep; mstep [Ho16]
  mstep; mstep; mstep; mstep; mstep [Ho8]
  ihave Rr := KeyGet.join64 n r.toNat q m $$ [Rq Rm]
  · iframe Rq Rm
  mstep; mstep; mstep [Rr]
  rw [storeBytes_pair64, storeBytes_i64_decode b0 hb0, storeBytes_i64_decode b1 hb1]
  mstep; mstep
  mstep; mstep; mstep [Ho0]
  mstep; mstep; mstep; mstep [Hg]
  rw [show s - 48 + 48 = s by simp]
  mstep
  mcredits R
  iframe Hc
  iunfold post372, rdr
  iframe Hg Rr Ho0 Ho8 Ho16 B0 B1
  isplitr
  · ipureintro; simp [htype]
  ihave S0 := KeyGet.split64 n (s - 48).toNat (q + 16) (m - 16) $$ S0
  icases S0 with ⟨S0, S4⟩
  ihave S0 := stk_word n _ _ $$ S0
  ihave S4 := stk_word n _ _ $$ S4
  ihave S0 := stk_join n _ 4 4 $$ [S0 S4]
  · iframe S0 S4
  ihave S8 := stk_word n _ _ $$ S8
  ihave S12 := stk_word n _ _ $$ S12
  ihave S8 := stk_join n _ 4 4 $$ [S8 S12]
  · iframe S8 S12
  ihave S8 := stk_addr (show (s - 48 + 8).toNat = s.toNat - 40 by omega) $$ S8
  ihave S0 := stk_addr (show (s - 48).toNat = s.toNat - 48 by omega) $$ S0
  ihave S16 := ReadRegister.stk_bytes n _ [0] 1 rfl $$ S16
  ihave S17 := ReadRegister.stk_bytes n _ b0 8 hb0 $$ S17
  ihave S25 := ReadRegister.stk_bytes n _ b1 8 hb1 $$ S25
  ihave S16 := stk_addr (show (s - 48 + 16).toNat = s.toNat - 32 by omega) $$ S16
  ihave S17 := stk_addr (show (s - 48 + 16).toNat + 1 = s.toNat - 31 by omega) $$ S17
  ihave S25 := stk_addr (show (s - 48 + 16).toNat + 9 = s.toNat - 23 by omega) $$ S25
  ihave S25 := stk_join n (s.toNat - 23) 8 15 $$ [S25 S33]
  · rw [show s.toNat - 23 + 8 = s.toNat - 15 by omega]; iframe S25 S33
  ihave S17 := stk_join n (s.toNat - 31) 8 23 $$ [S17 S25]
  · rw [show s.toNat - 31 + 8 = s.toNat - 23 by omega]; iframe S17 S25
  ihave S16 := stk_join n (s.toNat - 32) 1 31 $$ [S16 S17]
  · rw [show s.toNat - 32 + 1 = s.toNat - 31 by omega]; iframe S16 S17
  ihave S8 := stk_join n (s.toNat - 40) 8 32 $$ [S8 S16]
  · rw [show s.toNat - 40 + 8 = s.toNat - 32 by omega]; iframe S8 S16
  iapply stk_join n (s.toNat - 48) 8 40
  rw [show s.toNat - 48 + 8 = s.toNat - 40 by omega]
  iframe S0 S8

end U128

/-! ## `u64` (371) -/

section U64

variable {GF : BundledGFunctors} [WasmGS NearState GF]

def pre371 (n g : Nat) (gt : GlobalType) (s out r q m : UInt32) (ob0 ob8 b0 : List UInt8)
    (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 out, .i32 r]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 48) 48 ∗ rdr n r q m ∗
    n ↦[wms][ out.toNat ] ob0 ∗ n ↦[wms][ out.toNat + 8 ] ob8 ∗ n ↦[wms][ q.toNat ] b0)

def post371 (n g : Nat) (gt : GlobalType) (s out r q m : UInt32) (b0 : List UInt8)
    (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 48) 48 ∗ rdr n r (q + 8) (m - 8) ∗
    n ↦[i32][ out.toNat ] 0 ∗ n ↦[wms][ out.toNat + 8 ] b0 ∗ n ↦[wms][ q.toNat ] b0)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **`u64::deserialize_reader`** (371) on the 8 bytes `b0` at `q` (`8 ≤ m`). -/
theorem f371_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 1 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s out r q m : UInt32) (ob0 ob8 b0 : List UInt8)
    (hob0 : ob0.length = 4) (hob8 : ob8.length = 8)
    (hb0 : b0.length = 8) (hs : 48 ≤ s.toNat) (hm8 : 8 ≤ m.toNat)
    (hq : q.toNat + 8 ≤ 2 ^ 32) (hout : out.toNat + 16 ≤ 2 ^ 32) (hr : r.toNat + 8 ≤ 2 ^ 32) :
    rdCode inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f371 Cg
        (pre371 n g gt s out r q m ob0 ob8 b0)
        (fun _ => 138 * cfg.regularOpCost)
        (post371 n g gt s out r q m b0) := by
  iintro #Hcode
  iunfold rdCode at Hcode
  icases Hcode with ⟨#Hi, #H361, #H362, -, #H710, -⟩
  have hn := hm.mem
  have hg := hm.glob
  have ha361 := hm.funcs 361 (by decide)
  have ha362 := hm.funcs 362 (by decide)
  have ha710 := hm.funcs 710 (by decide)
  have t39 : types[39]!.params.length = 5 := by rfl
  have t31 : types[31]!.params.length = 3 := by rfl
  have hlt := s.toNat_lt
  have h48 : (s - 48).toNat = s.toNat - 48 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have e8 : (s - 48 + 8).toNat = s.toNat - 40 := by simp [UInt32.toNat_add, h48]; omega
  have e16 : (s - 48 + 16).toNat = s.toNat - 32 := by simp [UInt32.toNat_add, h48]; omega
  have e24 : (s - 48 + 24).toNat = s.toNat - 24 := by simp [UInt32.toNat_add, h48]; omega
  have hm7 : (7 : UInt32) < m := UInt32.lt_iff_toNat_lt.mpr (by simp; omega)
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold pre371 at HP
  icases HP with ⟨%hargs, Hg, Hs, Hr, Ho0, Ho8, B0⟩
  subst hargs
  iunfold rdr at Hr
  ihave Hr := KeyGet.split64 n r.toNat q m $$ Hr
  icases Hr with ⟨Rq, Rm⟩
  -- the frame: [sp, 8) [sp+8, 8) [sp+16, 8) [sp+24, 1) [sp+25, 8) [sp+33, 15)
  icases stk_split n (s.toNat - 48) 8 40 $$ Hs with ⟨S0, Hs⟩
  icases stk_split n (s.toNat - 48 + 8) 8 32 $$ Hs with ⟨S8, Hs⟩
  icases stk_split n (s.toNat - 48 + 8 + 8) 8 24 $$ Hs with ⟨S16, Hs⟩
  icases stk_split n (s.toNat - 48 + 8 + 8 + 8) 1 23 $$ Hs with ⟨S24, Hs⟩
  icases stk_split n (s.toNat - 48 + 8 + 8 + 8 + 1) 8 15 $$ Hs with ⟨S25, S33⟩
  rw [show s.toNat - 48 + 8 = s.toNat - 40 by omega, show s.toNat - 40 + 8 = s.toNat - 32 by omega,
    show s.toNat - 32 + 8 = s.toNat - 24 by omega, show s.toNat - 24 + 1 = s.toNat - 23 by omega,
    show s.toNat - 23 + 8 = s.toNat - 15 by omega]
  icases stk_bytes' $$ S8 with ⟨%c8, %hc8, S8⟩
  icases stk_bytes' $$ S16 with ⟨%c16, %hc16, S16⟩
  icases stk_bytes' $$ S24 with ⟨%c24, %hc24, S24⟩
  icases stk_bytes' $$ S25 with ⟨%c25, %hc25, S25⟩
  simp only [f371]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep; mstep; mstep; mstep [Rm]; mstep; mstep; mstep
  mstep with simp [Numeric.bool, Numeric.irelop32, hm7]
  mstep; mstep; mstep; mstep; mstep [Rq]; mstep; mstep; mstep
  mcall (f362_spec cfg lim (d + 1) types[39]! (by rfl) inst mi n hn Cg (s - 48 + 16) q m 8 c16 hc16 (by simp; omega))
    using [S16]
  · iunfold pre36x
    ihave S16 := memBytes_addr (show s.toNat - 32 = (s - 48 + 16).toNat by omega) $$ S16
    iframe S16
    ipureintro; exact ⟨_, rfl⟩
  iunfold post36x at HQ
  icases HQ with ⟨%hrs, S16, S20⟩
  subst hrs
  mstep; mstep; mstep; mstep; mstep [S16]; mstep; mstep [S20]
  mcall (f710_spec cfg lim (d + 1) types[31]! (by rfl) inst mi n hn Cg (s - 48 + 24) q c24 c25 b0
      hc24 hc25 hb0 (by omega) hq) using [S24 S25 B0]
  · iunfold pre710
    ihave S24 := memBytes_addr (show s.toNat - 24 = (s - 48 + 24).toNat by omega) $$ S24
    ihave S25 := memBytes_addr (show s.toNat - 23 = (s - 48 + 24).toNat + 1 by omega) $$ S25
    iframe S24 S25 B0
    ipureintro; rfl
  iunfold post710 at HQ
  icases HQ with ⟨%hrs, S24, S25, B0⟩
  subst hrs
  mstep; mstep [S24]
  mstep; mstep; mstep
  mstep; mstep [S25]; mstep
  mstep; mstep; mstep; mstep; mstep [Rq]; mstep; mstep [Rm]; mstep; mstep
  mcall (f361_spec cfg lim (d + 1) types[39]! (by rfl) inst mi n hn Cg (s - 48 + 8) q m 8 c8 hc8 (by simp; omega))
    using [S8]
  · iunfold pre36x
    ihave S8 := memBytes_addr (show s.toNat - 40 = (s - 48 + 8).toNat by omega) $$ S8
    iframe S8
    ipureintro; exact ⟨_, rfl⟩
  iunfold post36x at HQ
  icases HQ with ⟨%hrs, S8, S12⟩
  subst hrs
  ihave S8 := KeyGet.join64 n (s - 48 + 8).toNat (q + 8) (m - 8) $$ [S8 S12]
  · iframe S8 S12
  mstep; mstep [S8]
  rw [ofNat_decode_pair]
  mstep
  mstep; mstep; mstep; mstep; mstep [Ho8]
  ihave Rr := KeyGet.join64 n r.toNat q m $$ [Rq Rm]
  · iframe Rq Rm
  mstep; mstep; mstep [Rr]
  rw [storeBytes_pair64, storeBytes_i64_decode b0 hb0]
  mstep; mstep
  mstep; mstep; mstep [Ho0]
  mstep; mstep; mstep; mstep [Hg]
  rw [show s - 48 + 48 = s by simp]
  mstep
  mcredits R
  iframe Hc
  iunfold post371, rdr
  iframe Hg Rr Ho0 Ho8 B0
  isplitr
  · ipureintro; simp [htype]
  ihave S8 := KeyGet.split64 n (s - 48 + 8).toNat (q + 8) (m - 8) $$ S8
  icases S8 with ⟨S8, S12⟩
  ihave S8 := stk_word n _ _ $$ S8
  ihave S12 := stk_word n _ _ $$ S12
  ihave S8 := stk_join n _ 4 4 $$ [S8 S12]
  · iframe S8 S12
  ihave S8 := stk_addr (show (s - 48 + 8).toNat = s.toNat - 40 by omega) $$ S8
  ihave S16 := stk_word n _ _ $$ S16
  ihave S20 := stk_word n _ _ $$ S20
  ihave S16 := stk_join n _ 4 4 $$ [S16 S20]
  · iframe S16 S20
  ihave S16 := stk_addr (show (s - 48 + 16).toNat = s.toNat - 32 by omega) $$ S16
  ihave S24 := ReadRegister.stk_bytes n _ [0] 1 rfl $$ S24
  ihave S25 := ReadRegister.stk_bytes n _ b0 8 hb0 $$ S25
  ihave S24 := stk_addr (show (s - 48 + 24).toNat = s.toNat - 24 by omega) $$ S24
  ihave S25 := stk_addr (show (s - 48 + 24).toNat + 1 = s.toNat - 23 by omega) $$ S25
  ihave S25 := stk_join n (s.toNat - 23) 8 15 $$ [S25 S33]
  · rw [show s.toNat - 23 + 8 = s.toNat - 15 by omega]; iframe S25 S33
  ihave S24 := stk_join n (s.toNat - 24) 1 23 $$ [S24 S25]
  · rw [show s.toNat - 24 + 1 = s.toNat - 23 by omega]; iframe S24 S25
  ihave S16 := stk_join n (s.toNat - 32) 8 24 $$ [S16 S24]
  · rw [show s.toNat - 32 + 8 = s.toNat - 24 by omega]; iframe S16 S24
  ihave S8 := stk_join n (s.toNat - 40) 8 32 $$ [S8 S16]
  · rw [show s.toNat - 40 + 8 = s.toNat - 32 by omega]; iframe S8 S16
  iapply stk_join n (s.toNat - 48) 8 40
  rw [show s.toNat - 48 + 8 = s.toNat - 40 by omega]
  iframe S0 S8

end U64

end WNear.Binary.BorshInt
