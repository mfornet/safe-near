import Binary.Code
import Bridge.Functions.KeyGet
import Bridge.Functions.VecDeref
import Bridge.Functions.U128From
import NearLogic.Tactic.Control

/-!
# The leaves of Borsh's slice reader

```wat
;; 362 split_at (out, ptr, len, k, loc): len < k → panic; out := (ptr, k)         (the head)
;; 361 split_at (out, ptr, len, k, loc): len < k → panic; out := (ptr + k, len - k) (the tail)
;; 765 <[u8; 4]>::try_from (p, l) -> i64: l = 4 → (load32 p) << 8 (tag 0); else tag 1
;; 764 Ok(n) (out, n): out := (0, n)
;; 694 <[u8; 16]>::try_from (out, p, l): l = 16 → out.0 := 0 (byte), out.1.. := the 16 bytes
;; 710 <[u8; 8]>::try_from  (out, p, l): l = 8  → out.0 := 0 (byte), out.1.. := the 8 bytes
```

The arrays are copied with unaligned `i64` loads and stores (`storeBytes_w64`).
-/

namespace WNear.Binary.BorshLeaves

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic

/-! ## Eight bytes through an `i64` -/

/-- Eight bytes as the `u64` an `i64` load reads. -/
def w64 (bs : List UInt8) : UInt64 := UInt64.ofNat (Memory.decodeLE bs)

theorem storeBytes_w64 (bs : List UInt8) (h : bs.length = 8) : storeBytes (.i64 (w64 bs)) 8 = bs := by
  match bs, h with
  | [a, b, c, d, e, f, g, k], _ =>
    have ha := a.toNat_lt; have hb := b.toNat_lt; have hc := c.toNat_lt; have hd := d.toNat_lt
    have he := e.toNat_lt; have hf := f.toNat_lt; have hg := g.toNat_lt; have hk := k.toNat_lt
    simp only [w64, storeBytes, storeRaw, Memory.decodeLE, List.foldr, List.range,
      List.range.loop, List.map, Nat.shiftRight_eq_div_pow, List.cons.injEq, and_true]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (apply UInt8.toNat_inj.mp; simp <;> omega)

theorem storeBytes_i64_decode (bs : List UInt8) (h : bs.length = 8) :
    storeBytes (.i64 (UInt64.ofNat (Memory.decodeLE bs))) 8 = bs := storeBytes_w64 bs h

theorem storeBytes_i32_zero1 : storeBytes (.i32 0) 1 = [0] := rfl

section Leaves

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-! ## `split_at` (362, 361) -/

def pre36x (n : Nat) (out ptr len k : UInt32) (ob : List UInt8) (args : List Value) : IProp GF :=
  iprop(⌜∃ loc : UInt32, args = [.i32 out, .i32 ptr, .i32 len, .i32 k, .i32 loc]⌝ ∗ n ↦[wms][ out.toNat ] ob)

def post36x (n : Nat) (out a b : UInt32) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = []⌝ ∗ n ↦[i32][ out.toNat ] a ∗ n ↦[i32][ out.toNat + 4 ] b)

/-- The head of `split_at(k)` (362), `k ≤ len`: `(ptr, k)` at `out`. -/
theorem f362_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (n : Nat)
    (hn : mi.memAddrs[0]? = some n) (Cg : Nat) (out ptr len k : UInt32) (ob : List UInt8)
    (hob : ob.length = 8) (hk : k.toNat ≤ len.toNat) :
    ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f362 Cg (pre36x n out ptr len k ob)
        (fun _ => 10 * cfg.regularOpCost) (post36x n out ptr k) := by
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold pre36x at HP
  icases HP with ⟨%⟨loc, hargs⟩, Ho⟩
  subst hargs
  ihave Ho := U128From.memBytes_split n out.toNat 4 ob (by omega) $$ Ho
  icases Ho with ⟨Ho0, Ho4⟩
  have hge : k ≤ len := UInt32.le_iff_toNat_le.mpr hk
  simp only [f362]
  mstep; mstep; mstep; mstep
  mstep with simp [Numeric.bool, Numeric.irelop32, hge]
  mstep; mstep; mstep [Ho4]
  mstep; mstep; mstep [Ho0]
  mcredits R
  iframe Hc
  iunfold post36x
  iframe Ho0 Ho4
  ipureintro; simp [htype]

/-- The tail of `split_at(k)` (361), `k ≤ len`: `(ptr + k, len - k)` at `out`. -/
theorem f361_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (n : Nat)
    (hn : mi.memAddrs[0]? = some n) (Cg : Nat) (out ptr len k : UInt32) (ob : List UInt8)
    (hob : ob.length = 8) (hk : k.toNat ≤ len.toNat) :
    ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f361 Cg (pre36x n out ptr len k ob)
        (fun _ => 14 * cfg.regularOpCost) (post36x n out (ptr + k) (len - k)) := by
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold pre36x at HP
  icases HP with ⟨%⟨loc, hargs⟩, Ho⟩
  subst hargs
  ihave Ho := U128From.memBytes_split n out.toNat 4 ob (by omega) $$ Ho
  icases Ho with ⟨Ho0, Ho4⟩
  have hge : k ≤ len := UInt32.le_iff_toNat_le.mpr hk
  simp only [f361]
  mstep; mstep; mstep; mstep
  mstep with simp [Numeric.bool, Numeric.irelop32, hge]
  mstep; mstep; mstep; mstep; mstep [Ho4]
  mstep; mstep; mstep; mstep; mstep [Ho0]
  mcredits R
  iframe Hc
  iunfold post36x
  iframe Ho0 Ho4
  ipureintro; simp [htype]

/-! ## `Ok(n)` (764) -/

def pre764 (n : Nat) (out v : UInt32) (ob : List UInt8) (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 out, .i32 v]⌝ ∗ n ↦[wms][ out.toNat ] ob)

theorem f764_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (n : Nat)
    (hn : mi.memAddrs[0]? = some n) (Cg : Nat) (out v : UInt32) (ob : List UInt8)
    (hob : ob.length = 8) :
    ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f764 Cg (pre764 n out v ob)
        (fun _ => 6 * cfg.regularOpCost) (post36x n out 0 v) := by
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold pre764 at HP
  icases HP with ⟨%hargs, Ho⟩
  subst hargs
  ihave Ho := U128From.memBytes_split n out.toNat 4 ob (by omega) $$ Ho
  icases Ho with ⟨Ho0, Ho4⟩
  simp only [f764]
  mstep; mstep; mstep [Ho4]
  mstep; mstep; mstep [Ho0]
  mcredits R
  iframe Hc
  iunfold post36x
  iframe Ho0 Ho4
  ipureintro; simp [htype]

/-! ## `<[u8; 4]>::try_from` (765) -/

/-- What 765 returns for the four bytes `bs`: the `u32` shifted by 8 (tag 0). -/
def r765 (bs : List UInt8) : UInt64 := UInt64.ofNat (Memory.decodeLE bs * 256)

def pre765 (n : Nat) (p : UInt32) (bs : List UInt8) (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 p, .i32 4]⌝ ∗ n ↦[wms][ p.toNat ] bs)

def post765 (n : Nat) (p : UInt32) (bs : List UInt8) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = [.i64 (r765 bs)]⌝ ∗ n ↦[wms][ p.toNat ] bs)

theorem decodeLE_lt4 (bs : List UInt8) (h : bs.length = 4) : Memory.decodeLE bs < 2 ^ 32 := by
  match bs, h with
  | [a, b, c, d], _ =>
    have ha := a.toNat_lt; have hb := b.toNat_lt; have hc := c.toNat_lt; have hd := d.toNat_lt
    simp only [Memory.decodeLE, List.foldr]
    omega

theorem f765_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = [.i64]) (inst : Nat) (mi : ModuleInst) (n : Nat)
    (hn : mi.memAddrs[0]? = some n) (Cg : Nat) (p : UInt32) (bs : List UInt8) (hbs : bs.length = 4) :
    ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f765 Cg (pre765 n p bs)
        (fun _ => 16 * cfg.regularOpCost) (post765 n p bs) := by
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold pre765 at HP
  icases HP with ⟨%hargs, Hp⟩
  subst hargs
  simp only [f765]
  mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep [Hp]
  mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
  mstep
  mcredits R
  iframe Hc
  iunfold post765
  iframe Hp
  ipureintro
  have hl := decodeLE_lt4 bs hbs
  rw [htype]
  simp only [List.length_singleton, Nat.sub_self, List.drop_zero, List.cons.injEq, Value.i64.injEq, and_true]
  apply UInt64.toNat_inj.mp
  simp [r765, UInt64.toNat_shiftLeft, UInt64.toNat_ofNat, Nat.shiftLeft_eq]
  omega

/-! ## `<[u8; 16]>::try_from` (694) and `<[u8; 8]>::try_from` (710) -/

def pre694 (n : Nat) (out p : UInt32) (o0 o1 o2 b0 b1 : List UInt8) (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 out, .i32 p, .i32 16]⌝ ∗ n ↦[wms][ out.toNat ] o0 ∗ n ↦[wms][ out.toNat + 1 ] o1 ∗
    n ↦[wms][ out.toNat + 9 ] o2 ∗ n ↦[wms][ p.toNat ] b0 ∗ n ↦[wms][ p.toNat + 8 ] b1)

def post694 (n : Nat) (out p : UInt32) (b0 b1 : List UInt8) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = []⌝ ∗ n ↦[wms][ out.toNat ] [0] ∗ n ↦[wms][ out.toNat + 1 ] b0 ∗
    n ↦[wms][ out.toNat + 9 ] b1 ∗ n ↦[wms][ p.toNat ] b0 ∗ n ↦[wms][ p.toNat + 8 ] b1)

/-- `<[u8; 16]>::try_from` (694) on 16 bytes `b0 ++ b1`: `Ok` (tag byte 0) and the array at
`out + 1`. -/
theorem f694_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (n : Nat)
    (hn : mi.memAddrs[0]? = some n) (Cg : Nat) (out p : UInt32) (o0 o1 o2 b0 b1 : List UInt8)
    (ho0 : o0.length = 1) (ho1 : o1.length = 8) (ho2 : o2.length = 8) (hb0 : b0.length = 8) (hb1 : b1.length = 8)
    (hout : out.toNat + 17 ≤ 2 ^ 32) (hp : p.toNat + 16 ≤ 2 ^ 32) :
    ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f694 Cg (pre694 n out p o0 o1 o2 b0 b1)
        (fun _ => 23 * cfg.regularOpCost) (post694 n out p b0 b1) := by
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold pre694 at HP
  icases HP with ⟨%hargs, O0, O1, O2, B0, B1⟩
  subst hargs
  simp only [f694]
  mstep; mstep; mstep; mstep; mstep; mstep; mstep
  mstep; mstep; mstep [B0]; mstep [O1]
  mstep; mstep; mstep; mstep; mstep; mstep; mstep [B1]; mstep [O2]
  mstep; mstep; mstep; mstep; mstep [O0]
  rw [storeBytes_i64_decode b0 hb0, storeBytes_i64_decode b1 hb1, storeBytes_i32_zero1]
  mcredits R
  iframe Hc
  iunfold post694
  iframe O0 O1 O2 B0 B1
  ipureintro; simp [htype]

def pre710 (n : Nat) (out p : UInt32) (o0 o1 b0 : List UInt8) (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 out, .i32 p, .i32 8]⌝ ∗ n ↦[wms][ out.toNat ] o0 ∗ n ↦[wms][ out.toNat + 1 ] o1 ∗
    n ↦[wms][ p.toNat ] b0)

def post710 (n : Nat) (out p : UInt32) (b0 : List UInt8) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = []⌝ ∗ n ↦[wms][ out.toNat ] [0] ∗ n ↦[wms][ out.toNat + 1 ] b0 ∗ n ↦[wms][ p.toNat ] b0)

/-- `<[u8; 8]>::try_from` (710) on 8 bytes: `Ok` (tag byte 0) and the array at `out + 1`. -/
theorem f710_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (n : Nat)
    (hn : mi.memAddrs[0]? = some n) (Cg : Nat) (out p : UInt32) (o0 o1 b0 : List UInt8)
    (ho0 : o0.length = 1) (ho1 : o1.length = 8) (hb0 : b0.length = 8)
    (hout : out.toNat + 9 ≤ 2 ^ 32) (hp : p.toNat + 8 ≤ 2 ^ 32) :
    ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f710 Cg (pre710 n out p o0 o1 b0)
        (fun _ => 15 * cfg.regularOpCost) (post710 n out p b0) := by
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold pre710 at HP
  icases HP with ⟨%hargs, O0, O1, B0⟩
  subst hargs
  simp only [f710]
  mstep; mstep; mstep; mstep; mstep; mstep; mstep
  mstep; mstep; mstep [B0]; mstep [O1]
  mstep; mstep; mstep; mstep; mstep [O0]
  rw [storeBytes_i64_decode b0 hb0, storeBytes_i32_zero1]
  mcredits R
  iframe Hc
  iunfold post710
  iframe O0 O1 B0
  ipureintro; simp [htype]

end Leaves

end WNear.Binary.BorshLeaves
