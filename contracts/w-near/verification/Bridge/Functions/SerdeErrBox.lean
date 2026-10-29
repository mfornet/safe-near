import Bridge.Functions.SerdePosition
import Bridge.Functions.VecWithCap
import Bridge.Functions.FromUtf8Gen

/-!
# serde_json's error box (M6): `Box<ErrorImpl>` through the allocator

serde_json reports a syntax error (`EofWhileParsingString`, `ControlCharacterWhileParsingString`,
`InvalidUnicodeCodePoint`, …) through `Deserializer::error` (647; 657 is the same code, `f657_eq`):

```wat
;; 647 error(out, rd, code)       a 32-byte frame
(line, col) := position(rd)      ;; 638 → 645 (`SerdePosition`), linear in the index
e := *code                       ;; the 12-byte ErrorCode, copied to the frame
box := Error::syntax(e, line, col)
out := (1, box)                  ;; Err
;; 639 Error::syntax(e, line, col)  box := exchange_malloc(20) (590); box := (e, line, col)
;; 590 exchange_malloc(size)        624(size, 4); 0 → handle_alloc_error (842, not reached)
;; 624 Global::allocate             625(size, 4, false) in a 16-byte frame
;; 625 alloc_impl(out, size, al, z) __rust_alloc(size, al) (310); 0 → 726 (not reached)
```

The reject paths need only some finite cost, so the specification is loose: the result is `Err` with
a fresh 20-byte block whose contents are left open, and the cost is `costErr cfg F i`: the
position's `cost638 i` (linear in the index `i`), a constant, and the allocator's
`AllocWalk.cost310W cfg F 20 4` on a free list of any length `F`.

* `heapR`, `heapA`: the heap after an allocation, the block aside or with it.
* `f625_spec`, `f624_spec`, `f590_spec`: the allocation at alignment 4, through
  `AllocWalk.f310_spec_walk`, with room under the memory limit (`roomFor4`).
* `f639_spec`: the box, filled (`block_split20`, `block_join20`).
* `f647_spec`: `Err(box)` at `out`, the stack (80 bytes), the reader and the `ErrorCode` kept, at
  `costErr cfg F i`. The code it runs is `errCode`.
* `f648_spec_bad`: `as_str` on bytes of the input that are not UTF-8 (`utf8Ok` false): `from_utf8`
  (927, `FromUtf8Gen.f927_spec`) fails, and the error is `InvalidUnicodeCodePoint` (code 14) through
  657: `Err(box)`, at `(60 + cost927 len) · c + costErr cfg F i`, a 112-byte stack.

*Tactic note.* After an `mcall`, bring the credits to the `k * c + X` form (`mcredits`) before the
next `mstep`: stepping on the subtraction the call leaves sent the kernel into a deep recursion.
-/

namespace WNear.Binary.SerdeErrBox

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.AllocNewCell (cellPages)
open WNear.Binary.AllocAlloc (wordsOf)
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.AllocTwo (code310)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_intro stk_word stk_open581 stk_close581 stk_addr)

/-- Room for an allocation of `size` bytes at alignment 4 on a heap of length `len`, under `maxP`. -/
def roomFor4 (len maxP : Nat) (size : UInt32) : Prop :=
  len % 65536 = 0 ∧ 0 < len ∧ len + (cellPages (wordsOf size) 4).toNat * 65536 + 65536 ≤ 2 ^ 32 ∧
    (len + (cellPages (wordsOf size) 4).toNat * 65536) / 65536 ≤ maxP

section Defs

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The heap after an allocation of `size` bytes at `p`, the block aside: some length `len'` (grown
or not), the block listed as lent, the bound `max F 1`. -/
def heapR (n maxP len : Nat) (live : List (Nat × Nat)) (F : Nat) (size : UInt32) (p : UInt32) : IProp GF :=
  iprop(∃ len', ⌜len' = len ∨ len' = len + (cellPages (wordsOf size) 4).toNat * 65536⌝ ∗
    heapInv n maxP len' ((p.toNat, size.toNat) :: live) (max F 1))

/-- `heapR` and the block itself. -/
def heapA (n maxP len : Nat) (live : List (Nat × Nat)) (F : Nat) (size : UInt32) (p : UInt32) : IProp GF :=
  iprop(heapR n maxP len live F size p ∗ block n p.toNat size.toNat)

end Defs

section L625

variable {GF : BundledGFunctors} [WasmGS NearState GF]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **`Global::alloc_impl(out, size, 4, false)`** (625), `size ≥ 1` with room: `__rust_alloc(size, 4)`
(310), a block `p ≠ 0`, `(p, size)` at `out`. -/
theorem f625_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 6 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp out size idx : UInt32) (maxP len : Nat) (live : List (Nat × Nat)) (F : Nat)
    (ob : List UInt8) (hob : ob.length = 8) (hout : out.toNat + 8 ≤ 2 ^ 32) (hsp : 16 ≤ sp.toNat)
    (hsize : 1 ≤ size.toNat) (hsize2 : size.toNat < 2 ^ 28) (hr : roomFor4 len maxP size) :
    code310 n maxP inst mi A ∗ A 310 ↪[wf] FuncInst.wasm types[13]! inst f310
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f625 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 size, .i32 4, .i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          stk n (sp.toNat - 16) 16 ∗ vt n 1057464 idx ta (A 578) ∗ heapInv n maxP len live F ∗
          n ↦[wms][ out.toNat ] ob))
        (fun _ => 30 * cfg.regularOpCost + AllocWalk.cost310W cfg F size 4)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ ∃ p : UInt32, ⌜p ≠ 0⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          stk n (sp.toNat - 16) 16 ∗ vt n 1057464 idx ta (A 578) ∗ heapA n maxP len live F size p ∗
          n ↦[i32][ out.toNat ] p ∗ n ↦[i32][ out.toNat + 4 ] size)) := by
  iintro ⟨#Hcode, #H310⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold code310 at Hcode
    icases Hcode with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩
    iexact Hi
  obtain ⟨hlen0, hlen1, hroom, hmax⟩ := hr
  have hn := hm.mem
  have ha310 := hm.funcs 310 (by decide)
  have t13 : types[13]!.params.length = 2 := by rfl
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, Hvt, Hinv, Ho⟩
  subst hargs
  icases U128From.memBytes_split n out.toNat 4 ob (by omega) $$ Ho with ⟨Ho0, Ho4⟩
  icases stk_open581 n sp hsp $$ Hs with ⟨%o1, %o2, %o4, %⟨h1, h2, h4⟩, O1, O2, O4, W8⟩
  simp only [f625]
  have hne : size ≠ 0 := fun e => by simp [e] at hsize
  generalize hK : AllocWalk.cost310W cfg F size 4 = K
  mstep; mstep; mstep
  mstep; mstep; mstep; mstep; mstep
  mstep; mstep
  have key := AllocWalk.f310_spec_walk (GF := GF) cfg lim (d + 1) types[13]! (by rfl) inst mi A n g ta hm (by omega)
    Cg gt sp size 4 idx 2 maxP len live F o1 o2 o4 hsp (by simp) (by simp) hsize hsize2 hlen0 hlen1 h1 h2 h4 hroom hmax
  rw [hK] at key
  clear hK
  rw [show 30 * cfg.regularOpCost + K + R = 30 * cfg.regularOpCost + (K + R) by omega]
  mstep; mstep
  mcall key using [Hg O1 O2 O4 Hvt Hinv]
  · iframe Hg O1 O2 O4 Hvt Hinv
  icases HQ with ⟨%p, %⟨hrs, hp0, -⟩, Hg, HO, Hvt, %len', %hl', Hinv, Hb⟩
  subst hrs
  clear key hroom hmax hlen0 hlen1 h1 h2 h4
  ihave HA : heapA n maxP len live F size p $$ [Hinv Hb]
  · iunfold heapA, heapR
    iframe Hb
    iexists len'
    iframe Hinv
    ipureintro; exact hl'
  clear hl'
  have hpc : p ≠ 0 := hp0
  mcredits (11 * cfg.regularOpCost + R)
  mstep; mstep
  iapply mwpi_cons; iapply mwpi_br_if_taken'; isplitr
  · ipureintro; exact ⟨rfl, hpc⟩
  mctrl_norm; repeat mpay
  mstep; mstep; mstep [Ho4]
  mstep; mstep; mstep [Ho0]
  repeat mstep
  isplitl [Hc]
  · iapply BorrowMut.credits_le
    iframe Hc
    ipureintro; omega
  isplitr
  · ipureintro; trivial
  iexists p
  isplitr
  · ipureintro; exact hpc
  iframe Hg Hvt Ho0 Ho4 HA
  iapply stk_close581 n sp hsp
  iframe HO W8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **`RawVec::allocate_in`'s `Global::allocate(out, size, 4)`** (624): 625 in a 16-byte frame, its
`(p, size)` copied to `out`. -/
theorem f624_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 7 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp out size idx : UInt32) (maxP len : Nat) (live : List (Nat × Nat)) (F : Nat)
    (ob : List UInt8) (hob : ob.length = 8) (hout : out.toNat + 8 ≤ 2 ^ 32) (hsp : 32 ≤ sp.toNat)
    (hsize : 1 ≤ size.toNat) (hsize2 : size.toNat < 2 ^ 28) (hr : roomFor4 len maxP size) :
    code310 n maxP inst mi A ∗ A 310 ↪[wf] FuncInst.wasm types[13]! inst f310 ∗
      A 625 ↪[wf] FuncInst.wasm types[45]! inst f625
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f624 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 size, .i32 4]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          stk n (sp.toNat - 32) 32 ∗ vt n 1057464 idx ta (A 578) ∗ heapInv n maxP len live F ∗
          n ↦[wms][ out.toNat ] ob))
        (fun _ => 70 * cfg.regularOpCost + AllocWalk.cost310W cfg F size 4)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ ∃ p : UInt32, ⌜p ≠ 0⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          stk n (sp.toNat - 32) 32 ∗ vt n 1057464 idx ta (A 578) ∗ heapA n maxP len live F size p ∗
          n ↦[i32][ out.toNat ] p ∗ n ↦[i32][ out.toNat + 4 ] size)) := by
  iintro ⟨#Hcode, #H310, #H625⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold code310 at Hcode
    icases Hcode with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩
    iexact Hi
  have hn := hm.mem
  have hg := hm.glob
  have ha625 := hm.funcs 625 (by decide)
  have t45 : types[45]!.params.length = 4 := by rfl
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, Hvt, Hinv, Ho⟩
  subst hargs
  have hlt := sp.toNat_lt
  have h16 : (sp - 16).toNat = sp.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have h8 : (sp - 16 + 8).toNat = (sp - 16).toNat + 8 := by rw [UInt32.toNat_add, h16]; simp; omega
  icases stk_split n (sp.toNat - 32) 16 16 $$ Hs with ⟨S16, Hs⟩
  icases stk_split n (sp.toNat - 32 + 16) 8 8 $$ Hs with ⟨S8, S8'⟩
  iunfold stk at S8'
  icases S8' with ⟨%s8, %hs8, S8'⟩
  icases U128From.memBytes_split n out.toNat 4 ob (by omega) $$ Ho with ⟨Ho0, Ho4⟩
  simp only [f624]
  generalize hK : AllocWalk.cost310W cfg F size 4 = K
  have key := f625_spec (GF := GF) cfg lim (d + 1) types[45]! (by rfl) inst mi A n g ta hm (by omega) Cg gt (sp - 16)
    (sp - 16 + 8) size idx maxP len live F s8 hs8 (by omega) (by omega) hsize hsize2 hr
  rw [hK] at key
  clear hK
  rw [show 70 * cfg.regularOpCost + K + R = 70 * cfg.regularOpCost + (K + R) by omega]
  ihave S16 := stk_addr (show sp.toNat - 32 = (sp - 16).toNat - 16 by omega) $$ S16
  ihave S8' := AllocNewCell.memBytes_addr (show sp.toNat - 32 + 16 + 8 = (sp - 16 + 8).toNat by omega) $$ S8'
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep; mstep; mstep; mstep; mstep
  mcall key using [Hg S16 Hvt Hinv S8']
  · iframe Hg S16 Hvt Hinv S8'
  icases HQ with ⟨%hrs, %p, %hp0, Hg, S16, Hvt, HA, P0, P4⟩
  subst hrs
  clear key
  mcredits (18 * cfg.regularOpCost + R)
  mstep; mstep; mstep [P0] with (simp [UInt32.toNat_add]; omega)
  mstep [Ho0]
  mstep; mstep; mstep [P4] with (simp [UInt32.toNat_add]; omega)
  mstep [Ho4]
  mstep; mstep; mstep; mstep [Hg]
  rw [show sp - 16 + 16 = sp by simp]
  repeat mstep
  isplitl [Hc]
  · iapply BorrowMut.credits_le
    iframe Hc
    ipureintro; omega
  isplitr
  · ipureintro; trivial
  iexists p
  isplitr
  · ipureintro; exact hp0
  iframe Hg Hvt HA Ho0 Ho4
  ihave P0 := stk_word n _ _ $$ P0
  ihave P4 := stk_word n _ _ $$ P4
  ihave P8 := stk_join n (sp - 16 + 8).toNat 4 4 $$ [P0 P4]
  · iframe P0 P4
  ihave P8 := stk_addr (show (sp - 16 + 8).toNat = sp.toNat - 32 + 16 + 8 by omega) $$ P8
  ihave S16' := stk_join n (sp.toNat - 32 + 16) 8 8 $$ [S8 P8]
  · iframe S8 P8
  ihave S16 := stk_addr (show (sp - 16).toNat - 16 = sp.toNat - 32 by omega) $$ S16
  iapply stk_join n (sp.toNat - 32) 16 16
  iframe S16 S16'

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **`alloc::alloc::exchange_malloc(size)`** at alignment 4 (590): 624 in a 16-byte frame; the block
`p ≠ 0` (the out-of-memory path 842 not taken). -/
theorem f590_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 8 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp size idx : UInt32) (maxP len : Nat) (live : List (Nat × Nat)) (F : Nat)
    (hsp : 48 ≤ sp.toNat) (hsize : 1 ≤ size.toNat) (hsize2 : size.toNat < 2 ^ 28)
    (hr : roomFor4 len maxP size) :
    code310 n maxP inst mi A ∗ A 310 ↪[wf] FuncInst.wasm types[13]! inst f310 ∗
      A 625 ↪[wf] FuncInst.wasm types[45]! inst f625 ∗ A 624 ↪[wf] FuncInst.wasm types[31]! inst f624
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f590 Cg
        (fun args => iprop(⌜args = [.i32 size]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          stk n (sp.toNat - 48) 48 ∗ vt n 1057464 idx ta (A 578) ∗ heapInv n maxP len live F))
        (fun _ => 100 * cfg.regularOpCost + AllocWalk.cost310W cfg F size 4)
        (fun _ rs => iprop(∃ p : UInt32, ⌜rs = [.i32 p] ∧ p ≠ 0⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          stk n (sp.toNat - 48) 48 ∗ vt n 1057464 idx ta (A 578) ∗ heapA n maxP len live F size p)) := by
  iintro ⟨#Hcode, #H310, #H625, #H624⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold code310 at Hcode
    icases Hcode with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩
    iexact Hi
  have hn := hm.mem
  have hg := hm.glob
  have ha624 := hm.funcs 624 (by decide)
  have t31 : types[31]!.params.length = 3 := by rfl
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, Hvt, Hinv⟩
  subst hargs
  have hlt := sp.toNat_lt
  have h16 : (sp - 16).toNat = sp.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have h8 : (sp - 16 + 8).toNat = (sp - 16).toNat + 8 := by rw [UInt32.toNat_add, h16]; simp; omega
  icases stk_split n (sp.toNat - 48) 32 16 $$ Hs with ⟨S32, Hs⟩
  icases stk_split n (sp.toNat - 48 + 32) 8 8 $$ Hs with ⟨S8, S8'⟩
  iunfold stk at S8'
  icases S8' with ⟨%s8, %hs8, S8'⟩
  simp only [f590]
  generalize hK : AllocWalk.cost310W cfg F size 4 = K
  have key := f624_spec (GF := GF) cfg lim (d + 1) types[31]! (by rfl) inst mi A n g ta hm (by omega) Cg gt (sp - 16)
    (sp - 16 + 8) size idx maxP len live F s8 hs8 (by omega) (by omega) hsize hsize2 hr
  rw [hK] at key
  clear hK
  rw [show 100 * cfg.regularOpCost + K + R = 100 * cfg.regularOpCost + (K + R) by omega]
  ihave S32 := stk_addr (show sp.toNat - 48 = (sp - 16).toNat - 32 by omega) $$ S32
  ihave S8' := AllocNewCell.memBytes_addr (show sp.toNat - 48 + 32 + 8 = (sp - 16 + 8).toNat by omega) $$ S8'
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep; mstep; mstep; mstep
  mcall key using [Hg S32 Hvt Hinv S8']
  · iframe Hg S32 Hvt Hinv S8'
  icases HQ with ⟨%hrs, %p, %hp0, Hg, S32, Hvt, HA, P0, P4⟩
  subst hrs
  clear key
  mcredits (9 * cfg.regularOpCost + R)
  mstep
  mstep; mstep [P0] with (simp [UInt32.toNat_add]; omega)
  mstep
  iapply mwpi_cons; iapply mwpi_br_if_taken'; isplitr
  · ipureintro; exact ⟨rfl, hp0⟩
  mctrl_norm; repeat mpay
  mstep; mstep; mstep; mstep [Hg]
  rw [show sp - 16 + 16 = sp by simp]
  repeat mstep
  isplitl [Hc]
  · iapply BorrowMut.credits_le
    iframe Hc
    ipureintro; omega
  iexists p
  isplitr
  · ipureintro; exact ⟨by simp [htype], hp0⟩
  iframe Hg Hvt HA
  ihave P0 := stk_word n _ _ $$ P0
  ihave P4 := stk_word n _ _ $$ P4
  ihave P8 := stk_join n (sp - 16 + 8).toNat 4 4 $$ [P0 P4]
  · iframe P0 P4
  ihave P8 := stk_addr (show (sp - 16 + 8).toNat = sp.toNat - 48 + 32 + 8 by omega) $$ P8
  ihave S16 := stk_join n (sp.toNat - 48 + 32) 8 8 $$ [S8 P8]
  · iframe S8 P8
  ihave S32 := stk_addr (show (sp - 16).toNat - 32 = sp.toNat - 48 by omega) $$ S32
  iapply stk_join n (sp.toNat - 48) 32 16
  iframe S32 S16

end L625

section L639

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The block lies below `2^32`. -/
theorem heapR_bound (n maxP len : Nat) (live : List (Nat × Nat)) (F : Nat) (size p : UInt32) :
    heapR (GF := GF) n maxP len live F size p ⊢ ⌜p.toNat + size.toNat < 2 ^ 32⌝ ∗ heapR n maxP len live F size p := by
  iintro H
  iunfold heapR at H
  icases H with ⟨%len', %hl, H⟩
  ihave H := AllocZeroed.heapInv_bound n maxP len' _ _ $$ H
  icases H with ⟨%⟨hb, h32⟩, H⟩
  have := hb p.toNat size.toNat (by simp)
  isplitr
  · ipureintro; omega
  iunfold heapR
  iexists len'
  iframe H
  ipureintro; exact hl

/-- The 20-byte error box as its four fields: 8 bytes (the code's first two words), then three words. -/
theorem block_split20 (n p : Nat) :
    block (GF := GF) n p 20 ⊢ ∃ b0 b8 b12 b16 : List UInt8, ⌜b0.length = 8 ∧ b8.length = 4 ∧ b12.length = 4 ∧
      b16.length = 4⌝ ∗ n ↦[wms][ p ] b0 ∗ n ↦[wms][ p + 8 ] b8 ∗ n ↦[wms][ p + 12 ] b12 ∗
      n ↦[wms][ p + 16 ] b16 := by
  iintro H
  iunfold block at H
  icases H with ⟨%bs, %hbs, H⟩
  icases U128From.memBytes_split n p 8 bs (by omega) $$ H with ⟨B0, H⟩
  icases U128From.memBytes_split n (p + 8) 4 (bs.drop 8) (by simp; omega) $$ H with ⟨B8, H⟩
  icases U128From.memBytes_split n (p + 8 + 4) 4 ((bs.drop 8).drop 4) (by simp; omega) $$ H with ⟨B12, B16⟩
  iexists bs.take 8, (bs.drop 8).take 4, ((bs.drop 8).drop 4).take 4, ((bs.drop 8).drop 4).drop 4
  isplitr
  · ipureintro; simp; omega
  rw [show p + 8 + 4 = p + 12 by omega, show p + 12 + 4 = p + 16 by omega]
  iframe B0 B8 B12 B16

theorem block_join20 (n p : Nat) (b0 b8 b12 b16 : List UInt8) (h0 : b0.length = 8) (h8 : b8.length = 4)
    (h12 : b12.length = 4) (h16 : b16.length = 4) :
    n ↦[wms][ p ] b0 ∗ n ↦[wms][ p + 8 ] b8 ∗ n ↦[wms][ p + 12 ] b12 ∗ n ↦[wms][ p + 16 ] b16 ⊢
      block (GF := GF) n p 20 := by
  iintro ⟨B0, B8, B12, B16⟩
  ihave H := U128From.memBytes_join (GF := GF) n (p + 12) 4 b12 b16 h12 $$ [B12 B16]
  · rw [show p + 12 + 4 = p + 16 by omega]; iframe B12 B16
  ihave H := U128From.memBytes_join (GF := GF) n (p + 8) 4 b8 (b12 ++ b16) h8 $$ [B8 H]
  · rw [show p + 8 + 4 = p + 12 by omega]; iframe B8 H
  ihave H := U128From.memBytes_join (GF := GF) n p 8 b0 (b8 ++ (b12 ++ b16)) h0 $$ [B0 H]
  · iframe B0 H
  iunfold block
  iexists b0 ++ (b8 ++ (b12 ++ b16))
  iframe H
  ipureintro; simp; omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **`Error::syntax(code, line, column)`** (639): a 20-byte box (590), the 12-byte `ErrorCode` at
`e` copied into it, then the line and column. -/
theorem f639_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 9 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp e line col idx : UInt32) (maxP len : Nat) (live : List (Nat × Nat)) (F : Nat)
    (eb : List UInt8) (heb : eb.length = 12) (he : e.toNat + 12 ≤ 2 ^ 32)
    (hsp : 48 ≤ sp.toNat) (hr : roomFor4 len maxP 20) :
    code310 n maxP inst mi A ∗ A 310 ↪[wf] FuncInst.wasm types[13]! inst f310 ∗
      A 625 ↪[wf] FuncInst.wasm types[45]! inst f625 ∗ A 624 ↪[wf] FuncInst.wasm types[31]! inst f624 ∗
      A 590 ↪[wf] FuncInst.wasm types[32]! inst f590
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f639 Cg
        (fun args => iprop(⌜args = [.i32 e, .i32 line, .i32 col]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          stk n (sp.toNat - 48) 48 ∗ vt n 1057464 idx ta (A 578) ∗ heapInv n maxP len live F ∗
          n ↦[wms][ e.toNat ] eb))
        (fun _ => 140 * cfg.regularOpCost + AllocWalk.cost310W cfg F 20 4)
        (fun _ rs => iprop(∃ p : UInt32, ⌜rs = [.i32 p] ∧ p ≠ 0⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          stk n (sp.toNat - 48) 48 ∗ vt n 1057464 idx ta (A 578) ∗ heapA n maxP len live F 20 p ∗
          n ↦[wms][ e.toNat ] eb)) := by
  iintro ⟨#Hcode, #H310, #H625, #H624, #H590⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold code310 at Hcode
    icases Hcode with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩
    iexact Hi
  have hn := hm.mem
  have hg := hm.glob
  have ha590 := hm.funcs 590 (by decide)
  have t32 : types[32]!.params.length = 1 := by rfl
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, Hvt, Hinv, He⟩
  subst hargs
  icases U128From.memBytes_split n e.toNat 8 eb (by omega) $$ He with ⟨E0, E8⟩
  simp only [f639]
  generalize hK : AllocWalk.cost310W cfg F 20 4 = K
  have key := f590_spec (GF := GF) cfg lim (d + 1) types[32]! (by rfl) inst mi A n g ta hm (by omega) Cg gt sp 20 idx
    maxP len live F hsp (by decide) (by decide) hr
  rw [hK] at key
  clear hK
  rw [show 140 * cfg.regularOpCost + K + R = 140 * cfg.regularOpCost + (K + R) by omega]
  mstep
  mcall key using [Hg Hs Hvt Hinv]
  · iframe Hg Hs Hvt Hinv
  icases HQ with ⟨%p, %⟨hrs, hp0⟩, Hg, Hs, Hvt, HA⟩
  subst hrs
  clear key
  mcredits (28 * cfg.regularOpCost + R)
  iunfold heapA at HA
  icases HA with ⟨HR, Hb⟩
  ihave HR := heapR_bound n maxP len live F 20 p $$ HR
  icases HR with ⟨%hpb, HR⟩
  rw [show UInt32.toNat 20 = 20 from rfl] at hpb ⊢
  icases block_split20 n p.toNat $$ Hb with ⟨%b0, %b8, %b12, %b16, %⟨h0, h8, h12, h16⟩, B0, B8, B12, B16⟩
  mstep; mstep
  mstep [B16]
  mstep; mstep; mstep [B12]
  mstep; mstep; mstep; mstep; mstep; mstep
  mstep [E8] with (simp [UInt32.toNat_add]; omega)
  mstep [B8] with (simp [UInt32.toNat_add]; omega)
  mstep; mstep; mstep [E0]
  mstep [B0]
  repeat mstep
  isplitl [Hc]
  · iapply BorrowMut.credits_le
    iframe Hc
    ipureintro; omega
  iexists p
  isplitr
  · ipureintro; exact ⟨by simp [htype], hp0⟩
  iframe Hg Hs Hvt
  isplitr [E0 E8]
  · iunfold heapA
    iframe HR
    rw [show UInt32.toNat 20 = 20 from rfl]
    iapply block_join20 n p.toNat (storeBytes (Value.i64 (UInt64.ofNat (Memory.decodeLE (List.take 8 eb)))) 8)
      (bytes32 (UInt32.ofNat (Memory.decodeLE (List.drop 8 eb)))) (bytes32 line) (bytes32 col) (by simp [storeBytes])
      (by simp) (by simp) (by simp)
    iframe B0 B8 B12 B16
  ihave E := U128From.memBytes_join n e.toNat 8 (eb.take 8) (eb.drop 8) (by simp; omega) $$ [E0 E8]
  · iframe E0 E8
  rw [List.take_append_drop]
  iexact E

end L639

section L647

variable {GF : BundledGFunctors} [WasmGS NearState GF]
open WNear.Binary.SerdeRead (rd)
open WNear.Binary.SerdePosition (cost638 cost645 f638_spec)

/-- The code a syntax error runs: the allocator's, and 583, 609, 645, 638, 625, 624, 590, 639. -/
def errCode (n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) : IProp GF :=
  iprop(code310 n maxP inst mi A ∗ A 310 ↪[wf] FuncInst.wasm types[13]! inst f310 ∗
    A 625 ↪[wf] FuncInst.wasm types[45]! inst f625 ∗ A 624 ↪[wf] FuncInst.wasm types[31]! inst f624 ∗
    A 590 ↪[wf] FuncInst.wasm types[32]! inst f590 ∗ A 639 ↪[wf] FuncInst.wasm types[15]! inst f639 ∗
    A 583 ↪[wf] FuncInst.wasm types[36]! inst f583 ∗ A 609 ↪[wf] FuncInst.wasm types[39]! inst f609 ∗
    A 645 ↪[wf] FuncInst.wasm types[31]! inst f645 ∗ A 638 ↪[wf] FuncInst.wasm types[14]! inst f638)

/-- A syntax error's cost bound at the reader's index `i`, on `heapInv … F`. -/
def costErr (cfg : WasmConfig) (F i : Nat) : Nat :=
  (80 + cost638 i) * cfg.regularOpCost + (150 * cfg.regularOpCost + AllocWalk.cost310W cfg F 20 4)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **`Deserializer::error(out, rd, code)`** (647, and 657 whose code is the same): the position of
the reader's index (638), then `Error::syntax` (639) on the 12-byte `ErrorCode` at `c`: `Err(box)` at
`out`, the box a fresh 20-byte block. At most `costErr cfg F i`. -/
theorem f647_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 10 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp out de c ptr idx : UInt32) (ob cb bs : List UInt8) (i : Nat) (maxP len : Nat)
    (live : List (Nat × Nat)) (F : Nat) (hob : ob.length = 8) (hout : out.toNat + 8 ≤ 2 ^ 32)
    (hcb : cb.length = 12) (hc : c.toNat + 12 ≤ 2 ^ 32) (hde : de.toNat + 12 ≤ 2 ^ 32) (hi : i ≤ bs.length)
    (hlen : bs.length + 1 < 2 ^ 32) (hptr : ptr.toNat + bs.length ≤ 2 ^ 32) (hsp : 80 ≤ sp.toNat)
    (hr : roomFor4 len maxP 20) :
    errCode n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f647 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 de, .i32 c]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          stk n (sp.toNat - 80) 80 ∗ vt n 1057464 idx ta (A 578) ∗ heapInv n maxP len live F ∗
          n ↦[wms][ out.toNat ] ob ∗ n ↦[wms][ c.toNat ] cb ∗ rd n de ptr bs i))
        (fun _ => costErr cfg F i)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ ∃ p : UInt32, ⌜p ≠ 0⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          stk n (sp.toNat - 80) 80 ∗ vt n 1057464 idx ta (A 578) ∗ heapA n maxP len live F 20 p ∗
          n ↦[i32][ out.toNat ] 1 ∗ n ↦[i32][ out.toNat + 4 ] p ∗ n ↦[wms][ c.toNat ] cb ∗ rd n de ptr bs i)) := by
  iintro Hcode
  iunfold errCode at Hcode
  icases Hcode with ⟨#H310c, #H310, #H625, #H624, #H590, #H639, #H583, #H609, #H645, #H638⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold code310 at H310c
    icases H310c with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩
    iexact Hi
  have hn := hm.mem
  have hg := hm.glob
  have ha638 := hm.funcs 638 (by decide)
  have ha639 := hm.funcs 639 (by decide)
  have t14 : types[14]!.params.length = 2 := by rfl
  have t15 : types[15]!.params.length = 3 := by rfl
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, Hvt, Hinv, Ho, Hcb, Hrd⟩
  subst hargs
  have hlt := sp.toNat_lt
  have h32 : (sp - 32).toNat = sp.toNat - 32 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  icases stk_split n (sp.toNat - 80) 48 32 $$ Hs with ⟨S48, Hs⟩
  icases stk_split n (sp.toNat - 80 + 48) 8 24 $$ Hs with ⟨S8, Hs⟩
  icases stk_split n (sp.toNat - 80 + 48 + 8) 8 16 $$ Hs with ⟨SP, Hs⟩
  icases stk_split n (sp.toNat - 80 + 48 + 8 + 8) 12 4 $$ Hs with ⟨SE, S4⟩
  iunfold stk at SP SE
  icases SP with ⟨%sp8, %hsp8, SP⟩
  icases SE with ⟨%se, %hse, SE⟩
  icases U128From.memBytes_split n c.toNat 8 cb (by omega) $$ Hcb with ⟨C0, C8⟩
  simp only [f647, costErr]
  generalize hK2 : AllocWalk.cost310W cfg F 20 4 = K2
  rw [show (80 + cost638 i) * cfg.regularOpCost + (150 * cfg.regularOpCost + K2) + R =
    230 * cfg.regularOpCost + (cost638 i * cfg.regularOpCost + (K2 + R)) by rw [Nat.add_mul]; omega]
  have h8 : (sp - 32 + 8).toNat = (sp - 32).toNat + 8 := by rw [UInt32.toNat_add, h32]; simp; omega
  have key638 := f638_spec (GF := GF) cfg lim (d + 1) types[14]! (by rfl) inst mi n g hn hg (A 583) (A 609) (A 645)
    (hm.funcs 583 (by decide)) (hm.funcs 609 (by decide)) (hm.funcs 645 (by decide)) (by omega) Cg gt (sp - 32)
    (sp - 32 + 8) de ptr sp8 bs i hsp8 (by omega) hde hi hlen hptr (by omega)
  ihave S48 := stk_addr (show sp.toNat - 80 = (sp - 32).toNat - 48 by omega) $$ S48
  ihave SP := AllocNewCell.memBytes_addr (show sp.toNat - 80 + 48 + 8 = (sp - 32 + 8).toNat by
    rw [UInt32.toNat_add, h32]; simp; omega) $$ SP
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep; mstep; mstep
  have hK3 : (12 + cost638 i) * cfg.regularOpCost = 12 * cfg.regularOpCost + cost638 i * cfg.regularOpCost :=
    Nat.add_mul _ _ _
  have hK4 : (11 + cost638 i) * cfg.regularOpCost = 11 * cfg.regularOpCost + cost638 i * cfg.regularOpCost :=
    Nat.add_mul _ _ _
  mcall key638 using [Hg S48 SP Hrd]
  · iframe Hg S48 SP Hrd
  rw [hK4]
  clear hK3 hK4
  generalize cost638 i * cfg.regularOpCost = K1
  mcredits (210 * cfg.regularOpCost + (K2 + R))
  clear key638
  icases HQ with ⟨%hrs, Hg, S48, ⟨%line, %col, L0, L4⟩, Hrd⟩
  subst hrs
  icases U128From.memBytes_split n (sp.toNat - 80 + 48 + 8 + 8) 8 se (by omega) $$ SE with ⟨SE0, SE8⟩
  ihave SE0 := AllocNewCell.memBytes_addr (show sp.toNat - 80 + 48 + 8 + 8 = (sp - 32).toNat + 16 by omega) $$ SE0
  ihave SE8 := AllocNewCell.memBytes_addr (show sp.toNat - 80 + 48 + 8 + 8 + 8 = (sp - 32 + 16 + 8).toNat by
    rw [UInt32.toNat_add, UInt32.toNat_add, h32]; simp; omega) $$ SE8
  mstep; mstep [L4] with (simp [UInt32.toNat_add]; omega)
  mstep
  mstep; mstep [L0] with (simp [UInt32.toNat_add]; omega)
  mstep
  mstep; mstep; mstep; mstep; mstep
  mstep; mstep; mstep
  mstep [C8] with (simp [UInt32.toNat_add]; omega)
  mstep [SE8]
  mstep; mstep; mstep [C0]
  mstep [SE0]
  mstep; mstep; mstep; mstep; mstep
  ihave E := U128From.memBytes_join n ((sp - 32).toNat + 16) 8
    (storeBytes (Value.i64 (UInt64.ofNat (Memory.decodeLE (List.take 8 cb)))) 8)
    (bytes32 (UInt32.ofNat (Memory.decodeLE (List.drop 8 cb)))) (by simp [storeBytes]) $$ [SE0 SE8]
  · rw [show (sp - 32).toNat + 16 + 8 = (sp - 32 + 16 + 8).toNat by rw [UInt32.toNat_add, UInt32.toNat_add, h32]; simp; omega]
    iframe SE0 SE8
  ihave E := AllocNewCell.memBytes_addr (show (sp - 32).toNat + 16 = (sp - 32 + 16).toNat by
    rw [UInt32.toNat_add, h32]; simp; omega) $$ E
  have key639 := f639_spec (GF := GF) cfg lim (d + 1) types[15]! (by rfl) inst mi A n g ta hm (by omega) Cg gt
    (sp - 32) (sp - 32 + 16) line col idx maxP len live F
    (storeBytes (Value.i64 (UInt64.ofNat (Memory.decodeLE (List.take 8 cb)))) 8 ++
      bytes32 (UInt32.ofNat (Memory.decodeLE (List.drop 8 cb)))) (by simp [storeBytes])
    (by rw [UInt32.toNat_add, h32]; simp; omega) (by omega) hr
  rw [hK2] at key639
  clear hK2
  ihave S48 := stk_addr (show (sp - 32).toNat - 48 = (sp - 32).toNat - 48 by rfl) $$ S48
  mcall key639 using [Hg S48 Hvt Hinv E]
  · iframe Hg S48 Hvt Hinv E
  mcredits (34 * cfg.regularOpCost + R)
  clear key639
  icases HQ with ⟨%p, %⟨hrs, hp0⟩, Hg, S48, Hvt, HA, E⟩
  subst hrs
  icases U128From.memBytes_split n out.toNat 4 ob (by omega) $$ Ho with ⟨O0, O4⟩
  mstep
  mstep; mstep; mstep [O0]
  mstep; mstep; mstep [O4]
  mstep; mstep; mstep; mstep [Hg]
  rw [show sp - 32 + 32 = sp by simp]
  repeat mstep
  isplitl [Hc]
  · iapply BorrowMut.credits_le
    iframe Hc
    ipureintro; omega
  isplitr
  · ipureintro; trivial
  iexists p
  isplitr
  · ipureintro; exact hp0
  iframe Hg Hvt HA O0 O4 Hrd
  isplitr [C0 C8]
  · ihave L0 := stk_word n _ _ $$ L0
    ihave L4 := stk_word n _ _ $$ L4
    ihave Lw := stk_join n (sp - 32 + 8).toNat 4 4 $$ [L0 L4]
    · iframe L0 L4
    ihave Lw := stk_addr (show (sp - 32 + 8).toNat = sp.toNat - 80 + 48 + 8 by omega) $$ Lw
    ihave J1 := stk_join n (sp.toNat - 80 + 48) 8 8 $$ [S8 Lw]
    · iframe S8 Lw
    ihave E := stk_intro n _ _ $$ E
    ihave E := stk_addr (show (sp - 32 + 16).toNat = sp.toNat - 80 + 48 + 16 by
      rw [UInt32.toNat_add, h32]; simp; omega) $$ E
    rw [show (storeBytes (Value.i64 (UInt64.ofNat (Memory.decodeLE (List.take 8 cb)))) 8 ++
      bytes32 (UInt32.ofNat (Memory.decodeLE (List.drop 8 cb)))).length = 12 by simp [storeBytes]]
    ihave J2 := stk_join n (sp.toNat - 80 + 48) 16 12 $$ [J1 E]
    · iframe J1 E
    ihave S4 := stk_addr (show sp.toNat - 80 + 48 + 8 + 8 + 12 = sp.toNat - 80 + 48 + 28 by omega) $$ S4
    ihave J3 := stk_join n (sp.toNat - 80 + 48) 28 4 $$ [J2 S4]
    · iframe J2 S4
    ihave S48 := stk_addr (show (sp - 32).toNat - 48 = sp.toNat - 80 by omega) $$ S48
    iapply stk_join n (sp.toNat - 80) 48 32
    iframe S48 J3
  ihave C := U128From.memBytes_join n c.toNat 8 (cb.take 8) (cb.drop 8) (by simp; omega) $$ [C0 C8]
  · iframe C0 C8
  rw [List.take_append_drop]
  iexact C

/-- 657 (`peek_error`'s twin in `as_str`) has 647's code. -/
theorem f657_eq : f657 = f647 := rfl

end L647

section L648

variable {GF : BundledGFunctors} [WasmGS NearState GF]
open WNear.Binary.SerdeRead (rd)
open WNear.Binary.ArgsLeaves (sliceRead)
open WNear.Binary.FromUtf8 (res927 cost927)
open WNear.Binary.FromUtf8Gen (utf8Width)
open WNear.Binary.SerdePosition (cost638)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **`SliceRead::as_str(out, rd, p, len)`** (648) on bytes that are not UTF-8: the `len` bytes at
`p = ptr + a` inside the reader's input; `from_utf8` (927) fails, and the error is
`InvalidUnicodeCodePoint` (code 14) through 657: `Err(box)` at `out`. -/
theorem f648_spec_bad (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 11 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp out de ptr p len idx : UInt32) (ob ibs : List UInt8) (i a : Nat) (maxP mlen : Nat)
    (live : List (Nat × Nat)) (F : Nat) (hob : ob.length = 8) (hout : out.toNat + 8 ≤ 2 ^ 32)
    (hde : de.toNat + 12 ≤ 2 ^ 32) (hi : i ≤ ibs.length) (hlen : ibs.length + 1 < 2 ^ 32)
    (hptr : ptr.toNat + ibs.length ≤ 2 ^ 32) (hp : p.toNat = ptr.toNat + a) (ha : a + len.toNat ≤ ibs.length)
    (hbad : Utf8.utf8Ok ((ibs.drop a).take len.toNat) = false) (hsp : 112 ≤ sp.toNat)
    (hr : roomFor4 mlen maxP 20) :
    errCode n maxP inst mi A ∗ A 927 ↪[wf] FuncInst.wasm types[31]! inst f927 ∗
      A 657 ↪[wf] FuncInst.wasm types[31]! inst f657
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f648 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 de, .i32 p, .i32 len]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          stk n (sp.toNat - 112) 112 ∗ vt n 1057464 idx ta (A 578) ∗ heapInv n maxP mlen live F ∗
          n ↦[wms][ out.toNat ] ob ∗ rd n de ptr ibs i ∗ n ↦[wms][ 1071704 ] utf8Width))
        (fun _ => (60 + cost927 len.toNat) * cfg.regularOpCost + costErr cfg F i)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ ∃ q : UInt32, ⌜q ≠ 0⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          stk n (sp.toNat - 112) 112 ∗ vt n 1057464 idx ta (A 578) ∗ heapA n maxP mlen live F 20 q ∗
          n ↦[i32][ out.toNat ] 1 ∗ n ↦[i32][ out.toNat + 4 ] q ∗ rd n de ptr ibs i ∗
          n ↦[wms][ 1071704 ] utf8Width)) := by
  iintro ⟨Hcode, #H927, #H657⟩
  iunfold errCode at Hcode
  icases Hcode with ⟨#H310c, #H310, #H625, #H624, #H590, #H639, #H583, #H609, #H645, #H638⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold code310 at H310c
    icases H310c with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩
    iexact Hi
  have hn := hm.mem
  have hg := hm.glob
  have ha927 := hm.funcs 927 (by decide)
  have ha657 := hm.funcs 657 (by decide)
  have t31 : types[31]!.params.length = 3 := by rfl
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, Hvt, Hinv, Ho, Hrd, Ht⟩
  subst hargs
  have hlt := sp.toNat_lt
  have h32 : (sp - 32).toNat = sp.toNat - 32 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  iunfold rd, sliceRead at Hrd
  icases Hrd with ⟨⟨D0, D4, D8⟩, Hb⟩
  icases U128From.memBytes_split n ptr.toNat a ibs (by omega) $$ Hb with ⟨B0, Bx⟩
  icases U128From.memBytes_split n (ptr.toNat + a) len.toNat (ibs.drop a) (by simp; omega) $$ Bx with ⟨Bs, B2⟩
  ihave Bs := AllocNewCell.memBytes_addr (show ptr.toNat + a = p.toNat by omega) $$ Bs
  icases stk_split n (sp.toNat - 112) 80 32 $$ Hs with ⟨S80, Hs⟩
  icases stk_split n (sp.toNat - 112 + 80) 12 20 $$ Hs with ⟨SO, Hs⟩
  icases stk_split n (sp.toNat - 112 + 80 + 12) 4 16 $$ Hs with ⟨S4, Hs⟩
  icases stk_split n (sp.toNat - 112 + 80 + 12 + 4) 4 12 $$ Hs with ⟨SC0, Hs⟩
  icases stk_split n (sp.toNat - 112 + 80 + 12 + 4 + 4) 8 4 $$ Hs with ⟨SC8, S4'⟩
  iunfold stk at SO SC0 SC8
  icases SO with ⟨%so, %hso, SO⟩
  icases SC0 with ⟨%sc0, %hsc0, SC0⟩
  icases SC8 with ⟨%sc8, %hsc8, SC8⟩
  simp only [f648]
  rw [show (60 + cost927 len.toNat) * cfg.regularOpCost + costErr cfg F i + R =
    60 * cfg.regularOpCost + (cost927 len.toNat * cfg.regularOpCost + (costErr cfg F i + R)) by
      rw [Nat.add_mul]; omega]
  generalize hE : costErr cfg F i = E
  have hK2 : (13 + cost927 len.toNat) * cfg.regularOpCost = 13 * cfg.regularOpCost + cost927 len.toNat * cfg.regularOpCost :=
    Nat.add_mul _ _ _
  have hK3 : (16 + cost927 len.toNat) * cfg.regularOpCost = 16 * cfg.regularOpCost + cost927 len.toNat * cfg.regularOpCost :=
    Nat.add_mul _ _ _
  ihave SO := AllocNewCell.memBytes_addr (show sp.toNat - 112 + 80 = (sp - 32).toNat by omega) $$ SO
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep; mstep
  mcall (FromUtf8Gen.f927_spec cfg (lim := lim) (d + 1) types[31]! (by rfl) inst mi n hn Cg (sp - 32) p len so
    ((ibs.drop a).take len.toNat) hso (by omega) (by simp; omega) (by omega)) using [SO Bs Ht]
  · iframe SO Bs Ht
  rw [hK3]
  clear hK2 hK3
  generalize cost927 len.toNat * cfg.regularOpCost = K
  mcredits (36 * cfg.regularOpCost + (E + R))
  icases HQ with ⟨%hrs, Bs, Hres, Ht⟩
  subst hrs
  iunfold res927 at Hres
  rw [hbad]
  simp only [Bool.false_eq_true, ite_false]
  icases Hres with ⟨%eb, %heb, R0, R4⟩
  mstep; mstep
  mstep; mstep [R0] with (simp [UInt32.toNat_add]; omega)
  mstep; mstep
  mstep
  mstep; mstep
  mstep [SC0] with (simp [UInt32.toNat_add]; omega)
  mstep; mstep; mstep; mstep; mstep
  ihave Bs := AllocNewCell.memBytes_addr (show p.toNat = ptr.toNat + a by omega) $$ Bs
  ihave Bx := U128From.memBytes_join n (ptr.toNat + a) len.toNat ((ibs.drop a).take len.toNat)
    ((ibs.drop a).drop len.toNat) (by simp; omega) $$ [Bs B2]
  · iframe Bs B2
  rw [List.take_append_drop]
  ihave Hb := U128From.memBytes_join n ptr.toNat a (ibs.take a) (ibs.drop a) (by simp; omega) $$ [B0 Bx]
  · iframe B0 Bx
  rw [List.take_append_drop]
  ihave C := U128From.memBytes_join n (sp.toNat - 112 + 80 + 12 + 4) 4 (bytes32 14) sc8 (by simp) $$ [SC0 SC8]
  · iframe SC0 SC8
  ihave C := AllocNewCell.memBytes_addr (show sp.toNat - 112 + 80 + 12 + 4 = (sp - 32 + 16).toNat by
    rw [UInt32.toNat_add, h32]; simp; omega) $$ C
  ihave S80 := stk_addr (show sp.toNat - 112 = (sp - 32).toNat - 80 by omega) $$ S80
  have key := f647_spec (GF := GF) cfg lim (d + 1) types[31]! (by rfl) inst mi A n g ta hm (by omega) Cg gt
    (sp - 32) out de (sp - 32 + 16) ptr idx ob (bytes32 14 ++ sc8) ibs i maxP mlen live F hob hout (by simp; omega)
    (by rw [UInt32.toNat_add, h32]; simp; omega) hde hi hlen hptr (by omega) hr
  rw [← f657_eq, hE] at key
  unfold errCode at key
  mcall key using [Hg S80 Hvt Hinv Ho C D0 D4 D8 Hb]
  · iframe Hg S80 Hvt Hinv Ho C
    iunfold rd, sliceRead
    iframe D0 D4 D8 Hb
  clear key
  mcredits (11 * cfg.regularOpCost + R)
  icases HQ with ⟨%hrs, %q, %hq, Hg, S80, Hvt, HA, O0, O4, C, Hrd⟩
  subst hrs
  mstep
  mstep; mstep; mstep; mstep [Hg]
  rw [show sp - 32 + 32 = sp by simp]
  repeat mstep
  isplitl [Hc]
  · iapply BorrowMut.credits_le
    iframe Hc
    ipureintro; omega
  isplitr
  · ipureintro; trivial
  iexists q
  isplitr
  · ipureintro; exact hq
  iframe Hg Hvt HA O0 O4 Hrd Ht
  ihave R0 := stk_word n _ _ $$ R0
  ihave R4 := stk_intro n _ _ $$ R4
  rw [heb]
  ihave SO := stk_join n (sp - 32).toNat 4 8 $$ [R0 R4]
  · iframe R0 R4
  ihave SO := stk_addr (show (sp - 32).toNat = sp.toNat - 112 + 80 by omega) $$ SO
  ihave J1 := stk_join n (sp.toNat - 112 + 80) 12 4 $$ [SO S4]
  · iframe SO S4
  ihave C := stk_intro n _ _ $$ C
  ihave C := stk_addr (show (sp - 32 + 16).toNat = sp.toNat - 112 + 80 + 16 by
    rw [UInt32.toNat_add, h32]; simp; omega) $$ C
  rw [show (bytes32 14 ++ sc8).length = 12 by simp; omega]
  ihave J2 := stk_join n (sp.toNat - 112 + 80) 16 12 $$ [J1 C]
  · iframe J1 C
  ihave S4' := stk_addr (show sp.toNat - 112 + 80 + 12 + 4 + 4 + 8 = sp.toNat - 112 + 80 + 28 by omega) $$ S4'
  ihave J3 := stk_join n (sp.toNat - 112 + 80) 28 4 $$ [J2 S4']
  · iframe J2 S4'
  ihave S80 := stk_addr (show (sp - 32).toNat - 80 = sp.toNat - 112 by omega) $$ S80
  iapply stk_join n (sp.toNat - 112) 80 32
  iframe S80 J3

end L648

end WNear.Binary.SerdeErrBox
