import Bridge.Functions.SerdePosition
import Bridge.Functions.VecWithCap

/-!
# serde_json's error box (M6): `Box<ErrorImpl>` through the allocator

DEV
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

/-- The heap after an allocation of `size` bytes at `p`: some length `len'` (grown or not), the
block lent, the bound `max F 1`. -/
def heapA (n maxP len : Nat) (live : List (Nat × Nat)) (F : Nat) (size : UInt32) (p : UInt32) : IProp GF :=
  iprop(∃ len', ⌜len' = len ∨ len' = len + (cellPages (wordsOf size) 4).toNat * 65536⌝ ∗
    heapInv n maxP len' ((p.toNat, size.toNat) :: live) (max F 1) ∗ block n p.toNat size.toNat)

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
  · iunfold heapA
    iexists len'
    iframe Hinv Hb
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

end WNear.Binary.SerdeErrBox
