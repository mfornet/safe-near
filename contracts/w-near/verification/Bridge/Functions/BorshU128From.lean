import Bridge.Functions.LookupMapBorsh
import Bridge.Functions.BorshInt
import Bridge.Functions.U128From

/-!
# `u128::try_from_slice` (376) and `LookupMap::deserialize_value` (398)

```wat
;; 376 try_from_slice (out, ptr, len): sp -= 64; [sp+12] := len; [sp+8] := ptr
;;     372(sp + 40, sp + 8)                       ;; u128::deserialize_reader
;;     [sp+24] := i64 [sp+52]; [sp+32] := [sp+60]; [sp+16] := i64 [sp+44]
;;     tag [sp+40] = 1 → Err (not taken)
;;     [sp+12] ≠ 0 → Err via 736 (not taken: the slice is consumed)
;;     out := 0; out+16 := i64 [sp+28]; out+8 := i64 [sp+20]; sp += 64
;; 398 deserialize_value (out, ptr, len): sp -= 32; 376(sp + 8, ptr, len)
;;     tag [sp+8] = 1 → panic (521, not taken)
;;     out+8 := i64 [sp+24]; out := i64 [sp+16]; sp += 32
```
-/

namespace WNear.Binary.LookupMapBorsh

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_word stk_addr roomFor)

section S376

variable {GF : BundledGFunctors} [WasmGS NearState GF]
open WNear.Binary.BorshInt (rdCode rdr pre372 post372 f372_spec)
open WNear.Binary.BorshFT (split8 join64' split64' joinB)
open WNear.Binary.VecFromElem (ofNat_decode_pair storeBytes_pair64)

/-- The code of 376 (persistent). -/
def code376 (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) : IProp GF :=
  iprop(rdCode inst mi A ∗ A 372 ↪[wf] FuncInst.wasm types[14]! inst f372)

instance (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) : Persistent (code376 (GF := GF) inst mi A) := by
  unfold code376; infer_instance

def pre376 (n g : Nat) (gt : GlobalType) (s out ptr : UInt32) (b0 b1 ob : List UInt8) (args : List Value) :
    IProp GF :=
  iprop(⌜args = [.i32 out, .i32 ptr, .i32 16]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 112) 112 ∗
    n ↦[wms][ ptr.toNat ] b0 ∗ n ↦[wms][ ptr.toNat + 8 ] b1 ∗ n ↦[wms][ out.toNat ] ob)

/-- `Ok(v)` at `out`: the tag 0, the 4 bytes after it untouched, the `u128` `b0 ++ b1` at `out + 8`. -/
def post376 (n g : Nat) (gt : GlobalType) (s out ptr : UInt32) (b0 b1 ob : List UInt8) (_args rs : List Value) :
    IProp GF :=
  iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 112) 112 ∗
    n ↦[wms][ ptr.toNat ] b0 ∗ n ↦[wms][ ptr.toNat + 8 ] b1 ∗
    n ↦[i32][ out.toNat ] 0 ∗ n ↦[wms][ out.toNat + 4 ] ((ob.drop 4).take 4) ∗
    n ↦[wms][ out.toNat + 8 ] b0 ∗ n ↦[wms][ out.toNat + 16 ] b1)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **`u128::try_from_slice`** (376) on the 16-byte slice `b0 ++ b1` at `ptr`: 372 reads it, the
slice is then empty, `Ok` with the value at `out + 8`. -/
theorem f376_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 2 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s out ptr : UInt32) (b0 b1 ob : List UInt8) (hs : 112 ≤ s.toNat)
    (hb0 : b0.length = 8) (hb1 : b1.length = 8) (hob : ob.length = 24)
    (hout : out.toNat + 24 ≤ 2 ^ 32) (hptr : ptr.toNat + 16 ≤ 2 ^ 32) :
    code376 inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f376 Cg
        (pre376 n g gt s out ptr b0 b1 ob)
        (fun _ => 244 * cfg.regularOpCost)
        (post376 n g gt s out ptr b0 b1 ob) := by
  iintro #Hk
  ihave #Hrd : rdCode inst mi A $$ []
  · iunfold code376 at Hk; icases Hk with ⟨#H, -⟩; iexact H
  ihave #H372 : A 372 ↪[wf] FuncInst.wasm types[14]! inst f372 $$ []
  · iunfold code376 at Hk; icases Hk with ⟨-, #H⟩; iexact H
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold rdCode at Hrd; icases Hrd with ⟨#H, -⟩; iexact H
  obtain ⟨x0, x1, rfl⟩ := split8 b0 hb0
  obtain ⟨y0, y1, rfl⟩ := split8 b1 hb1
  have hn := hm.mem
  have hg := hm.glob
  have ha372 := hm.funcs 372 (by decide)
  have t14 : types[14]!.params.length = 2 := by rfl
  have hlt := s.toNat_lt
  have h64 : (s - 64).toNat = s.toNat - 64 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have e40 : (s - 64 + 40).toNat = s.toNat - 24 := by simp [UInt32.toNat_add, h64]; omega
  have e8 : (s - 64 + 8).toNat = s.toNat - 56 := by simp [UInt32.toNat_add, h64]; omega
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold pre376 at HP
  icases HP with ⟨%hargs, Hg, Hs, B0, B1, Ho⟩
  subst hargs
  -- out: [0, 4) [4, 8) [8, 16) [16, 24)
  ihave Ho := U128From.memBytes_split n out.toNat 4 ob (by omega) $$ Ho
  icases Ho with ⟨Ho0, Ho⟩
  ihave Ho := U128From.memBytes_split n (out.toNat + 4) 4 (ob.drop 4) (by simp; omega) $$ Ho
  icases Ho with ⟨Ho4, Ho⟩
  ihave Ho := U128From.memBytes_split n (out.toNat + 4 + 4) 8 ((ob.drop 4).drop 4) (by simp; omega) $$ Ho
  icases Ho with ⟨Ho8, Ho16⟩
  rw [show out.toNat + 4 + 4 = out.toNat + 8 by omega, show out.toNat + 8 + 8 = out.toNat + 16 by omega]
  -- the stack: 372's 48, then the frame
  icases stk_split n (s.toNat - 112) 48 64 $$ Hs with ⟨Lo, Hs⟩
  rw [show s.toNat - 112 + 48 = s.toNat - 64 by omega]
  icases stk_split n (s.toNat - 64) 8 56 $$ Hs with ⟨U0, Hs⟩
  rw [show s.toNat - 64 + 8 = s.toNat - 56 by omega]
  icases stk_split n (s.toNat - 56) 4 52 $$ Hs with ⟨R8, Hs⟩
  rw [show s.toNat - 56 + 4 = s.toNat - 52 by omega]
  icases stk_split n (s.toNat - 52) 4 48 $$ Hs with ⟨R12, Hs⟩
  rw [show s.toNat - 52 + 4 = s.toNat - 48 by omega]
  icases stk_split n (s.toNat - 48) 8 40 $$ Hs with ⟨FA, Hs⟩
  rw [show s.toNat - 48 + 8 = s.toNat - 40 by omega]
  icases stk_split n (s.toNat - 40) 8 32 $$ Hs with ⟨FB, Hs⟩
  rw [show s.toNat - 40 + 8 = s.toNat - 32 by omega]
  icases stk_split n (s.toNat - 32) 4 28 $$ Hs with ⟨FC, Hs⟩
  rw [show s.toNat - 32 + 4 = s.toNat - 28 by omega]
  icases stk_split n (s.toNat - 28) 4 24 $$ Hs with ⟨FD, Hs⟩
  rw [show s.toNat - 28 + 4 = s.toNat - 24 by omega]
  icases stk_split n (s.toNat - 24) 4 20 $$ Hs with ⟨FT, Hs⟩
  rw [show s.toNat - 24 + 4 = s.toNat - 20 by omega]
  icases stk_split n (s.toNat - 20) 4 16 $$ Hs with ⟨FG, Hs⟩
  rw [show s.toNat - 20 + 4 = s.toNat - 16 by omega]
  icases stk_split n (s.toNat - 16) 8 8 $$ Hs with ⟨P0, P1⟩
  rw [show s.toNat - 16 + 8 = s.toNat - 8 by omega]
  icases ReadRegister.stk4_word n _ $$ R8 with ⟨%r8, R8⟩
  icases ReadRegister.stk4_word n _ $$ R12 with ⟨%r12, R12⟩
  icases ReadRegister.stk4_word n _ $$ FG with ⟨%gw, FG⟩
  icases BorshInt.stk_bytes' $$ FA with ⟨%fa, %hfa, FA⟩
  icases BorshInt.stk_bytes' $$ FB with ⟨%fb, %hfb, FB⟩
  icases BorshInt.stk_bytes' $$ FC with ⟨%fc, %hfc, FC⟩
  icases BorshInt.stk_bytes' $$ FT with ⟨%ft, %hft, FT⟩
  icases BorshInt.stk_bytes' $$ P0 with ⟨%p0, %hp0, P0⟩
  icases BorshInt.stk_bytes' $$ P1 with ⟨%p1, %hp1, P1⟩
  simp only [f376]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep; mstep [R12]
  mstep; mstep; mstep [R8]
  mstep; mstep; mstep; mstep; mstep; mstep
  mcall (f372_spec cfg lim (d + 1) types[14]! (by rfl) inst mi A n g ta hm (by omega) Cg gt (s - 64) (s - 64 + 40)
      (s - 64 + 8) ptr 16 ft p0 p1 (bytes32 x0 ++ bytes32 x1) (bytes32 y0 ++ bytes32 y1) hft hp0 hp1
      (by simp) (by simp) (by omega) (by decide) (by omega) (by omega) (by omega))
    using [Hg Lo R8 R12 FT P0 P1 B0 B1]
  · iunfold pre372, rdr
    ihave Lo := stk_addr (show s.toNat - 112 = (s - 64).toNat - 48 by omega) $$ Lo
    ihave R := join64' (a := (s - 64 + 8).toNat) (b := s.toNat - 52) ptr 16 (by omega) $$ [R8 R12]
    · ihave R8 := memBytes_addr (show s.toNat - 56 = (s - 64 + 8).toNat by omega) $$ R8
      iframe R8 R12
    ihave FT := memBytes_addr (show s.toNat - 24 = (s - 64 + 40).toNat by omega) $$ FT
    ihave P0 := memBytes_addr (show s.toNat - 16 = (s - 64 + 40).toNat + 8 by omega) $$ P0
    ihave P1 := memBytes_addr (show s.toNat - 8 = (s - 64 + 40).toNat + 16 by omega) $$ P1
    iframe Hg Lo R FT P0 P1 B0 B1
    ipureintro; rfl
  iunfold post372, rdr at HQ
  icases HQ with ⟨%hrs, Hg, Lo, R, FT, P0, P1, B0, B1⟩
  subst hrs
  ihave R := memBytes_addr (show (s - 64 + 8).toNat = s.toNat - 56 by omega) $$ R
  ihave FT := memBytes_addr (show (s - 64 + 40).toNat = s.toNat - 24 by omega) $$ FT
  ihave P0 := memBytes_addr (show (s - 64 + 40).toNat + 8 = s.toNat - 16 by omega) $$ P0
  ihave P1 := memBytes_addr (show (s - 64 + 40).toNat + 16 = s.toNat - 8 by omega) $$ P1
  icases split64' (a := s.toNat - 56) (b := s.toNat - 52) (ptr + 16) (16 - 16) (by omega) $$ R with ⟨R8, R12⟩
  icases split64' (a := s.toNat - 16) (b := s.toNat - 12) x0 x1 (by omega) $$ P0 with ⟨X0, X1⟩
  icases split64' (a := s.toNat - 8) (b := s.toNat - 4) y0 y1 (by omega) $$ P1 with ⟨Y0, Y1⟩
  -- [sp+24, sp+32) := [sp+52, sp+60)
  ihave XY := join64' (a := s.toNat - 12) (b := s.toNat - 8) x1 y0 (by omega) $$ [X1 Y0]
  · iframe X1 Y0
  mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep [XY]
  rw [ofNat_decode_pair]
  mstep [FB]
  rw [storeBytes_pair64]
  icases split64' (a := s.toNat - 12) (b := s.toNat - 8) x1 y0 (by omega) $$ XY with ⟨X1, Y0⟩
  icases split64' (a := s.toNat - 40) (b := s.toNat - 36) x1 y0 (by omega) $$ FB with ⟨FB0, FB4⟩
  -- [sp+32] := [sp+60]
  mstep; mstep; mstep; mstep; mstep; mstep; mstep [Y1]; mstep [FC]
  -- [sp+16, sp+24) := [sp+44, sp+52)
  ihave GX := join64' (a := s.toNat - 20) (b := s.toNat - 16) gw x0 (by omega) $$ [FG X0]
  · iframe FG X0
  mstep; mstep; mstep [GX]
  rw [ofNat_decode_pair]
  mstep [FA]
  rw [storeBytes_pair64]
  icases split64' (a := s.toNat - 20) (b := s.toNat - 16) gw x0 (by omega) $$ GX with ⟨FG, X0⟩
  icases split64' (a := s.toNat - 48) (b := s.toNat - 44) gw x0 (by omega) $$ FA with ⟨FA0, FA4⟩
  -- TODO: block: tag [sp+40] = 0 ≠ 1 (br_if not taken); [sp+12] = 16 - 16 = 0 (br_if taken, skipping 736);
  --   local4 := i64 [sp+28, sp+36) = pair64 y0 y1 (join64' FB4 FC); local5 := i64 [sp+20, sp+28) = pair64 x0 x1
  --   (join64' FA4 FB0); out := 0 (Ho0); out+16 := local4 (Ho16 at (out + 16).toNat); out+8 := local5
  --   (Ho8 at (out + 8).toNat); br 1; sp += 64. Then rebuild stk n (s.toNat - 112) 112 from
  --   Lo U0 R8 R12 FA0 FA4 FB0 FB4 FC FD FT FG X0 X1 Y0 Y1 (StrRepeat/LookupMapBorsh `stkJ` chain),
  --   calibrate the cost (mcredits R; lower the 400 until it fails).
  ihave L4 := join64' (a := s.toNat - 36) (b := s.toNat - 32) y0 y1 (by omega) $$ [FB4 FC]
  · iframe FB4 FC
  ihave L5 := join64' (a := s.toNat - 44) (b := s.toNat - 40) x0 x1 (by omega) $$ [FA4 FB0]
  · iframe FA4 FB0
  ihave L4 := memBytes_addr (show s.toNat - 36 = (s - 64 + 16 + 12).toNat by simp [UInt32.toNat_add, h64]; omega) $$ L4
  ihave Ho16 := memBytes_addr (show out.toNat + 16 = (out + 16).toNat by simp [UInt32.toNat_add]; omega) $$ Ho16
  ihave Ho8 := memBytes_addr (show out.toNat + 8 = (out + 8).toNat by simp [UInt32.toNat_add]; omega) $$ Ho8
  mstep; mstep; mstep; mstep [FT]; mstep; mstep; mstep
  mstep; mstep; mstep [R12]; mstep; mstep
  mstep; mstep; mstep; mstep; mstep; mstep [L4]; mstep
  mstep; mstep [L5]; mstep
  rw [ofNat_decode_pair, ofNat_decode_pair]
  mstep; mstep; mstep [Ho0]
  mstep; mstep; mstep; mstep; mstep [Ho16]
  mstep; mstep; mstep; mstep; mstep [Ho8]
  rw [storeBytes_pair64, storeBytes_pair64]
  mstep; mstep; mstep; mstep; mstep [Hg]
  rw [show s - 64 + 64 = s by simp]
  mcredits R
  iframe Hc
  iunfold post376
  isplitr
  · ipureintro; simp [htype]
  ihave Ho16 := memBytes_addr (show (out + 16).toNat = out.toNat + 16 by simp [UInt32.toNat_add]; omega) $$ Ho16
  ihave Ho8 := memBytes_addr (show (out + 8).toNat = out.toNat + 8 by simp [UInt32.toNat_add]; omega) $$ Ho8
  iframe Hg B0 B1 Ho0 Ho4 Ho8 Ho16
  ihave L4 := memBytes_addr (show (s - 64 + 16 + 12).toNat = s.toNat - 36 by simp [UInt32.toNat_add, h64]; omega) $$ L4
  ihave Lo := stk_addr (show (s - 64).toNat - 48 = s.toNat - 112 by omega) $$ Lo
  ihave R8 := stk_word n _ _ $$ R8
  ihave R12 := stk_word n _ _ $$ R12
  ihave FA0 := stk_word n _ _ $$ FA0
  ihave FT := stk_word n _ _ $$ FT
  ihave FG := stk_word n _ _ $$ FG
  ihave X0 := stk_word n _ _ $$ X0
  ihave X1 := stk_word n _ _ $$ X1
  ihave Y0 := stk_word n _ _ $$ Y0
  ihave Y1 := stk_word n _ _ $$ Y1
  ihave L4 := VecFromElem.stk_intro n _ _ $$ L4
  ihave L5 := VecFromElem.stk_intro n _ _ $$ L5
  ihave X := stkJ (n := n) (show s.toNat - 64 = s.toNat - 112 + 48 by omega) $$ [Lo U0]
  · iframe Lo U0
  ihave X := stkJ (n := n) (show s.toNat - 56 = s.toNat - 112 + (48 + 8) by omega) $$ [X R8]
  · iframe X R8
  ihave X := stkJ (n := n) (show s.toNat - 52 = s.toNat - 112 + (48 + 8 + 4) by omega) $$ [X R12]
  · iframe X R12
  ihave X := stkJ (n := n) (show s.toNat - 48 = s.toNat - 112 + (48 + 8 + 4 + 4) by omega) $$ [X FA0]
  · iframe X FA0
  ihave X := stkJ (n := n) (show s.toNat - 44 = s.toNat - 112 + (48 + 8 + 4 + 4 + 4) by omega) $$ [X L5]
  · iframe X L5
  ihave X := stkJ (n := n) (show s.toNat - 36 = s.toNat - 112 + (48 + 8 + 4 + 4 + 4 + (bytes32 x0 ++ bytes32 x1).length) by simp [bytes32]; omega) $$ [X L4]
  · iframe X L4
  ihave X := stkJ (n := n) (show s.toNat - 28 = s.toNat - 112 + (48 + 8 + 4 + 4 + 4 + (bytes32 x0 ++ bytes32 x1).length + (bytes32 y0 ++ bytes32 y1).length) by simp [bytes32]; omega) $$ [X FD]
  · iframe X FD
  ihave X := stkJ (n := n) (show s.toNat - 24 = s.toNat - 112 + (48 + 8 + 4 + 4 + 4 + (bytes32 x0 ++ bytes32 x1).length + (bytes32 y0 ++ bytes32 y1).length + 4) by simp [bytes32]; omega) $$ [X FT]
  · iframe X FT
  ihave X := stkJ (n := n) (show s.toNat - 20 = s.toNat - 112 + (48 + 8 + 4 + 4 + 4 + (bytes32 x0 ++ bytes32 x1).length + (bytes32 y0 ++ bytes32 y1).length + 4 + 4) by simp [bytes32]; omega) $$ [X FG]
  · iframe X FG
  ihave X := stkJ (n := n) (show s.toNat - 16 = s.toNat - 112 + (48 + 8 + 4 + 4 + 4 + (bytes32 x0 ++ bytes32 x1).length + (bytes32 y0 ++ bytes32 y1).length + 4 + 4 + 4) by simp [bytes32]; omega) $$ [X X0]
  · iframe X X0
  ihave X := stkJ (n := n) (show s.toNat - 12 = s.toNat - 112 + (48 + 8 + 4 + 4 + 4 + (bytes32 x0 ++ bytes32 x1).length + (bytes32 y0 ++ bytes32 y1).length + 4 + 4 + 4 + 4) by simp [bytes32]; omega) $$ [X X1]
  · iframe X X1
  ihave X := stkJ (n := n) (show s.toNat - 8 = s.toNat - 112 + (48 + 8 + 4 + 4 + 4 + (bytes32 x0 ++ bytes32 x1).length + (bytes32 y0 ++ bytes32 y1).length + 4 + 4 + 4 + 4 + 4) by simp [bytes32]; omega) $$ [X Y0]
  · iframe X Y0
  ihave X := stkJ (n := n) (show s.toNat - 4 = s.toNat - 112 + (48 + 8 + 4 + 4 + 4 + (bytes32 x0 ++ bytes32 x1).length + (bytes32 y0 ++ bytes32 y1).length + 4 + 4 + 4 + 4 + 4 + 4) by simp [bytes32]; omega) $$ [X Y1]
  · iframe X Y1
  iapply stkL (n := n) rfl (by simp [bytes32]) $$ X

end S376

/-! ## `LookupMap::deserialize_value` (398): `u128::try_from_slice(..).expect(..)` -/

section S398

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The code of 398 (persistent). -/
def code398 (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) : IProp GF :=
  iprop(code376 inst mi A ∗ A 376 ↪[wf] FuncInst.wasm types[31]! inst f376)

instance (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) : Persistent (code398 (GF := GF) inst mi A) := by
  unfold code398; infer_instance

def pre398 (n g : Nat) (gt : GlobalType) (s out ptr : UInt32) (b0 b1 ob : List UInt8) (args : List Value) :
    IProp GF :=
  iprop(⌜args = [.i32 out, .i32 ptr, .i32 16]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 144) 144 ∗
    n ↦[wms][ ptr.toNat ] b0 ∗ n ↦[wms][ ptr.toNat + 8 ] b1 ∗ n ↦[wms][ out.toNat ] ob)

/-- The `u128` `b0 ++ b1` at `out`. -/
def post398 (n g : Nat) (gt : GlobalType) (s out ptr : UInt32) (b0 b1 : List UInt8) (_args rs : List Value) :
    IProp GF :=
  iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 144) 144 ∗
    n ↦[wms][ ptr.toNat ] b0 ∗ n ↦[wms][ ptr.toNat + 8 ] b1 ∗
    n ↦[wms][ out.toNat ] b0 ∗ n ↦[wms][ out.toNat + 8 ] b1)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **`LookupMap::deserialize_value`** (398) on the 16-byte slice `b0 ++ b1` at `ptr`: the `u128` it holds. -/
theorem f398_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 3 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s out ptr : UInt32) (b0 b1 ob : List UInt8) (hs : 144 ≤ s.toNat)
    (hb0 : b0.length = 8) (hb1 : b1.length = 8) (hob : ob.length = 16)
    (hout : out.toNat + 16 ≤ 2 ^ 32) (hptr : ptr.toNat + 16 ≤ 2 ^ 32) :
    code398 inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f398 Cg
        (pre398 n g gt s out ptr b0 b1 ob)
        (fun _ => 288 * cfg.regularOpCost)
        (post398 n g gt s out ptr b0 b1) := by
  iintro #Hk
  ihave #H376c : code376 inst mi A $$ []
  · iunfold code398 at Hk; icases Hk with ⟨#H, -⟩; iexact H
  ihave #H376 : A 376 ↪[wf] FuncInst.wasm types[31]! inst f376 $$ []
  · iunfold code398 at Hk; icases Hk with ⟨-, #H⟩; iexact H
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold code376, BorshInt.rdCode at H376c; icases H376c with ⟨⟨#H, -⟩, -⟩; iexact H
  have hn := hm.mem
  have hg := hm.glob
  have ha376 := hm.funcs 376 (by decide)
  have t31 : types[31]!.params.length = 3 := by rfl
  have hlt := s.toNat_lt
  have h32 : (s - 32).toNat = s.toNat - 32 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold pre398 at HP
  icases HP with ⟨%hargs, Hg, Hs, B0, B1, Ho⟩
  subst hargs
  icases stk_split n (s.toNat - 144) 112 32 $$ Hs with ⟨Lo, Fr⟩
  rw [show s.toNat - 144 + 112 = s.toNat - 32 by omega]
  icases stk_split n (s.toNat - 32) 8 24 $$ Fr with ⟨U0, Fr⟩
  rw [show s.toNat - 32 + 8 = s.toNat - 24 by omega]
  iunfold stk at Fr
  icases Fr with ⟨%fb, %hfb, Fr⟩
  simp only [f398]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep; mstep; mstep; mstep
  mcall (f376_spec cfg lim (d + 1) types[31]! (by rfl) inst mi A n g ta hm (by omega) Cg gt (s - 32) (s - 32 + 8)
      ptr b0 b1 fb (by omega) hb0 hb1 hfb (by simp [UInt32.toNat_add, h32]; omega) hptr)
      using [Hg Lo B0 B1 Fr]
  · iunfold pre376
    ihave Lo := stk_addr (show s.toNat - 144 = (s - 32).toNat - 112 by omega) $$ Lo
    ihave Fr := memBytes_addr (show s.toNat - 24 = (s - 32 + 8).toNat by simp [UInt32.toNat_add, h32]; omega) $$ Fr
    iframe Hg Lo B0 B1 Fr
    ipureintro; rfl
  iunfold post376 at HQ
  icases HQ with ⟨%hrs, Hg, Lo, B0, B1, T0, T4, T8, T16⟩
  subst hrs
  ihave T0 := memBytes_addr (show (s - 32 + 8).toNat = s.toNat - 24 by simp [UInt32.toNat_add, h32]; omega) $$ T0
  ihave T8 := memBytes_addr (show (s - 32 + 8).toNat + 8 = s.toNat - 16 by simp [UInt32.toNat_add, h32]; omega) $$ T8
  ihave T16 := memBytes_addr (show (s - 32 + 8).toNat + 16 = (s - 32 + 24).toNat by simp [UInt32.toNat_add, h32]; omega) $$ T16
  ihave Ho := U128From.memBytes_split n out.toNat 8 ob (by omega) $$ Ho
  icases Ho with ⟨O0, O8⟩
  mstep; mstep; mstep [T0]; mstep; mstep; mstep
  mstep; mstep [T8]; mstep; mstep; mstep; mstep; mstep; mstep [T16]; mstep [O8]
  rw [BorshLeaves.storeBytes_i64_decode _ hb1]
  mstep; mstep; mstep [O0]
  rw [BorshLeaves.storeBytes_i64_decode _ hb0]
  mstep; mstep; mstep; mstep [Hg]
  rw [show s - 32 + 32 = s by simp]
  mcredits R
  iframe Hc
  iunfold post398
  isplitr
  · ipureintro; simp [htype]
  iframe Hg B0 B1 O0 O8
  ihave T4 := memBytes_addr (show (s - 32 + 8).toNat + 4 = s.toNat - 20 by simp [UInt32.toNat_add, h32]; omega) $$ T4
  ihave T16 := memBytes_addr (show (s - 32 + 24).toNat = s.toNat - 8 by simp [UInt32.toNat_add, h32]; omega) $$ T16
  ihave Lo := stk_addr (show (s - 32).toNat - 112 = s.toNat - 144 by omega) $$ Lo
  ihave T0 := stk_word n _ _ $$ T0
  ihave T4 := VecFromElem.stk_intro n _ _ $$ T4
  ihave T8 := VecFromElem.stk_intro n _ _ $$ T8
  ihave T16 := VecFromElem.stk_intro n _ _ $$ T16
  ihave X := stkJ (n := n) (show s.toNat - 32 = s.toNat - 144 + 112 by omega) $$ [Lo U0]
  · iframe Lo U0
  ihave X := stkJ (n := n) (show s.toNat - 24 = s.toNat - 144 + (112 + 8) by omega) $$ [X T0]
  · iframe X T0
  ihave X := stkJ (n := n) (show s.toNat - 20 = s.toNat - 144 + (112 + 8 + 4) by omega) $$ [X T4]
  · iframe X T4
  ihave X := stkJ (n := n) (show s.toNat - 16 = s.toNat - 144 + (112 + 8 + 4 + (List.take 4 (List.drop 4 fb)).length) by simp; omega) $$ [X T8]
  · iframe X T8
  ihave X := stkJ (n := n) (show s.toNat - 8 = s.toNat - 144 + (112 + 8 + 4 + (List.take 4 (List.drop 4 fb)).length + b0.length) by simp; omega) $$ [X T16]
  · iframe X T16
  iapply stkL (n := n) rfl (by simp; omega) $$ X

end S398

end WNear.Binary.LookupMapBorsh
