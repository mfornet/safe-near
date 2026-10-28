import Bridge.Functions.VecAppend
import Bridge.Functions.BorshContract
import Bridge.Functions.VecDeref

/-!
# Borsh serialization of the contract state (48, 100, 164, 163)

```wat
;; 48 <Vec<u8> as BorshSerialize>::serialize(v, w) -> io::Result: sp -= 16
;;     779(sp, v)                        ;; (ptr, len)
;;     [sp+12] := len; 711(w, sp + 12, 4); 711(w, ptr, len); sp += 16; 3 (Ok)
```

* `f48_spec`: the `Vec<u8>` `(p, c, L)` at `v` appended to the `Vec` at `w` with room, as Borsh
  (`bytes32 L ++ pre`): `Ok` (3).
-/

namespace WNear.Binary.BorshSer

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_word stk_addr)
open WNear.Binary.FmtSink (roomPre roomPost)
open WNear.Binary.VecAppend (appCode f711_room)

section Spec

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The code of 48 (persistent). -/
def serCode (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) : IProp GF :=
  iprop(appCode inst mi A ∗ A 779 ↪[wf] FuncInst.wasm types[14]! inst f779)

instance (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) : Persistent (serCode (GF := GF) inst mi A) := by
  unfold serCode; infer_instance

/-- The writer `Vec` `(wp, wc, wl)` at `w`, with `ob` where the bytes go. -/
def writer (n : Nat) (w wp wc wl : UInt32) (ob : List UInt8) : IProp GF :=
  iprop(n ↦[i32][ w.toNat ] wp ∗ n ↦[i32][ w.toNat + 4 ] wc ∗ n ↦[i32][ w.toNat + 8 ] wl ∗
    n ↦[wms][ wp.toNat + wl.toNat ] ob)

def pre48 (n g : Nat) (gt : GlobalType) (s v w p c L wp wc wl : UInt32) (pre ob : List UInt8)
    (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 v, .i32 w]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 32) 32 ∗
    n ↦[wms][ v.toNat ] (bytes32 p ++ (bytes32 c ++ bytes32 L)) ∗ n ↦[wms][ p.toNat ] pre ∗
    writer n w wp wc wl ob)

def post48 (n g : Nat) (gt : GlobalType) (s v w p c L wp wc wl : UInt32) (pre : List UInt8)
    (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = [.i64 3]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 32) 32 ∗
    n ↦[wms][ v.toNat ] (bytes32 p ++ (bytes32 c ++ bytes32 L)) ∗ n ↦[wms][ p.toNat ] pre ∗
    n ↦[i32][ w.toNat ] wp ∗ n ↦[i32][ w.toNat + 4 ] wc ∗ n ↦[i32][ w.toNat + 8 ] (wl + 4 + L) ∗
    n ↦[wms][ wp.toNat + wl.toNat ] (bytes32 L ++ pre))

set_option maxHeartbeats 4000000 in
/-- **`<Vec<u8> as BorshSerialize>::serialize`** (48): the length as a `u32`, then the bytes. -/
theorem f48_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 6 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s v w p c L wp wc wl : UInt32) (pre ob : List UInt8) (hs : 32 ≤ s.toNat)
    (hal : s.toNat % 8 = 0) (hpre : pre.length = L.toNat) (hob : ob.length = 4 + L.toNat)
    (hv : v.toNat + 12 ≤ 2 ^ 32) (hw : w.toNat + 12 ≤ 2 ^ 32) (hroom : wl.toNat + 4 + L.toNat ≤ wc.toNat)
    (hwp : wp.toNat + wc.toNat < 2 ^ 32) (hp : p.toNat + L.toNat ≤ 2 ^ 32) :
    serCode inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f48 Cg (pre48 n g gt s v w p c L wp wc wl pre ob)
        (fun _ => 68 * cfg.regularOpCost + (115 * cfg.regularOpCost + MemCpy.cost 4 * cfg.regularOpCost) +
          (115 * cfg.regularOpCost + MemCpy.cost L.toNat * cfg.regularOpCost))
        (post48 n g gt s v w p c L wp wc wl pre) := by
  iintro #Hk
  ihave #Ha : appCode inst mi A $$ []
  · iunfold serCode at Hk; icases Hk with ⟨#H, -⟩; iexact H
  ihave #H779 : A 779 ↪[wf] FuncInst.wasm types[14]! inst f779 $$ []
  · iunfold serCode at Hk; icases Hk with ⟨-, #H⟩; iexact H
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold appCode at Ha; icases Ha with ⟨-, -, -, -, -, -, #H⟩; iexact H
  ihave #H711 : A 711 ↪[wf] FuncInst.wasm types[31]! inst f711 $$ []
  · iunfold appCode at Ha; icases Ha with ⟨-, -, -, -, #H, -, -⟩; iexact H
  have hn := hm.mem
  have hg := hm.glob
  have ha779 := hm.funcs 779 (by decide)
  have ha711 := hm.funcs 711 (by decide)
  have t14 : types[14]!.params.length = 2 := by rfl
  have t31 : types[31]!.params.length = 3 := by rfl
  have hlt := s.toNat_lt
  have h16 : (s - 16).toNat = s.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have e12 : (s - 16 + 12).toNat = s.toNat - 4 := by simp [UInt32.toNat_add, h16]; omega
  have hLlt := L.toNat_lt
  have hwl4 : (wl + 4).toNat = wl.toNat + 4 := by simp [UInt32.toNat_add]; omega
  have hwl4L : (wl + 4 + L).toNat = wl.toNat + 4 + L.toNat := by simp [UInt32.toNat_add]; omega
  have hob4 : (ob.take 4).length = 4 := by simp; omega
  have hobL : (ob.drop 4).length = L.toNat := by simp; omega
  have hm4 : MemCpy.cost 4 * cfg.regularOpCost = 78 * cfg.regularOpCost := rfl
  rw [hm4]
  generalize hM : MemCpy.cost L.toNat * cfg.regularOpCost = M
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold pre48 at HP
  icases HP with ⟨%hargs, Hg, Hs, Hv, Hp, Hw⟩
  subst hargs
  iunfold writer at Hw
  icases Hw with ⟨W0, W4, W8, Wo⟩
  ihave Wo := U128From.memBytes_split n (wp.toNat + wl.toNat) 4 ob (by omega) $$ Wo
  icases Wo with ⟨Wo4, WoL⟩
  -- the stack: 711's frame (16), then ours: O (8), U (4), the length cell (4)
  icases stk_split n (s.toNat - 32) 16 16 $$ Hs with ⟨Fr, Hs⟩
  icases stk_split n (s.toNat - 32 + 16) 8 8 $$ Hs with ⟨O, Hs⟩
  icases stk_split n (s.toNat - 32 + 16 + 8) 4 4 $$ Hs with ⟨U, LC⟩
  rw [show s.toNat - 32 + 16 = s.toNat - 16 by omega, show s.toNat - 16 + 8 = s.toNat - 8 by omega,
    show s.toNat - 8 + 4 = s.toNat - 4 by omega]
  iunfold stk at O
  icases O with ⟨%obb, %hobb, O⟩
  icases ReadRegister.stk4_word n _ $$ LC with ⟨%lc, LC⟩
  simp only [f48]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep
  mcall (VecDeref.f779_spec cfg lim (d + 1) types[14]! rfl inst mi n hn Cg (s - 16) v obb
      (bytes32 p ++ (bytes32 c ++ bytes32 L)) hobb (by simp)) using [O Hv]
  · iunfold VecDeref.pre
    rw [h16]
    iframe O Hv
    ipureintro; rfl
  iunfold VecDeref.post at HQ
  icases HQ with ⟨%hrs, O, Hv⟩
  subst hrs
  have hpl : (bytes32 p ++ (bytes32 c ++ bytes32 L)).take 4 ++ (bytes32 p ++ (bytes32 c ++ bytes32 L)).drop 8 =
      bytes32 p ++ bytes32 L := by
    have l4 : ∀ x : UInt32, (bytes32 x).length = 4 := fun x => by simp [bytes32]
    rw [List.take_left' (l4 p), ← List.append_assoc, List.drop_left' (by simp [l4])]
  rw [hpl, h16]
  ihave O := KeyGet.split64 n (s.toNat - 16) p L $$ O
  icases O with ⟨O0, O4⟩
  ihave O0 := memBytes_addr (show s.toNat - 16 = (s - 16).toNat by omega) $$ O0
  ihave O4 := memBytes_addr (show s.toNat - 16 + 4 = (s - 16).toNat + 4 by omega) $$ O4
  ihave LC := memBytes_addr (show s.toNat - 4 = (s - 16).toNat + 12 by omega) $$ LC
  mstep; mstep [O0]; mstep; mstep; mstep; mstep [O4]; mstep; mstep [LC]
  mstep; mstep; mstep; mstep; mstep
  have h16' : 16 ≤ (s - 16).toNat := by omega
  mcall (f711_room (GF := GF) cfg lim (d + 1) types[31]! (by rfl) inst mi A n g ta hm (by omega) Cg
      gt (s - 16) w wp wc wl (s - 16 + 12) 4 (ob.take 4) (bytes32 L) h16' hob4 (by simp [bytes32]) hw
      (by simp; omega) hwp (by simp [UInt32.toNat_add]; omega)) using [Hg Fr W0 W4 W8 Wo4 LC]
      with (simp only [show MemCpy.cost (UInt32.toNat 4) = 78 from rfl]; mstep_norm_full; omega)
  · iunfold roomPre
    ihave LC := memBytes_addr (show (s - 16).toNat + 12 = (s - 16 + 12).toNat by simp [UInt32.toNat_add]; omega) $$ LC
    ihave Fr := stk_addr (show s.toNat - 32 = (s - 16).toNat - 16 by omega) $$ Fr
    iframe Hg Fr W0 W4 W8 Wo4 LC
  icases HQ with ⟨%hrs, HQ⟩
  subst hrs
  iunfold roomPost at HQ
  icases HQ with ⟨Hg, Fr, W0, W4, W8, Wo4, LC⟩
  simp only [show MemCpy.cost 4 = 78 from rfl, Nat.reduceAdd]
  mstep; mstep; mstep
  have hM' : (11 + (115 + MemCpy.cost L.toNat)) * cfg.regularOpCost = 126 * cfg.regularOpCost + M := by
    rw [← hM, Nat.add_mul, Nat.add_mul]; omega
  ihave WoL := memBytes_addr (show wp.toNat + wl.toNat + 4 = wp.toNat + (wl + 4).toNat by omega) $$ WoL
  mcall (f711_room (GF := GF) cfg lim (d + 1) types[31]! (by rfl) inst mi A n g ta hm (by omega) Cg
      gt (s - 16) w wp wc (wl + 4) p L (ob.drop 4) pre h16' hobL hpre hw (by omega) hwp hp)
      using [Hg Fr W0 W4 W8 WoL Hp] with (mstep_norm_full; rw [hM']; omega)
  · iunfold roomPre
    iframe Hg Fr W0 W4 W8 WoL Hp
  icases HQ with ⟨%hrs, HQ⟩
  subst hrs
  iunfold roomPost at HQ
  icases HQ with ⟨Hg, Fr, W0, W4, W8, WoL, Hp⟩
  have hM'' : (245 + (11 + (115 + MemCpy.cost L.toNat))) * cfg.regularOpCost = 371 * cfg.regularOpCost + M := by
    rw [← hM, Nat.add_mul, Nat.add_mul, Nat.add_mul]; omega
  simp only [hM'']
  mstep; mstep; mstep; mstep [Hg]
  rw [show s - 16 + 16 = s by simp]
  mstep
  mcredits R
  iframe Hc
  iunfold post48
  isplitr
  · ipureintro; simp [htype]
  iframe Hg Hv Hp W0 W4 W8
  isplitr [Wo4 WoL]
  · ihave Fr := stk_addr (show (s - 16).toNat - 16 = s.toNat - 32 by omega) $$ Fr
    ihave O0 := stk_word n _ _ $$ O0
    ihave O4 := stk_word n _ _ $$ O4
    ihave LC := memBytes_addr (show (s - 16 + 12).toNat = s.toNat - 4 by simp [UInt32.toNat_add]; omega) $$ LC
    ihave LC := stk_word n _ _ $$ LC
    ihave O := stk_join n _ 4 4 $$ [O0 O4]
    · iframe O0 O4
    ihave O := stk_addr (show (s - 16).toNat = s.toNat - 16 by omega) $$ O
    ihave UL := stk_join n (s.toNat - 8) 4 4 $$ [U LC]
    · rw [show s.toNat - 8 + 4 = s.toNat - 4 by omega]; iframe U LC
    ihave OU := stk_join n (s.toNat - 16) 8 8 $$ [O UL]
    · rw [show s.toNat - 16 + 8 = s.toNat - 8 by omega]; iframe O UL
    iapply stk_join n (s.toNat - 32) 16 16
    rw [show s.toNat - 32 + 16 = s.toNat - 16 by omega]
    iframe Fr OU
  iapply BorshFT.joinB (n := n) (a := wp.toNat + wl.toNat) (b := wp.toNat + (wl + 4).toNat) (bytes32 L) pre
    (by simp [bytes32, hwl4]; omega)
  iframe Wo4 WoL

end Spec

end WNear.Binary.BorshSer
