import Bridge.Functions.BorshSer
import Bridge.Functions.BorshFT
import Binary.Code.Part07

/-!
# The Borsh leaves of the `LookupMap` path (377, 395, 378, 397, 376, 398)

```wat
;; 377 <String as BorshSerialize> into a fresh Vec (out, v): sp -= 32
;;     373(sp + 16, 1024)                   ;; Vec::with_capacity(1024) at sp + 16
;;     779(sp + 8, v)                       ;; (ptr, len) of the String
;;     [sp+28] := len; 711(sp + 16, sp + 28, 4); 711(sp + 16, ptr, len)
;;     out := 0 (Ok); out+12 := [sp+24]; out+4 := [sp+16] (i64); sp += 32
;; 395 try_to_vec (out, v): sp -= 16; 377(sp, v); tag = 1 → panic (521, not taken)
;;     out := [sp+4] (i64); out+8 := [sp+12]; sp += 16
```

* `f377_spec` / `f395_spec`: the `String` `(p, c, L)` at `v` serialized as Borsh
  (`bytes32 L ++ pre`) into a fresh 1024-byte block `q` (`grown`).
-/

namespace WNear.Binary.LookupMapBorsh

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_word stk_addr roomFor)
open WNear.Binary.VecWithCap (vecCode2 pre373 post373 costAllocF okG)
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.AllocInv (heapInv)
open WNear.Binary.FmtSink (grown heapAfter_grown roomPre roomPost)
open WNear.Binary.VecAppend (appCode f711_room)
open WNear.Binary.BorshSer (serCode)

section S377

variable {GF : BundledGFunctors} [WasmGS NearState GF]

theorem stkJ {n a b k1 k2 : Nat} (h : b = a + k1) :
    stk (GF := GF) n a k1 ∗ stk n b k2 ⊢ stk n a (k1 + k2) := by
  subst h; exact stk_join n a k1 k2

theorem stkL {n a a' k k' : Nat} (ha : a = a') (hk : k = k') : stk (GF := GF) n a k ⊢ stk n a' k' := by
  subst ha hk; exact .rfl

/-- The code of 377 (persistent). -/
def code377 (n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) : IProp GF :=
  iprop(vecCode2 n maxP inst mi A ∗ serCode inst mi A)

instance (n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) : Persistent (code377 (GF := GF) n maxP inst mi A) := by
  unfold code377; infer_instance

def pre377 (n g : Nat) (gt : GlobalType) (s out v p c L : UInt32) (idx : UInt32) (ta a578 maxP len : Nat)
    (live : List (Nat × Nat)) (F : Nat) (pre ob : List UInt8) (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 out, .i32 v]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 112) 112 ∗
    vt n 1057464 idx ta a578 ∗ heapInv n maxP len live F ∗
    n ↦[wms][ v.toNat ] (bytes32 p ++ (bytes32 c ++ bytes32 L)) ∗ n ↦[wms][ p.toNat ] pre ∗
    n ↦[wms][ out.toNat ] ob)

/-- `Ok(vec)` at `out`: the 1024-byte block `q` holding `bytes32 L ++ pre`, then the rest. -/
def post377 (n g : Nat) (gt : GlobalType) (s out v p c L : UInt32) (idx : UInt32) (ta a578 maxP len : Nat)
    (live : List (Nat × Nat)) (F : Nat) (pre : List UInt8) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 112) 112 ∗ vt n 1057464 idx ta a578 ∗
    n ↦[wms][ v.toNat ] (bytes32 p ++ (bytes32 c ++ bytes32 L)) ∗ n ↦[wms][ p.toNat ] pre ∗
    ∃ (q : UInt32) (rest : List UInt8), ⌜q ≠ 0 ∧ q.toNat + 1024 < 2 ^ 32 ∧ rest.length = 1024 - (4 + L.toNat)⌝ ∗
      grown n maxP len live F q 1024 ∗
      n ↦[i32][ out.toNat ] 0 ∗ n ↦[wms][ out.toNat + 4 ] (bytes32 q ++ bytes32 1024) ∗
      n ↦[i32][ out.toNat + 12 ] (0 + 4 + L) ∗
      n ↦[wms][ q.toNat ] (bytes32 L ++ pre) ∗ n ↦[wms][ q.toNat + (4 + L.toNat) ] rest)

/-- The cost of 377, activation excluded. -/
def cost377 (cfg : WasmConfig) (F : Nat) (L : UInt32) : Nat :=
  572 * cfg.regularOpCost + costAllocF cfg F 1024 + (MemCpy.cost 4 + MemCpy.cost L.toNat) * cfg.regularOpCost

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **`<String as BorshSerialize>` into a fresh `Vec`** (377): `Vec::with_capacity(1024)`, the length
as a `u32`, the bytes; `Ok(vec)` at `out`. -/
theorem f377_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 12 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s out v p c L : UInt32) (idx : UInt32) (maxP len : Nat) (live : List (Nat × Nat))
    (F : Nat) (hF : okG F) (pre ob : List UInt8) (hs : 112 ≤ s.toNat)
    (hpre : pre.length = L.toNat) (hL : L.toNat + 4 ≤ 1024) (hob : ob.length = 16)
    (hout : out.toNat + 16 ≤ 2 ^ 32) (hv : v.toNat + 12 ≤ 2 ^ 32) (hp : p.toNat + L.toNat ≤ 2 ^ 32)
    (hr : roomFor len maxP 1024) :
    code377 n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f377 Cg
        (pre377 n g gt s out v p c L idx ta (A 578) maxP len live F pre ob)
        (fun _ => cost377 cfg F L)
        (post377 n g gt s out v p c L idx ta (A 578) maxP len live F pre) := by
  iintro #Hk
  ihave #Hv : vecCode2 n maxP inst mi A $$ []
  · iunfold code377 at Hk; icases Hk with ⟨#H, -⟩; iexact H
  ihave #Hs : serCode inst mi A $$ []
  · iunfold code377 at Hk; icases Hk with ⟨-, #H⟩; iexact H
  ihave #Ha : appCode inst mi A $$ []
  · iunfold serCode at Hs; icases Hs with ⟨#H, -⟩; iexact H
  ihave #H779 : A 779 ↪[wf] FuncInst.wasm types[14]! inst f779 $$ []
  · iunfold serCode at Hs; icases Hs with ⟨-, #H⟩; iexact H
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold appCode at Ha; icases Ha with ⟨-, -, -, -, -, -, #H⟩; iexact H
  ihave #H711 : A 711 ↪[wf] FuncInst.wasm types[31]! inst f711 $$ []
  · iunfold appCode at Ha; icases Ha with ⟨-, -, -, -, #H, -, -⟩; iexact H
  ihave #H373 : A 373 ↪[wf] FuncInst.wasm types[14]! inst f373 $$ []
  · iunfold vecCode2 at Hv
    icases Hv with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, #H, -⟩
    iexact H
  have hn := hm.mem
  have hg := hm.glob
  have ha373 := hm.funcs 373 (by decide)
  have ha779 := hm.funcs 779 (by decide)
  have ha711 := hm.funcs 711 (by decide)
  have t14 : types[14]!.params.length = 2 := by rfl
  have t31 : types[31]!.params.length = 3 := by rfl
  have hlt := s.toNat_lt
  have hLlt := L.toNat_lt
  have h32 : (s - 32).toNat = s.toNat - 32 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have e8 : (s - 32 + 8).toNat = s.toNat - 24 := by simp [UInt32.toNat_add, h32]; omega
  have e16 : (s - 32 + 16).toNat = s.toNat - 16 := by simp [UInt32.toNat_add, h32]; omega
  have e28 : (s - 32 + 28).toNat = s.toNat - 4 := by simp [UInt32.toNat_add, h32]; omega
  unfold cost377
  rw [show (MemCpy.cost 4 + MemCpy.cost L.toNat) * cfg.regularOpCost =
    78 * cfg.regularOpCost + MemCpy.cost L.toNat * cfg.regularOpCost by rw [Nat.add_mul]; rfl]
  generalize hA : costAllocF cfg F 1024 = KA
  generalize hM : MemCpy.cost L.toNat * cfg.regularOpCost = M
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold pre377 at HP
  icases HP with ⟨%hargs, Hg, Hs, Hvt, Hinv, Hv, Hp, Ho⟩
  subst hargs
  -- the stack: 373's 80, then our frame: U (8), O (8), V (12), LC (4)
  icases stk_split n (s.toNat - 112) 80 32 $$ Hs with ⟨Lo, Fr⟩
  rw [show s.toNat - 112 + 80 = s.toNat - 32 by omega]
  icases stk_split n (s.toNat - 32) 8 24 $$ Fr with ⟨U, Fr⟩
  icases stk_split n (s.toNat - 32 + 8) 8 16 $$ Fr with ⟨O, Fr⟩
  icases stk_split n (s.toNat - 32 + 8 + 8) 12 4 $$ Fr with ⟨V, LC⟩
  rw [show s.toNat - 32 + 8 = s.toNat - 24 by omega, show s.toNat - 24 + 8 = s.toNat - 16 by omega,
    show s.toNat - 16 + 12 = s.toNat - 4 by omega]
  iunfold stk at O V
  icases O with ⟨%obb, %hobb, O⟩
  icases V with ⟨%vb, %hvb, V⟩
  icases ReadRegister.stk4_word n _ $$ LC with ⟨%lc, LC⟩
  simp only [f377]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep; mstep; mstep
  mcall (VecWithCap.f373_spec cfg lim (d + 1) types[14]! (by rfl) inst mi A n g ta hm (by omega) Cg gt (s - 32)
      (s - 32 + 16) 1024 idx maxP len live vb hvb (by omega) (by decide) (fun _ => hr) F hF)
      using [Hg Lo Hvt Hinv V] with (rw [hA]; mstep_norm_full; omega)
  · iunfold pre373
    ihave Lo := stk_addr (show s.toNat - 112 = (s - 32).toNat - 80 by omega) $$ Lo
    ihave V := memBytes_addr (show s.toNat - 16 = (s - 32 + 16).toNat by omega) $$ V
    iframe Hg Lo Hvt Hinv V
    ipureintro; rfl
  rw [hA]
  iunfold post373 at HQ
  icases HQ with ⟨%hrs, %q, Hg, Lo, Hvt, V0, V4, V8, HA⟩
  subst hrs
  icases heapAfter_grown (by decide) $$ HA with ⟨%⟨hq0, hqb⟩, Hblk, Hgr⟩
  simp only [UInt32.reduceToNat] at hqb
  iunfold AllocInv.block at Hblk
  icases Hblk with ⟨%bs, %hbs, Hblk⟩
  simp only [UInt32.reduceToNat] at hbs
  ihave Hblk := U128From.memBytes_split n q.toNat 4 bs (by omega) $$ Hblk
  icases Hblk with ⟨Wo4, Hblk⟩
  ihave Hblk := U128From.memBytes_split n (q.toNat + 4) L.toNat (bs.drop 4) (by simp; omega) $$ Hblk
  icases Hblk with ⟨WoL, Rest⟩
  mstep; mstep; mstep; mstep
  mcall (VecDeref.f779_spec cfg lim (d + 1) types[14]! rfl inst mi n hn Cg (s - 32 + 8) v obb
      (bytes32 p ++ (bytes32 c ++ bytes32 L)) hobb (by simp)) using [O Hv]
  · iunfold VecDeref.pre
    rw [e8]
    iframe O Hv
    ipureintro; rfl
  iunfold VecDeref.post at HQ
  icases HQ with ⟨%hrs, O, Hv⟩
  subst hrs
  have hpl : (bytes32 p ++ (bytes32 c ++ bytes32 L)).take 4 ++ (bytes32 p ++ (bytes32 c ++ bytes32 L)).drop 8 =
      bytes32 p ++ bytes32 L := by
    have l4 : ∀ x : UInt32, (bytes32 x).length = 4 := fun x => by simp [bytes32]
    rw [List.take_left' (l4 p), ← List.append_assoc, List.drop_left' (by simp [l4])]
  rw [hpl, e8]
  ihave O := KeyGet.split64 n (s.toNat - 24) p L $$ O
  icases O with ⟨O0, O4⟩
  ihave O0 := memBytes_addr (show s.toNat - 24 = (s - 32).toNat + 8 by omega) $$ O0
  ihave O4 := memBytes_addr (show s.toNat - 24 + 4 = (s - 32).toNat + 12 by omega) $$ O4
  ihave LC := memBytes_addr (show s.toNat - 4 = (s - 32).toNat + 28 by omega) $$ LC
  mstep; mstep [O0]; mstep; mstep; mstep; mstep [O4]; mstep; mstep [LC]
  mstep; mstep; mstep; mstep; mstep; mstep; mstep
  icases stk_split n ((s - 32).toNat - 80) 64 16 $$ Lo with ⟨Lo, Fr16⟩
  ihave Fr16 := stk_addr (show (s - 32).toNat - 80 + 64 = (s - 32).toNat - 16 by omega) $$ Fr16
  have h16' : 16 ≤ (s - 32).toNat := by omega
  mcall (f711_room (GF := GF) cfg lim (d + 1) types[31]! (by rfl) inst mi A n g ta hm (by omega) Cg
      gt (s - 32) (s - 32 + 16) q 1024 0 (s - 32 + 28) 4 (bs.take 4) (bytes32 L) h16' (by simp; omega)
      (by simp [bytes32]) (by omega) (by simp) (by simp; omega) (by simp [UInt32.toNat_add]; omega))
      using [Hg Fr16 V0 V4 V8 Wo4 LC]
      with (simp only [show MemCpy.cost (UInt32.toNat 4) = 78 from rfl]; mstep_norm_full; omega)
  · iunfold roomPre
    ihave LC := memBytes_addr (show (s - 32).toNat + 28 = (s - 32 + 28).toNat by simp [UInt32.toNat_add]; omega) $$ LC
    simp only [UInt32.toNat_zero, Nat.add_zero]
    iframe Hg Fr16 V0 V4 V8 Wo4 LC
  icases HQ with ⟨%hrs, HQ⟩
  subst hrs
  iunfold roomPost at HQ
  icases HQ with ⟨Hg, Fr16, V0, V4, V8, Wo4, LC⟩
  simp only [show MemCpy.cost 4 = 78 from rfl, Nat.reduceAdd]
  mstep; mstep; mstep; mstep; mstep
  have hM' : (11 + (115 + MemCpy.cost L.toNat)) * cfg.regularOpCost = 126 * cfg.regularOpCost + M := by
    rw [← hM, Nat.add_mul, Nat.add_mul]; omega
  ihave WoL := memBytes_addr (show q.toNat + 4 = q.toNat + (0 + 4 : UInt32).toNat by simp) $$ WoL
  mcall (f711_room (GF := GF) cfg lim (d + 1) types[31]! (by rfl) inst mi A n g ta hm (by omega) Cg
      gt (s - 32) (s - 32 + 16) q 1024 (0 + 4) p L ((bs.drop 4).take L.toNat) pre h16' (by simp; omega) hpre
      (by omega) (by simp; omega) (by simp; omega) hp)
      using [Hg Fr16 V0 V4 V8 WoL Hp] with (mstep_norm_full; rw [hM']; omega)
  · iunfold roomPre
    iframe Hg Fr16 V0 V4 V8 WoL Hp
  icases HQ with ⟨%hrs, HQ⟩
  subst hrs
  iunfold roomPost at HQ
  icases HQ with ⟨Hg, Fr16, V0, V4, V8, WoL, Hp⟩
  simp only [hM']
  ihave Ho := U128From.memBytes_split n out.toNat 4 ob (by omega) $$ Ho
  icases Ho with ⟨Q0, Ho⟩
  ihave Ho := U128From.memBytes_split n (out.toNat + 4) 8 (ob.drop 4) (by simp; omega) $$ Ho
  icases Ho with ⟨Q4, Q12⟩
  have hob0 : (ob.take 4).length = 4 := by simp; omega
  have hob4 : ((ob.drop 4).take 8).length = 8 := by simp; omega
  have hob12 : ((ob.drop 4).drop 8).length = 4 := by simp; omega
  ihave V01 := KeyGet.join64 n (s - 32 + 16).toNat q 1024 $$ [V0 V4]
  · iframe V0 V4
  ihave V01 := memBytes_addr (show (s - 32 + 16).toNat = (s - 32).toNat + 16 by omega) $$ V01
  ihave V8 := memBytes_addr (show (s - 32 + 16).toNat + 8 = (s - 32 + 24).toNat by simp [UInt32.toNat_add, h32]; omega) $$ V8
  ihave Q12 := memBytes_addr (show out.toNat + 4 + 8 = (out + 12).toNat by simp [UInt32.toNat_add]; omega) $$ Q12
  mstep; mstep; mstep [Q0]
  mstep; mstep; mstep; mstep; mstep; mstep; mstep [V8]; mstep [Q12]
  mstep; mstep; mstep [V01]; mstep [Q4]
  rw [BorshLeaves.storeBytes_i64_decode _ (by simp [bytes32])]
  mstep; mstep; mstep; mstep [Hg]
  rw [show s - 32 + 32 = s by simp]
  mcredits R
  iframe Hc
  iunfold post377
  isplitr
  · ipureintro; simp [htype]
  iframe Hg Hvt Hv Hp
  isplitl [Lo Fr16 U O0 O4 V01 V8 LC]
  · ihave Lo := stk_join n ((s - 32).toNat - 80) 64 16 $$ [Lo Fr16]
    · rw [show (s - 32).toNat - 80 + 64 = (s - 32).toNat - 16 by omega]; iframe Lo Fr16
    ihave Lo := stk_addr (show (s - 32).toNat - 80 = s.toNat - 112 by omega) $$ Lo
    ihave O := KeyGet.join64 n ((s - 32).toNat + 8) p L $$ [O0 O4]
    · iframe O0 O4
    ihave O := VecFromElem.stk_intro n _ _ $$ O
    ihave V8 := stk_word n _ _ $$ V8
    ihave LC := stk_word n _ _ $$ LC
    ihave V01 := VecFromElem.stk_intro n _ _ $$ V01
    ihave X := stkJ (n := n) (show s.toNat - 32 = s.toNat - 112 + 80 by omega) $$ [Lo U]
    · iframe Lo U
    ihave X := stkJ (n := n) (show (s - 32).toNat + 8 = s.toNat - 112 + (80 + 8) by omega) $$ [X O]
    · iframe X O
    ihave X := stkJ (n := n) (show (s - 32).toNat + 16 = s.toNat - 112 + (80 + 8 + (bytes32 p ++ bytes32 L).length) by simp [bytes32]; omega) $$ [X V01]
    · iframe X V01
    ihave X := stkJ (n := n) (show (s - 32 + 24).toNat = s.toNat - 112 + (80 + 8 + (bytes32 p ++ bytes32 L).length + (bytes32 q ++ bytes32 1024).length) by simp [bytes32, UInt32.toNat_add, h32]; omega) $$ [X V8]
    · iframe X V8
    ihave X := stkJ (n := n) (show (s - 32 + 28).toNat = s.toNat - 112 + (80 + 8 + (bytes32 p ++ bytes32 L).length + (bytes32 q ++ bytes32 1024).length + 4) by simp [bytes32, UInt32.toNat_add, h32]; omega) $$ [X LC]
    · iframe X LC
    iapply stkL (n := n) rfl (by simp [bytes32]) $$ X
  iexists q, (bs.drop 4).drop L.toNat
  isplitr
  · ipureintro; exact ⟨hq0, hqb, by simp; omega⟩
  ihave Q12 := memBytes_addr (show (out + 12).toNat = out.toNat + 12 by simp [UInt32.toNat_add]; omega) $$ Q12
  ihave WoL := memBytes_addr (show q.toNat + (0 + 4 : UInt32).toNat = q.toNat + 4 by simp) $$ WoL
  iframe Hgr Q0 Q4 Q12
  isplitl [Wo4 WoL]
  · iapply BorshFT.joinB (n := n) (a := q.toNat) (b := q.toNat + 4) (bytes32 L) pre (by simp [bytes32])
    iframe Wo4 WoL
  iapply memBytes_addr (show q.toNat + 4 + L.toNat = q.toNat + (4 + L.toNat) by omega) $$ Rest

/-- The code of 395 (persistent). -/
def code395 (n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) : IProp GF :=
  iprop(code377 n maxP inst mi A ∗ A 377 ↪[wf] FuncInst.wasm types[14]! inst f377)

instance (n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) : Persistent (code395 (GF := GF) n maxP inst mi A) := by
  unfold code395; infer_instance

def pre395 (n g : Nat) (gt : GlobalType) (s out v p c L : UInt32) (idx : UInt32) (ta a578 maxP len : Nat)
    (live : List (Nat × Nat)) (F : Nat) (pre ob : List UInt8) (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 out, .i32 v]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 128) 128 ∗
    vt n 1057464 idx ta a578 ∗ heapInv n maxP len live F ∗
    n ↦[wms][ v.toNat ] (bytes32 p ++ (bytes32 c ++ bytes32 L)) ∗ n ↦[wms][ p.toNat ] pre ∗
    n ↦[wms][ out.toNat ] ob)

/-- The `Vec` `(q, 1024, 4 + L)` at `out`, `q` holding `bytes32 L ++ pre`, then the rest. -/
def post395 (n g : Nat) (gt : GlobalType) (s out v p c L : UInt32) (idx : UInt32) (ta a578 maxP len : Nat)
    (live : List (Nat × Nat)) (F : Nat) (pre : List UInt8) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 128) 128 ∗ vt n 1057464 idx ta a578 ∗
    n ↦[wms][ v.toNat ] (bytes32 p ++ (bytes32 c ++ bytes32 L)) ∗ n ↦[wms][ p.toNat ] pre ∗
    ∃ (q : UInt32) (rest : List UInt8), ⌜q ≠ 0 ∧ q.toNat + 1024 < 2 ^ 32 ∧ rest.length = 1024 - (4 + L.toNat)⌝ ∗
      grown n maxP len live F q 1024 ∗
      n ↦[i32][ out.toNat ] q ∗ n ↦[i32][ out.toNat + 4 ] 1024 ∗ n ↦[i32][ out.toNat + 8 ] (0 + 4 + L) ∗
      n ↦[wms][ q.toNat ] (bytes32 L ++ pre) ∗ n ↦[wms][ q.toNat + (4 + L.toNat) ] rest)

/-- The cost of 395, activation excluded. -/
def cost395 (cfg : WasmConfig) (F : Nat) (L : UInt32) : Nat := 39 * cfg.regularOpCost + cost377 cfg F L

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **`BorshSerialize::try_to_vec`** (395) of the `String` at `v`: 377, the `Vec` unwrapped. -/
theorem f395_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 13 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s out v p c L : UInt32) (idx : UInt32) (maxP len : Nat) (live : List (Nat × Nat))
    (F : Nat) (hF : okG F) (pre ob : List UInt8) (hs : 128 ≤ s.toNat)
    (hpre : pre.length = L.toNat) (hL : L.toNat + 4 ≤ 1024) (hob : ob.length = 12)
    (hout : out.toNat + 12 ≤ 2 ^ 32) (hv : v.toNat + 12 ≤ 2 ^ 32) (hp : p.toNat + L.toNat ≤ 2 ^ 32)
    (hr : roomFor len maxP 1024) :
    code395 n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f395 Cg
        (pre395 n g gt s out v p c L idx ta (A 578) maxP len live F pre ob)
        (fun _ => cost395 cfg F L)
        (post395 n g gt s out v p c L idx ta (A 578) maxP len live F pre) := by
  iintro #Hk
  ihave #H377c : code377 n maxP inst mi A $$ []
  · iunfold code395 at Hk; icases Hk with ⟨#H, -⟩; iexact H
  ihave #H377 : A 377 ↪[wf] FuncInst.wasm types[14]! inst f377 $$ []
  · iunfold code395 at Hk; icases Hk with ⟨-, #H⟩; iexact H
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold code377, serCode, appCode at H377c
    icases H377c with ⟨-, ⟨⟨-, -, -, -, -, -, #H⟩, -⟩⟩; iexact H
  have hn := hm.mem
  have hg := hm.glob
  have ha377 := hm.funcs 377 (by decide)
  have t14 : types[14]!.params.length = 2 := by rfl
  have hlt := s.toNat_lt
  have h16 : (s - 16).toNat = s.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  unfold cost395
  generalize hK : cost377 cfg F L = K
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold pre395 at HP
  icases HP with ⟨%hargs, Hg, Hs, Hvt, Hinv, Hv, Hp, Ho⟩
  subst hargs
  icases stk_split n (s.toNat - 128) 112 16 $$ Hs with ⟨Lo, Fr⟩
  rw [show s.toNat - 128 + 112 = s.toNat - 16 by omega]
  iunfold stk at Fr
  icases Fr with ⟨%fb, %hfb, Fr⟩
  simp only [f395]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep
  mcall (f377_spec cfg lim (d + 1) types[14]! (by rfl) inst mi A n g ta hm (by omega) Cg gt (s - 16) (s - 16) v p c L
      idx maxP len live F hF pre fb (by omega) hpre hL hfb (by omega) hv hp hr)
      using [Hg Lo Hvt Hinv Hv Hp Fr] with (rw [hK]; mstep_norm_full; omega)
  · iunfold pre377
    ihave Lo := stk_addr (show s.toNat - 128 = (s - 16).toNat - 112 by omega) $$ Lo
    ihave Fr := memBytes_addr (show s.toNat - 16 = (s - 16).toNat by omega) $$ Fr
    iframe Hg Lo Hvt Hinv Hv Hp Fr
    ipureintro; rfl
  rw [hK]
  iunfold post377 at HQ
  icases HQ with ⟨%hrs, Hg, Lo, Hvt, Hv, Hp, %q, %rest, %⟨hq0, hqb, hrest⟩, Hgr, T0, T4, T12, Wo, Rest⟩
  subst hrs
  ihave Ho := U128From.memBytes_split n out.toNat 8 ob (by omega) $$ Ho
  icases Ho with ⟨Q0, Q8⟩
  ihave Q8 := memBytes_addr (show out.toNat + 8 = (out + 8).toNat by simp [UInt32.toNat_add]; omega) $$ Q8
  ihave T12 := memBytes_addr (show (s - 16).toNat + 12 = (s - 16 + 12).toNat by simp [UInt32.toNat_add, h16]; omega) $$ T12
  mstep; mstep; mstep [T0]; mstep; mstep; mstep
  mstep; mstep; mstep [T4]; mstep [Q0]
  rw [BorshLeaves.storeBytes_i64_decode _ (by simp [bytes32])]
  mstep; mstep; mstep; mstep; mstep; mstep; mstep [T12]; mstep [Q8]
  mstep; mstep; mstep; mstep [Hg]
  rw [show s - 16 + 16 = s by simp]
  mcredits R
  iframe Hc
  iunfold post395
  isplitr
  · ipureintro; simp [htype]
  iframe Hg Hvt Hv Hp
  isplitl [Lo T0 T4 T12]
  · ihave T0 := stk_word n _ _ $$ T0
    ihave T4 := VecFromElem.stk_intro n _ _ $$ T4
    ihave T12 := stk_word n _ _ $$ T12
    ihave X := stkJ (n := n) (show (s - 16).toNat = s.toNat - 128 + 112 by omega) $$ [Lo T0]
    · ihave Lo := stk_addr (show (s - 16).toNat - 112 = s.toNat - 128 by omega) $$ Lo
      iframe Lo T0
    ihave X := stkJ (n := n) (show (s - 16).toNat + 4 = s.toNat - 128 + (112 + 4) by omega) $$ [X T4]
    · iframe X T4
    ihave X := stkJ (n := n) (show (s - 16 + 12).toNat = s.toNat - 128 + (112 + 4 + (bytes32 q ++ bytes32 1024).length) by simp [bytes32, UInt32.toNat_add, h16]; omega) $$ [X T12]
    · iframe X T12
    iapply stkL (n := n) rfl (by simp [bytes32]) $$ X
  iexists q, rest
  isplitr
  · ipureintro; exact ⟨hq0, hqb, hrest⟩
  ihave Q8 := memBytes_addr (show (out + 8).toNat = out.toNat + 8 by simp [UInt32.toNat_add]; omega) $$ Q8
  icases KeyGet.split64 n out.toNat q 1024 $$ Q0 with ⟨Q0, Q4⟩
  iframe Hgr Q0 Q4 Q8 Wo Rest

end S377

end WNear.Binary.LookupMapBorsh
