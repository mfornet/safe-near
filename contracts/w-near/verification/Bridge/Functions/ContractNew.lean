import Bridge.Functions.MeasureUsage
import Bridge.Functions.StateWrite

/-!
# `FungibleToken::new` (107) and `Contract::new` (289)

```wat
;; 107 FungibleToken::new(out, prefix): out := 0 (i64); out+24 := prefix[0..8); out+8 := 0;
;;     out+16 := 0; out+32 := prefix[8..12); 404(out)    ;; measure_account_storage_usage
;; 289 Contract::new(out): sp -= 16; 94(sp, 1)            ;; Vec::with_capacity(1)
;;     [ptr] := 97 (u8); [sp+8] := 1; 107(out, sp); sp += 16
```

`f289_spec`: the `FungibleToken` at `out` (`ftAt`): `total_supply = 0`, the prefix `b"a"` in a
fresh one-byte block, `account_storage_usage = 85 + extra`; the host as `Post404`.
-/

namespace WNear.Binary.ContractNew

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open WNear.Binary.Interface (IfaceMod iface ifaceCode)
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_word stk_addr roomFor grownLen)
open WNear.Binary.VecWithCap (vecCode2 costAllocF okG pre373 post373)
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.AllocInv (heapInv)
open WNear.Binary.FmtSink (grown)
open WNear.Binary.StorageWrite (wslot evictedRegister)
open WNear.Binary.StorageRemove (rslot)
open WNear.Binary.ReadRegister (ifaceR)
open WNear.Binary.EnvGetters (uslot)
open WNear.Binary.BorshSer (ftAt)
open WNear.Binary.LookupMapLeaves (prefixAt)
open WNear.Binary.LookupMapOps (HeapRoomK LenIn lenIn_step lenIn_zero roomFor_ofK cost402)
open WNear.Binary.MeasureUsage (mKey mVal code404 pre404 post404 cost404 Post404 lenIn_trans heapRoom_shift)
open Near.TrieOverlay

section S107

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The code of 107 (persistent). -/
def code107 (e n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (mx : Option Nat) : IProp GF :=
  iprop(code404 e n maxP inst mi A mx ∗ A 404 ↪[wf] FuncInst.wasm types[0]! inst f404)

instance (e n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (mx : Option Nat) :
    Persistent (code107 (GF := GF) e n maxP inst mi A mx) := by
  unfold code107; infer_instance

/-- The resources 404 uses besides the contract: the stack, the interface, the heap, the statics, the
host. -/
def env404 (n g ta : Nat) (A : Nat → Nat) (gt : GlobalType) (s : UInt32) (idx : UInt32) (maxP len : Nat)
    (live : List (Nat × Nat)) (F : Nat) (h : NearState) : IProp GF :=
  iprop(g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 352) 352 ∗
    ifaceR n ta A ∗ uslot n ta A ∗ wslot n ta A ∗ rslot n ta A ∗ vt n 1057464 idx ta (A 578) ∗
    heapInv n maxP len live F ∗ n ↦[wms][ 1052792 ] [97] ∗ n ↦[wms][ 1052800 ] List.replicate 16 0 ∗
    mhostPt h)

/-- What 404 leaves of `env404`. -/
def env404' (n g ta : Nat) (A : Nat → Nat) (gt : GlobalType) (s : UInt32) (idx : UInt32) (maxP len : Nat)
    (live : List (Nat × Nat)) (F : Nat) (Q : NearState → Prop) : IProp GF :=
  iprop(g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 352) 352 ∗
    ifaceR n ta A ∗ uslot n ta A ∗ wslot n ta A ∗ rslot n ta A ∗ vt n 1057464 idx ta (A 578) ∗
    (∃ len', ⌜LenIn len 7 len'⌝ ∗ heapInv n maxP len' live (F + 7)) ∗
    n ↦[wms][ 1052792 ] [97] ∗ n ↦[wms][ 1052800 ] List.replicate 16 0 ∗ (∃ h', ⌜Q h'⌝ ∗ mhostPt h'))

def pre107 (n g ta : Nat) (A : Nat → Nat) (gt : GlobalType) (s out v q : UInt32) (idx : UInt32)
    (maxP len : Nat) (live : List (Nat × Nat)) (F : Nat) (ob : List UInt8) (h : NearState)
    (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 out, .i32 v]⌝ ∗ env404 n g ta A gt s idx maxP len live F h ∗
    n ↦[wms][ out.toNat ] ob ∗ n ↦[wms][ v.toNat ] (bytes32 q ++ (bytes32 1 ++ bytes32 1)) ∗
    n ↦[wms][ q.toNat ] [97])

def post107 (n g ta : Nat) (A : Nat → Nat) (gt : GlobalType) (s out v q : UInt32) (idx : UInt32)
    (maxP len : Nat) (live : List (Nat × Nat)) (F : Nat) (e : Nat) (Q : NearState → Prop)
    (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = []⌝ ∗ env404' n g ta A gt s idx maxP len live F Q ∗
    ftAt n out (List.replicate 8 0) (List.replicate 8 0) (storeBytes (.i64 (UInt64.ofNat (85 + e))) 8) q 1 ∗
    n ↦[wms][ v.toNat ] (bytes32 q ++ (bytes32 1 ++ bytes32 1)) ∗ n ↦[wms][ q.toNat ] [97])

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 16000000 in
/-- **`FungibleToken::new`** (107) with the prefix `Vec` `(q, 1, 1)` at `v` (`q` holding `"a"`). -/
theorem f107_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (e : Nat) (A : Nat → Nat) (n g ta : Nat)
    (mx : Option Nat) (hm : IfaceMod mi A n g ta) (hd : d + 20 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s out v q : UInt32) (idx : UInt32) (maxP len : Nat)
    (live : List (Nat × Nat)) (F : Nat) (hF : okG F) (ob : List UInt8)
    (hs : 352 ≤ s.toNat) (hal : s.toNat % 8 = 0) (hob : ob.length = 36) (hout : out.toNat + 36 ≤ 2 ^ 32)
    (hv : v.toNat + 12 ≤ 2 ^ 32) (hq : q.toNat + 1 ≤ 2 ^ 32) (hroom : HeapRoomK 7 len maxP)
    (h : NearState) (st : Near.TrieOverlay.State) {bud : Nat}
    (hview : h.context.isView = false) (hacc : h.storageAccounting = some st) (hcanon : Canon st)
    (hlink : StorageLink h st) (hproof : ProofBudget h st bud)
    (hbud : writeProofCost (contractKey h.context.currentAccountId mKey) none +
      removeProofCost (contractKey h.context.currentAccountId mKey) (some mVal) ≤ bud)
    (hlim : withinLimit h.config.maxStorageKeyLen 69 = true)
    (hvlim : withinLimit h.config.maxStorageValueLen 16 = true)
    (hreg : withinLimit h.config.maxRegisterLen 16 = true)
    (hnone : h.storage mKey = none)
    (hU : h.context.storageUsage.toNat + (85 + e) < 2 ^ 64)
    (K2 : Nat) (hK2 : ∀ h1 s2, erase h1 = erase (storageWriteHost e h mKey mVal evictedRegister s2) →
      250 * cfg.regularOpCost + storageUsageUse h1 + cost402 cfg (F + 3) 1 64 h1 mKey mVal ≤ K2) :
    code107 e n maxP inst mi A mx
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f107 Cg
        (pre107 n g ta A gt s out v q idx maxP len live F ob h)
        (fun _ => 100 * cfg.regularOpCost + cost404 cfg F h K2)
        (post107 n g ta A gt s out v q idx maxP len live F e (Post404 e h st bud)) := by
  iintro #Hk
  iunfold code107 at Hk
  icases Hk with ⟨#H404c, #F404⟩
  ihave #S404 := MeasureUsage.f404_spec cfg lim (d + 1) types[0]! rfl inst mi e A n g ta mx hm (by omega) Cg gt
    s out q 1 idx maxP len live F hF (storeBytes (.i64 0) 8) hs hal rfl hout (by omega) hroom
    h st hview hacc hcanon hlink hproof hbud hlim hvlim hreg hnone hU K2 hK2 $$ H404c
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold code404, LookupMapOps.code401, LookupMapInsert.code391, DropVec.dropCode at H404c
    icases H404c with ⟨⟨⟨-, ⟨#H, -⟩, -⟩, -⟩, -⟩; iexact H
  have hn := hm.mem
  have ha404 := hm.funcs 404 (by decide)
  have t0 : types[0]!.params.length = 1 := by rfl
  generalize hK : cost404 cfg F h K2 = K
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold pre107 at HP
  icases HP with ⟨%hargs, HE, Ho, Hv, Hq⟩
  subst hargs
  iunfold env404 at HE
  icases HE with ⟨Hg, Hs, HIR, HU, HW, HR, Hvt, Hinv, Ha, Hz, Hhost⟩
  have ho8 : (out + 8).toNat = out.toNat + 8 := by simp [UInt32.toNat_add]; omega
  have ho16 : (out + 16).toNat = out.toNat + 16 := by simp [UInt32.toNat_add]; omega
  have ho24 : (out + 24).toNat = out.toNat + 24 := by simp [UInt32.toNat_add]; omega
  have ho32 : (out + 32).toNat = out.toNat + 32 := by simp [UInt32.toNat_add]; omega
  have hv8 : (v + 8).toNat = v.toNat + 8 := by simp [UInt32.toNat_add]; omega
  ihave Ho := U128From.memBytes_split n out.toNat 8 ob (by omega) $$ Ho
  icases Ho with ⟨O0, Ho⟩
  ihave Ho := U128From.memBytes_split n (out.toNat + 8) 8 (ob.drop 8) (by simp; omega) $$ Ho
  icases Ho with ⟨O8, Ho⟩
  ihave Ho := U128From.memBytes_split n (out.toNat + 8 + 8) 8 ((ob.drop 8).drop 8) (by simp; omega) $$ Ho
  icases Ho with ⟨O16, Ho⟩
  ihave Ho := U128From.memBytes_split n (out.toNat + 8 + 8 + 8) 8 (((ob.drop 8).drop 8).drop 8) (by simp; omega) $$ Ho
  icases Ho with ⟨O24, O32⟩
  have l0 : (ob.take 8).length = 8 := by simp; omega
  have l8 : ((ob.drop 8).take 8).length = 8 := by simp; omega
  have l16 : (((ob.drop 8).drop 8).take 8).length = 8 := by simp; omega
  have l24 : ((((ob.drop 8).drop 8).drop 8).take 8).length = 8 := by simp; omega
  have l32 : ((((ob.drop 8).drop 8).drop 8).drop 8).length = 4 := by simp; omega
  ihave O8 := memBytes_addr (show out.toNat + 8 = (out + 8).toNat by omega) $$ O8
  ihave O16 := memBytes_addr (show out.toNat + 8 + 8 = (out + 16).toNat by omega) $$ O16
  ihave O24 := memBytes_addr (show out.toNat + 8 + 8 + 8 = out.toNat + 24 by omega) $$ O24
  ihave O32 := memBytes_addr (show out.toNat + 8 + 8 + 8 + 8 = (out + 32).toNat by omega) $$ O32
  ihave Hv := (show (n ↦[wms][ v.toNat ] (bytes32 q ++ (bytes32 1 ++ bytes32 1)) : IProp GF) ⊢
      n ↦[wms][ v.toNat ] (bytes32 q ++ bytes32 1 ++ bytes32 1) by rw [List.append_assoc]) $$ Hv
  ihave Hv := BorshFT.splitB (n := n) (a := v.toNat) (b := v.toNat + 8) (bytes32 q ++ bytes32 1) (bytes32 1)
    (by simp [bytes32]) $$ Hv
  icases Hv with ⟨V0, V8⟩
  ihave V8 := memBytes_addr (show v.toNat + 8 = (v + 8).toNat by omega) $$ V8
  simp only [f107]
  mstep; mstep; mstep [O0] with (first | exact List.ne_nil_of_length_pos (by omega) | (simp [storeWidth, NumType.byteWidth]; omega) | rfl)
  mstep; mstep; mstep [V0] with (first | (simp [bytes32, loadWidth, NumType.byteWidth]) | omega)
  rw [VecFromElem.ofNat_decode_pair]
  mstep [O24] with (first | exact List.ne_nil_of_length_pos (by omega) | (simp [storeWidth, NumType.byteWidth]; omega) | rfl)
  rw [VecFromElem.storeBytes_pair64]
  mstep; mstep; mstep; mstep; mstep [O8] with (first | exact List.ne_nil_of_length_pos (by omega) | (simp [storeWidth, NumType.byteWidth]; omega) | rfl)
  mstep; mstep; mstep; mstep; mstep [O16] with (first | exact List.ne_nil_of_length_pos (by omega) | (simp [storeWidth, NumType.byteWidth]; omega) | rfl)
  mstep; mstep; mstep; mstep; mstep; mstep; mstep [V8] with (first | (simp [bytes32, loadWidth, NumType.byteWidth]) | omega)
  mstep [O32] with (first | exact List.ne_nil_of_length_pos (by omega) | (simp [storeWidth, NumType.byteWidth]; omega) | rfl)
  rw [show (UInt32.ofNat 1 : UInt32) = 1 from rfl]
  ihave O24 := memBytes_addr (show out.toNat + 24 = (out + 24).toNat by omega) $$ O24
  ihave O32 := memBytes_addr (show (out + 32).toNat = (out + 24).toNat + (bytes32 q ++ bytes32 1).length by
    simp [bytes32]; omega) $$ O32
  ihave Hm := BorshFT.joinB (n := n) (a := (out + 24).toNat) (b := (out + 24).toNat + (bytes32 q ++ bytes32 1).length)
    (bytes32 q ++ bytes32 1) (bytes32 1) rfl $$ [O24 O32]
  · iframe O24 O32
  ihave Hm : LookupMapLeaves.prefixAt n (out + 24) q 1 1 $$ [Hm]
  · iunfold LookupMapLeaves.prefixAt; rw [List.append_assoc] at *; iexact Hm
  ihave O16 := memBytes_addr (show (out + 16).toNat = out.toNat + 16 by omega) $$ O16
  mstep
  mcall S404 using [Hg Hs HIR HU HW HR Hvt Hinv O16 Hm Hq Ha Hz Hhost] with (rw [hK]; mstep_norm_full; omega)
  · iunfold pre404
    iframe Hg Hs HIR HU HW HR Hvt Hinv O16 Hm Hq Ha Hz Hhost
    ipureintro; rfl
  iunfold post404 at HQ
  icases HQ with ⟨%hrs, Hg, Hs, HIR, HU, HW, HR, Hvt, Hinv, O16, Hm, Hq, Ha, Hz, Hhost⟩
  subst hrs
  mcredits R
  iframe Hc
  iunfold post107, env404', ftAt
  isplitr
  · ipureintro; simp [htype]
  iframe Hg Hs HIR HU HW HR Hvt Hinv Ha Hz Hhost Hq
  ihave O8 := memBytes_addr (show (out + 8).toNat = out.toNat + 8 by omega) $$ O8
  iunfold LookupMapLeaves.prefixAt at Hm
  ihave Hm := memBytes_addr (show (out + 24).toNat = out.toNat + 24 by omega) $$ Hm
  ihave Hv := BorshFT.joinB (n := n) (a := v.toNat) (b := v.toNat + (bytes32 q ++ bytes32 1).length)
    (bytes32 q ++ bytes32 1) (bytes32 1) rfl $$ [V0 V8]
  · ihave V8 := memBytes_addr (show (v + 8).toNat = v.toNat + (bytes32 q ++ bytes32 1).length by
      simp [bytes32]; omega) $$ V8
    iframe V0 V8
  rw [List.append_assoc] at *
  rw [show storeBytes (Value.i64 0) 8 = List.replicate 8 (0 : UInt8) from rfl]
  iframe O0 O8 O16 Hm Hv

end S107

end WNear.Binary.ContractNew
