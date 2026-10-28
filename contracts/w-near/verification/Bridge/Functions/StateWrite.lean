import Bridge.Functions.StorageWrite
import Bridge.Functions.BorshSer
import Bridge.Functions.DropVec
import Bridge.Functions.StateRead

/-!
# `env::state_write` (function 220)

```wat
;; 220 state_write(contract): sp -= 48
;;     163(sp + 32, contract)                    ;; try_to_vec: Ok(vec) at sp + 32
;;     tag = 1 → panic "Cannot serialize the contract state." (not on our path)
;;     [sp+16..28] := vec; 779(sp + 8, sp + 16)  ;; (ptr, len)
;;     547(1049788, 5, ptr, len)                 ;; storage_write(b"STATE", bytes), its bool dropped
;;     68(sp + 16)                               ;; the Vec freed
;;     sp += 48
```

* `memBytes_disjoint`: two owned nonempty byte ranges of the same memory do not overlap.
* `f220_spec`: `env::state_write(&contract)` on the `FungibleToken` at `c` (`ftAt`): the host as
  `StorageWritePost` of `storage_write(b"STATE", borsh(contract))`, the heap with one more free
  cell.
-/

namespace WNear.Binary.StateWrite

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open WNear.Binary.Interface (IfaceMod iface ifaceCode)
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_word stk_addr)

section Disjoint

variable {GF : BundledGFunctors} [ι : WasmGS NearState GF]

theorem memBytes_cons (n i : Nat) (b : UInt8) (bs : List UInt8) :
    (n ↦[wms][ i ] (b :: bs) : IProp GF) ⊣⊢ (Loc.byte n i ↦ₛ (Cell.byte b : Cell NearState)) ∗ n ↦[wms][ i + 1 ] bs := by
  unfold WasmLogic.memBytes
  simp only [byteCells]
  exact BigSepL.bigSepL_cons

/-- The byte at `a + k` of an owned range. -/
theorem memBytes_at (n a k : Nat) (xs : List UInt8) (hk : k < xs.length) :
    (n ↦[wms][ a ] xs : IProp GF) ⊢ ∃ x : UInt8, (Loc.byte n (a + k) ↦ₛ (Cell.byte x : Cell NearState)) ∗ True := by
  iintro H
  ihave H := U128From.memBytes_split n a k xs (by omega) $$ H
  icases H with ⟨-, H⟩
  cases hd : xs.drop k with
  | nil => simp at hd; omega
  | cons x r =>
    ihave H := (memBytes_cons n (a + k) x r).1 $$ H
    icases H with ⟨H, -⟩
    iexists x
    iframe H

/-- Two owned nonempty byte ranges of memory `n` are disjoint. -/
theorem memBytes_disjoint (n a b : Nat) (xs ys : List UInt8) (hx : xs ≠ []) (hy : ys ≠ []) :
    (n ↦[wms][ a ] xs ∗ n ↦[wms][ b ] ys : IProp GF) ⊢
      ⌜a + xs.length ≤ b ∨ b + ys.length ≤ a⌝ ∗ n ↦[wms][ a ] xs ∗ n ↦[wms][ b ] ys := by
  by_cases hd : a + xs.length ≤ b ∨ b + ys.length ≤ a
  · iintro ⟨H1, H2⟩
    iframe H1 H2
    ipureintro; exact hd
  · have hxl : 0 < xs.length := List.length_pos_of_ne_nil hx
    have hyl : 0 < ys.length := List.length_pos_of_ne_nil hy
    iintro ⟨H1, H2⟩
    iexfalso
    ihave H1 := memBytes_at n a (max a b - a) xs (by omega) $$ H1
    ihave H2 := memBytes_at n b (max a b - b) ys (by omega) $$ H2
    icases H1 with ⟨%x1, C1, -⟩
    icases H2 with ⟨%x2, C2, -⟩
    rw [show a + (max a b - a) = max a b by omega, show b + (max a b - b) = max a b by omega]
    ihave %hne := ghost_map_elem_ne (GF := GF) ι.name (Loc.byte n (max a b)) (Loc.byte n (max a b)) (.own 1)
      (Cell.byte x1 : Cell NearState) (Cell.byte x2) $$ C1 C2
    exact absurd rfl hne

end Disjoint

section Spec

variable {GF : BundledGFunctors} [WasmGS NearState GF]

open WNear.Binary.VecFromElem (roomFor)
open WNear.Binary.VecWithCap (vecCode2 costAllocF okG)
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.AllocInv (heapInv)
open WNear.Binary.FmtSink (grown)
open WNear.Binary.BorshSer (ftAt ser163Code pre163 post163 cost48)
open WNear.Binary.StorageWrite (wslot wCode pre547 post547 evictedRegister)
open WNear.Binary.DropVec (dropCode pre747 post747)
open WNear.Binary.StateRead (stateKey)

theorem stkJ {n a b k1 k2 : Nat} (h : b = a + k1) :
    stk (GF := GF) n a k1 ∗ stk n b k2 ⊢ stk n a (k1 + k2) := by
  subst h; exact stk_join n a k1 k2

theorem stkL {n a a' k k' : Nat} (ha : a = a') (hk : k = k') : stk (GF := GF) n a k ⊢ stk n a' k' := by
  subst ha hk; exact .rfl

/-- The Borsh bytes of a `FungibleToken`: the prefix `Vec`, `total_supply`, `account_storage_usage`. -/
def stateBytes (L : UInt32) (pre b0 b1 c0 : List UInt8) : List UInt8 := bytes32 L ++ pre ++ (b0 ++ b1) ++ c0

/-- The code `state_write` runs (persistent). -/
def swCode (e n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (mx : Option Nat) : IProp GF :=
  iprop(ser163Code n maxP inst mi A ∗ dropCode inst mi A ∗ ifaceCode e inst mi A n mx ∗ wCode e inst A ∗
    A 428 ↪[wf] FuncInst.wasm types[54]! inst f428 ∗ A 547 ↪[wf] FuncInst.wasm types[33]! inst f547 ∗
    A 163 ↪[wf] FuncInst.wasm types[14]! inst f163 ∗ A 68 ↪[wf] FuncInst.wasm types[0]! inst f68)

instance (e n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (mx : Option Nat) :
    Persistent (swCode (GF := GF) e n maxP inst mi A mx) := by
  unfold swCode; infer_instance

def pre220 (n g ta : Nat) (A : Nat → Nat) (gt : GlobalType) (s c p L : UInt32) (idx : UInt32) (maxP len : Nat)
    (live : List (Nat × Nat)) (F : Nat) (b0 b1 c0 pre : List UInt8) (h : NearState) (args : List Value) :
    IProp GF :=
  iprop(⌜args = [.i32 c]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 144) 144 ∗ iface n ta A ∗ wslot n ta A ∗
    vt n 1057464 idx ta (A 578) ∗ heapInv n maxP len live F ∗ ftAt n c b0 b1 c0 p L ∗
    n ↦[wms][ p.toNat ] pre ∗ n ↦[wms][ 1049788 ] stateKey ∗ mhostPt h)

def post220 (n g ta : Nat) (A : Nat → Nat) (gt : GlobalType) (s c p L : UInt32) (idx : UInt32) (maxP len : Nat)
    (live : List (Nat × Nat)) (F : Nat) (b0 b1 c0 pre : List UInt8) (Q : NearState → Prop)
    (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 144) 144 ∗ iface n ta A ∗ wslot n ta A ∗
    vt n 1057464 idx ta (A 578) ∗ (∃ len', ⌜len' = len ∨ len' = VecFromElem.grownLen len 1024⌝ ∗
      heapInv n maxP len' live (F + 1)) ∗ ftAt n c b0 b1 c0 p L ∗
    n ↦[wms][ p.toNat ] pre ∗ n ↦[wms][ 1049788 ] stateKey ∗ (∃ h', ⌜Q h'⌝ ∗ mhostPt h'))

open Near.TrieAccounting Near.TrieConstruction Near.TrieOverlay in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **`env::state_write(&contract)`** (220) on the `FungibleToken` at `c`: its Borsh bytes
(`stateBytes`) written under `STATE` (`storage_write`, `StorageWritePost`), the buffer freed. -/
theorem f220_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (e : Nat) (A : Nat → Nat) (n g ta : Nat)
    (mx : Option Nat) (hm : IfaceMod mi A n g ta) (hd : d + 14 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s c p L : UInt32) (idx : UInt32) (maxP len : Nat) (live : List (Nat × Nat))
    (F : Nat) (hF : okG F) (b0 b1 c0 pre : List UInt8) (hs : 144 ≤ s.toNat) (hal : s.toNat % 8 = 0)
    (hb0 : b0.length = 8) (hb1 : b1.length = 8) (hc0 : c0.length = 8)
    (hpre : pre.length = L.toNat) (hL : L.toNat + 28 ≤ 1024)
    (hc : c.toNat + 36 ≤ 2 ^ 32) (hp : p.toNat + L.toNat ≤ 2 ^ 32) (hr : roomFor len maxP 1024)
    (h : NearState) (st : Near.TrieOverlay.State) {b : Nat}
    (hview : h.context.isView = false) (hacc : h.storageAccounting = some st)
    (hlim : withinLimit h.config.maxStorageKeyLen 5 = true)
    (hvlim : withinLimit h.config.maxStorageValueLen (L.toNat + 28) = true)
    (hb : build st.entries = .ok st.base) (hz : zeroHash ∉ st.base.witness.map Prod.fst)
    (hlink : h.storage stateKey = viewVal st (contractKey h.context.currentAccountId stateKey))
    (hproof : ProofBudget h st b)
    (hbud : writeProofCost (contractKey h.context.currentAccountId stateKey) (h.storage stateKey) ≤ b)
    (hreg : ∀ v, h.storage stateKey = some v → withinLimit h.config.maxRegisterLen v.length = true) :
    swCode e n maxP inst mi A mx
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f220 Cg
        (pre220 n g ta A gt s c p L idx maxP len live F b0 b1 c0 pre h)
        (fun _ => 100 * cfg.regularOpCost +
          (70 * cfg.regularOpCost + (35 * cfg.regularOpCost + (203 * cfg.regularOpCost + costAllocF cfg F 1024)) +
            (30 * cfg.regularOpCost + (800 * cfg.regularOpCost + cost48 cfg L))) +
          (51 * cfg.regularOpCost + (257 * cfg.regularOpCost +
            storageWriteUse h stateKey 5 (L.toNat + 28))) + 315 * cfg.regularOpCost)
        (post220 n g ta A gt s c p L idx maxP len live F b0 b1 c0 pre
          (StorageWritePost e h stateKey (stateBytes L pre b0 b1 c0) evictedRegister st)) := by
  iintro #Hk
  iunfold swCode at Hk
  icases Hk with ⟨#H163c, #Hdrop, #Hcode, #Hw, #F428, #F547, #F163, #F68⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold dropCode at Hdrop; icases Hdrop with ⟨#H, -⟩; iexact H
  ihave #H779 : A 779 ↪[wf] FuncInst.wasm types[14]! inst f779 $$ []
  · iunfold BorshSer.ser163Code, BorshSer.ser164Code, BorshSer.ftSerCode, BorshSer.serCode at H163c
    icases H163c with ⟨⟨⟨⟨-, #H⟩, -⟩, -⟩, -⟩; iexact H
  have hn := hm.mem
  have hg := hm.glob
  have ha163 := hm.funcs 163 (by decide)
  have ha547 := hm.funcs 547 (by decide)
  have ha779 := hm.funcs 779 (by decide)
  have ha68 := hm.funcs 68 (by decide)
  have t14 : types[14]!.params.length = 2 := by rfl
  have t33 : types[33]!.params.length = 4 := by rfl
  have t0 : types[0]!.params.length = 1 := by rfl
  have hlt := s.toNat_lt
  have hLlt := L.toNat_lt
  have h48 : (s - 48).toNat = s.toNat - 48 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have e32 : (s - 48 + 32).toNat = s.toNat - 16 := by simp [UInt32.toNat_add, h48]; omega
  have e16 : (s - 48 + 16).toNat = s.toNat - 32 := by simp [UInt32.toNat_add, h48]; omega
  have e8 : (s - 48 + 8).toNat = s.toNat - 40 := by simp [UInt32.toNat_add, h48]; omega
  have e24 : (s - 48 + 24).toNat = s.toNat - 24 := by simp [UInt32.toNat_add, h48]; omega
  have e44 : (s - 48 + 44).toNat = s.toNat - 4 := by simp [UInt32.toNat_add, h48]; omega
  have hvl : (0 + 4 + L + 16 + 8 : UInt32).toNat = L.toNat + 28 := by simp [UInt32.toNat_add]; omega
  generalize hK163 : 70 * cfg.regularOpCost + (35 * cfg.regularOpCost + (203 * cfg.regularOpCost +
    costAllocF cfg F 1024)) + (30 * cfg.regularOpCost + (800 * cfg.regularOpCost + cost48 cfg L)) = K163
  generalize hKw : storageWriteUse h stateKey 5 (L.toNat + 28) = Kw
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold pre220 at HP
  icases HP with ⟨%hargs, Hg, Hs, HI, HW, Hvt, Hinv, Hft, Hp, Hkey, Hhost⟩
  subst hargs
  icases stk_split n (s.toNat - 144) 96 48 $$ Hs with ⟨Lo, Fr⟩
  rw [show s.toNat - 144 + 96 = s.toNat - 48 by omega]
  icases stk_split n (s.toNat - 48) 8 40 $$ Fr with ⟨F0, Fr⟩
  icases stk_split n (s.toNat - 48 + 8) 8 32 $$ Fr with ⟨D, Fr⟩
  icases stk_split n (s.toNat - 48 + 8 + 8) 12 20 $$ Fr with ⟨V, Fr⟩
  icases stk_split n (s.toNat - 48 + 8 + 8 + 12) 4 16 $$ Fr with ⟨U, O⟩
  rw [show s.toNat - 48 + 8 = s.toNat - 40 by omega, show s.toNat - 40 + 8 = s.toNat - 32 by omega,
    show s.toNat - 32 + 12 = s.toNat - 20 by omega, show s.toNat - 20 + 4 = s.toNat - 16 by omega]
  iunfold stk at O
  icases O with ⟨%ob, %hob, O⟩
  simp only [f220]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep; mstep; mstep
  mcall (BorshSer.f163_spec cfg lim (d + 1) types[14]! (by rfl) inst mi A n g ta hm (by omega) Cg gt (s - 48)
      (s - 48 + 32) c p L idx maxP len live F hF b0 b1 c0 pre ob (by omega) (by omega) hb0 hb1 hc0 hpre hL hob
      (by omega) hc hp hr) using [Hg Lo Hvt Hinv Hft Hp O] with (rw [hK163]; mstep_norm_full; omega)
  · iunfold pre163
    ihave Lo := stk_addr (show s.toNat - 144 = (s - 48).toNat - 96 by omega) $$ Lo
    ihave O := memBytes_addr (show s.toNat - 16 = (s - 48 + 32).toNat by omega) $$ O
    iframe Hg Lo Hvt Hinv Hft Hp O
    ipureintro; rfl
  rw [hK163]
  iunfold post163 at HQ
  icases HQ with ⟨%hrs, Hg, Lo, Hvt, Hft, Hp, %q, %rest, %⟨hq0, hqb, hrest⟩, Hgr, O0, O4, O12, Wo, Rest⟩
  subst hrs
  have hq4 : q.toNat + 1024 < 2 ^ 32 := hqb
  ihave O0 := memBytes_addr (show (s - 48 + 32).toNat = (s - 48).toNat + 32 by omega) $$ O0
  ihave O4 := memBytes_addr (show (s - 48 + 32).toNat + 4 = (s - 48).toNat + 36 by omega) $$ O4
  ihave O12 := memBytes_addr (show (s - 48 + 32).toNat + 12 = (s - 48 + 44).toNat by simp [UInt32.toNat_add, h48]; omega) $$ O12
  iunfold stk at V
  icases V with ⟨%vb, %hvb, V⟩
  ihave V := U128From.memBytes_split n (s.toNat - 32) 8 vb (by omega) $$ V
  icases V with ⟨V0, V8⟩
  have hv0 : (vb.take 8).length = 8 := by simp; omega
  have hv8 : (vb.drop 8).length = 4 := by simp; omega
  ihave V0 := memBytes_addr (show s.toNat - 32 = (s - 48).toNat + 16 by omega) $$ V0
  ihave V8 := memBytes_addr (show s.toNat - 32 + 8 = (s - 48 + 24).toNat by omega) $$ V8
  mstep; mstep; mstep [O0]; mstep; mstep; mstep
  mstep; mstep; mstep; mstep; mstep; mstep; mstep [O12]; mstep [V8]
  mstep; mstep; mstep [O4]; mstep [V0]
  rw [BorshLeaves.storeBytes_i64_decode _ (by simp [bytes32])]
  iunfold stk at D
  icases D with ⟨%db, %hdb, D⟩
  ihave D := memBytes_addr (show s.toNat - 40 = (s - 48 + 8).toNat by omega) $$ D
  ihave V0 := memBytes_addr (show (s - 48).toNat + 16 = (s - 48 + 16).toNat by omega) $$ V0
  ihave V8 := memBytes_addr (show (s - 48 + 24).toNat = (s - 48 + 16).toNat + 8 by omega) $$ V8
  ihave VV := BorshFT.joinB (n := n) (a := (s - 48 + 16).toNat) (b := (s - 48 + 16).toNat + 8)
    (bytes32 q ++ bytes32 1024) (bytes32 (0 + 4 + L + 16 + 8)) (by simp [bytes32]) $$ [V0 V8]
  · iframe V0 V8
  mstep; mstep; mstep; mstep; mstep; mstep
  mcall (VecDeref.f779_spec cfg lim (d + 1) types[14]! rfl inst mi n hn Cg (s - 48 + 8) (s - 48 + 16) db
      (bytes32 q ++ bytes32 1024 ++ bytes32 (0 + 4 + L + 16 + 8)) hdb (by simp [bytes32])) using [D VV]
  · iunfold VecDeref.pre
    iframe D VV
    ipureintro; rfl
  iunfold VecDeref.post at HQ
  icases HQ with ⟨%hrs, D, VV⟩
  subst hrs
  have hpl : (bytes32 q ++ (bytes32 1024 ++ bytes32 (0 + 4 + L + 16 + 8))).take 4 ++
      (bytes32 q ++ (bytes32 1024 ++ bytes32 (0 + 4 + L + 16 + 8))).drop 8 =
      bytes32 q ++ bytes32 (0 + 4 + L + 16 + 8) := by
    have l4 : ∀ x : UInt32, (bytes32 x).length = 4 := fun x => by simp [bytes32]
    rw [List.take_left' (l4 q), ← List.append_assoc, List.drop_left' (by simp [l4])]
  rw [hpl]
  ihave D := KeyGet.split64 n (s - 48 + 8).toNat q (0 + 4 + L + 16 + 8) $$ D
  icases D with ⟨D0, D4⟩
  ihave D0 := memBytes_addr (show (s - 48 + 8).toNat = (s - 48).toNat + 8 by omega) $$ D0
  ihave D4 := memBytes_addr (show (s - 48 + 8).toNat + 4 = (s - 48).toNat + 12 by omega) $$ D4
  mstep; mstep; mstep; mstep [D0]; mstep; mstep [D4]
  have hsl : (stateBytes L pre b0 b1 c0).length = L.toNat + 28 := by
    simp [stateBytes, bytes32, hpre, hb0, hb1, hc0]; omega
  have hk5 : stateKey.length = 5 := by rw [← StateRead.stateKey_eq]; rfl
  have hkl5 : stateKey.length = (5 : UInt32).toNat := by rw [hk5]; rfl
  ihave Wo := (show (n ↦[wms][ q.toNat ] (bytes32 L ++ (pre ++ (b0 ++ (b1 ++ c0)))) : IProp GF) ⊢
    n ↦[wms][ q.toNat ] stateBytes L pre b0 b1 c0 by simp only [stateBytes, List.append_assoc]; exact .rfl) $$ Wo
  icases memBytes_disjoint n 1049788 q.toNat stateKey (stateBytes L pre b0 b1 c0) (by intro h0; have := congrArg List.length h0; rw [hk5] at this; simp at this)
    (by intro h0; have := congrArg List.length h0; rw [hsl] at this; simp at this) $$ [Hkey Wo]
    with ⟨%hdj, Hkey, Wo⟩
  · iframe Hkey Wo
  ihave #H3 : (ifaceCode (GF := GF) e inst mi A n mx ∗ wCode e inst A ∗
      A 428 ↪[wf] FuncInst.wasm types[54]! inst f428) $$ []
  · iframe Hcode Hw F428
  ihave #S547 := StorageWrite.f547_spec_host (GF := GF) cfg lim (d + 1) types[33]! (by rfl) inst mi e A n g ta mx hm
    (by omega) Cg gt (s - 48) 1049788 5 q (0 + 4 + L + 16 + 8) (by omega) (by omega) stateKey
    (stateBytes L pre b0 b1 c0) h st hkl5 (by decide) (by rw [hsl, hvl]) (by rw [hvl]; omega) hdj hview hacc
    (by rw [hk5]; exact hlim) (by rw [hsl]; exact hvlim) hb hz hlink hproof hbud hreg $$ H3
  icases stk_split n ((s - 48).toNat - 96) 64 32 $$ Lo with ⟨Lo, Lo32⟩
  ihave Lo32 := stk_addr (show (s - 48).toNat - 96 + 64 = (s - 48).toNat - 32 by omega) $$ Lo32
  mcall S547 using [Hg HI HW Lo32 Hkey Wo Hhost]
    with (simp only [hvl, show (5 : UInt32).toNat = 5 from rfl, hKw]; mstep_norm_full; omega)
  · iunfold pre547
    simp only [UInt32.reduceToNat]
    iframe Hg HI HW Lo32 Hkey Wo Hhost
  simp only [hvl, show (5 : UInt32).toNat = 5 from rfl, hKw]
  iunfold post547 at HQ
  icases HQ with ⟨%hrs, Hg, HI, HW, Lo32, Hkey, Wo, ⟨%h', %hq, Hhost⟩⟩
  subst hrs
  -- the result dropped; the `Vec` freed
  iunfold grown at Hgr
  icases Hgr with ⟨%hl', %hhl, Hinv⟩
  ihave VV := BorshFT.splitB (n := n) (a := (s - 48 + 16).toNat) (b := (s - 48 + 16).toNat + 4) (bytes32 q)
    (bytes32 1024 ++ bytes32 (0 + 4 + L + 16 + 8)) (by simp [bytes32]) $$ VV
  icases VV with ⟨P0, VV⟩
  ihave VV := KeyGet.split64 n ((s - 48 + 16).toNat + 4) 1024 (0 + 4 + L + 16 + 8) $$ VV
  icases VV with ⟨P4, P8⟩
  ihave Blk : AllocInv.block n q.toNat 1024 $$ [Wo Rest]
  · iunfold AllocInv.block
    ihave B := BorshFT.joinB (n := n) (a := q.toNat) (b := q.toNat + (4 + L.toNat + 24)) _ rest
      (by rw [hsl]; omega) $$ [Wo Rest]
    · iframe Wo Rest
    iexists _
    iframe B
    ipureintro; simp [hsl, hrest]; omega
  mstep; mstep; mstep; mstep
  mcall (DropVec.f68_spec cfg lim (d + 1) types[0]! rfl inst mi A n g ta hm (by omega) Cg maxP hl'
      ((q.toNat, UInt32.toNat 1024) :: live) F (s - 48 + 16) q 1024 (0 + 4 + L + 16 + 8) (by decide) (by omega))
      using [P0 P4 P8 Hinv Blk]
  · iunfold pre747
    ihave P4 := memBytes_addr (show (s - 48 + 16).toNat + 4 = (s - 48 + 16).toNat + 4 by rfl) $$ P4
    ihave P8 := memBytes_addr (show (s - 48 + 16).toNat + 4 + 4 = (s - 48 + 16).toNat + 8 by omega) $$ P8
    simp only [UInt32.reduceToNat]
    iframe P0 P4 P8 Hinv Blk
    ipureintro; exact List.mem_cons_self
  iunfold post747 at HQ
  icases HQ with ⟨%hrs, P0, P4, P8, Hinv⟩
  subst hrs
  mstep; mstep; mstep; mstep [Hg]
  rw [show s - 48 + 48 = s by simp]
  mcredits R
  iframe Hc
  iunfold post220
  isplitr
  · ipureintro; simp [htype]
  iframe Hg HI HW Hvt Hft Hp Hkey
  isplitl [F0 U O0 O12 O4 D0 D4 Lo Lo32 P0 P4 P8]
  · ihave D0 := stk_word n _ _ $$ D0
    ihave D4 := stk_word n _ _ $$ D4
    ihave P0 := stk_word n _ _ $$ P0
    ihave P4 := stk_word n _ _ $$ P4
    ihave P8 := stk_word n _ _ $$ P8
    ihave O0 := stk_word n _ _ $$ O0
    ihave O12 := stk_word n _ _ $$ O12
    ihave O4 := VecFromElem.stk_intro n _ _ $$ O4
    ihave X := stkJ (n := n) (show (s - 48).toNat - 32 = (s - 48).toNat - 96 + 64 by omega) $$ [Lo Lo32]
    · iframe Lo Lo32
    ihave X := stkJ (n := n) (show s.toNat - 48 = (s - 48).toNat - 96 + (64 + 32) by omega) $$ [X F0]
    · iframe X F0
    ihave X := stkJ (n := n) (show (s - 48).toNat + 8 = (s - 48).toNat - 96 + (64 + 32 + 8) by omega) $$ [X D0]
    · iframe X D0
    ihave X := stkJ (n := n) (show (s - 48).toNat + 12 = (s - 48).toNat - 96 + (64 + 32 + 8 + 4) by omega) $$ [X D4]
    · iframe X D4
    ihave X := stkJ (n := n) (show (s - 48 + 16).toNat = (s - 48).toNat - 96 + (64 + 32 + 8 + 4 + 4) by omega) $$ [X P0]
    · iframe X P0
    ihave X := stkJ (n := n) (show (s - 48 + 16).toNat + 4 = (s - 48).toNat - 96 + (64 + 32 + 8 + 4 + 4 + 4) by omega) $$ [X P4]
    · iframe X P4
    ihave X := stkJ (n := n) (show (s - 48 + 16).toNat + 8 = (s - 48).toNat - 96 + (64 + 32 + 8 + 4 + 4 + 4 + 4) by omega) $$ [X P8]
    · iframe X P8
    ihave X := stkJ (n := n) (show s.toNat - 20 = (s - 48).toNat - 96 + (64 + 32 + 8 + 4 + 4 + 4 + 4 + 4) by omega) $$ [X U]
    · iframe X U
    ihave X := stkJ (n := n) (show (s - 48).toNat + 32 = (s - 48).toNat - 96 + (64 + 32 + 8 + 4 + 4 + 4 + 4 + 4 + 4) by omega) $$ [X O0]
    · iframe X O0
    ihave X := stkJ (n := n) (show (s - 48).toNat + 36 = (s - 48).toNat - 96 + (64 + 32 + 8 + 4 + 4 + 4 + 4 + 4 + 4 + 4) by omega) $$ [X O4]
    · iframe X O4
    ihave X := stkJ (n := n) (show (s - 48 + 44).toNat = (s - 48).toNat - 96 + (64 + 32 + 8 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + (bytes32 q ++ bytes32 1024).length) by simp [bytes32]; omega) $$ [X O12]
    · iframe X O12
    iapply stkL (n := n) (k := 64 + 32 + 8 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + (bytes32 q ++ bytes32 1024).length + 4)
      (k' := 144) (show (s - 48).toNat - 96 = s.toNat - 144 by omega) (by first | rfl | simp [bytes32])
    iexact X
  isplitl [Hinv]
  · iexists hl'
    simp only [List.erase_cons_head] at *
    iframe Hinv
    ipureintro; exact hhl
  iexists h'
  iframe Hhost
  ipureintro; exact hq

end Spec

end WNear.Binary.StateWrite
