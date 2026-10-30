import Bridge.Functions.DepositCosts
import Bridge.Functions.PredecessorId
import Bridge.Functions.LookupMapContains
import Bridge.Functions.EnvGetters

/-!
# `near_deposit` (232): the body (M8)

```wat
;; 232 near_deposit(self): sp = s - 144
529(sp + 24)                                  attached_deposit: (l3, l2) = (lo, hi), also at sp + 40
block @1 block @2
  (l3 | l2) == 0 → br @2                      → begin_panic("Requires positive attached deposit")  664
  526(sp + 56)                                predecessor_account_id: the String at sp + 56
  block @3 block @4
    394(self + 24, sp + 56) → br @4           contains_key: registered → the call of 406
    418(sp + 72, self); amount < min → br @1  → begin_panic("ERR_DEPOSIT_TOO_SMALL")          664
    409(self, sp + 56)                        internal_register_account
    418(sp + 72, self); (l3, l2) := amount - min (no borrow: br @3 → 853 not taken)
  end @4
  seg406 ++ tail232                           DepositSegAll.seg406_all
```

* `code232`, `stat232`: the code and the statics the body uses.
* `DCase`, `dcase`: the outcome, from the deposit, the balance when registered, the minimum and
  the supply (`requires positive`, `too small`, `balance overflow`, `supply overflow`, `ok`);
  `DCase.text`: the panic's text.
* `body232_reg`: the account registered.
-/

namespace WNear.Binary.DepositBody

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.Interface (IfaceMod iface ifaceCode)
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_word stk_addr roomFor)
open WNear.Binary.BorshFT (splitB joinB stkJ stkSp stkA join64' split64' stkW stkB)
open WNear.Binary.BorshInt (stk_bytes')
open WNear.Binary.VecWithCap (okG)
open WNear.Binary.ReadRegister (ifaceR RegOk)
open WNear.Binary.StorageWrite (wslot evictedRegister)
open WNear.Binary.LookupMapLeaves (prefixAt)
open WNear.Binary.LookupMapOps (HeapRoomK LenIn)
open WNear.Binary.InternalDeposit (code406 code409 Post406 zeroAt)
open WNear.Binary.DepositTail (tailCode tailStat tail232 logText)
open WNear.Binary.U128From (u128Bytes)
open WNear.Binary.PanicStr (panicCode panicSlot panicked)
open WNear.Binary.DepositPanicSpec (MFunSpecT_persistent hookRes pPre PanicSpecD)
open WNear.Binary.DepositSeg (seg406 LenUp)
open WNear.Binary.DepositSegAll (codeSeg costSegAll seg406_all)
open WNear.Binary.InternalDepositOverflow (balMsg textSupply)
open WNear.Binary.NewBody (keep keep_of_erase keep_acc)
open WNear.Binary.EnvGetters (dslot dCode depLo depHi)
open WNear.Binary.EnvPredecessor (pslot)
open WNear.Binary.StorageHasKey (hslot)
open WNear.Binary.PredecessorId (code526 strAt cost526)
open WNear.Binary.LookupMapContains (code394 cost394)
open WNear.Binary.FromUtf8Gen (utf8Width)

/-! ## The outcome -/

/-- The outcome of `near_deposit`. -/
inductive DCase
  | pos | small | bal | sup | ok
  deriving DecidableEq

/-- The text each panic passes to `panic_utf8`. -/
def DCase.text : DCase → List UInt8
  | .pos => NearDepositPanics.textPositive
  | .small => NearDepositPanics.textTooSmall
  | .bal => balMsg
  | .sup => textSupply
  | .ok => []

/-- The amount deposited: all of it to a registered account, less the minimum to a new one. -/
def amountOf (dep : Nat) (reg : Option Nat) (min : Nat) : Nat :=
  match reg with
  | some _ => dep
  | none => dep - min

/-- The outcome, from the deposit `dep`, the balance `reg` when registered, the minimum `min` and
the supply `T`, in the binary's order. -/
def dcase (dep : Nat) (reg : Option Nat) (min T : Nat) : DCase :=
  if dep = 0 then .pos
  else if reg = none ∧ dep < min then .small
  else if 2 ^ 128 ≤ reg.getD 0 + amountOf dep reg min then .bal
  else if 2 ^ 128 ≤ T + amountOf dep reg min then .sup
  else .ok

theorem dcase_reg_text (dep B m T : Nat) (hd : dep ≠ 0) (hno : ¬ (B + dep < 2 ^ 128 ∧ T + dep < 2 ^ 128)) :
    (dcase dep (some B) m T).text = if B + dep < 2 ^ 128 then textSupply else balMsg := by
  unfold dcase amountOf
  rw [if_neg hd, if_neg (by simp), Option.getD_some]
  by_cases h1 : B + dep < 2 ^ 128
  · have h2 : ¬ (T + dep < 2 ^ 128) := fun h2 => hno ⟨h1, h2⟩
    rw [if_neg (Nat.not_le.mpr h1), if_pos (Nat.le_of_not_lt h2), if_pos h1]; rfl
  · rw [if_pos (Nat.le_of_not_lt h1), if_neg h1]; rfl

theorem dcase_reg_ok (dep B m T : Nat) (hd : dep ≠ 0) (h1 : B + dep < 2 ^ 128) (h2 : T + dep < 2 ^ 128) :
    dcase dep (some B) m T = .ok := by
  unfold dcase amountOf
  rw [if_neg hd, if_neg (by simp), Option.getD_some, if_neg (Nat.not_le.mpr h1), if_neg (Nat.not_le.mpr h2)]

theorem dcase_reg_nok (dep B m T : Nat) (hd : dep ≠ 0) (hno : ¬ (B + dep < 2 ^ 128 ∧ T + dep < 2 ^ 128)) :
    dcase dep (some B) m T ≠ .ok := by
  intro hc
  have := dcase_reg_text dep B m T hd hno
  rw [hc] at this
  by_cases h1 : B + dep < 2 ^ 128
  · rw [if_pos h1] at this; exact absurd this (by decide +kernel)
  · rw [if_neg h1] at this; exact absurd this (by decide +kernel)

/-- The deposit's words. -/
abbrev depOf (h : NearState) : Nat := (depLo h).toNat + 2 ^ 64 * (depHi h).toNat

/-! ## The resources -/

section Res

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The code of 232 (persistent). -/
def code232 (e n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (mx : Option Nat) : IProp GF :=
  iprop(codeSeg e n maxP inst mi A mx ∗ dCode e inst A ∗ A 444 ↪[wf] FuncInst.wasm types[14]! inst f444 ∗
    A 529 ↪[wf] FuncInst.wasm types[0]! inst f529 ∗ code526 e inst mi A n maxP mx ∗
    A 526 ↪[wf] FuncInst.wasm types[0]! inst f526 ∗ code394 e n maxP inst mi A mx ∗
    A 394 ↪[wf] FuncInst.wasm types[13]! inst f394 ∗ A 418 ↪[wf] FuncInst.wasm types[14]! inst f418 ∗
    A 553 ↪[wf] FuncInst.wasm types[0]! inst f553 ∗ A 954 ↪[wf] FuncInst.wasm types[8]! inst f954 ∗
    A 566 ↪[wf] FuncInst.wasm types[4]! inst f566 ∗ code409 e n maxP inst mi A mx ∗
    A 409 ↪[wf] FuncInst.wasm types[14]! inst f409 ∗ A 664 ↪[wf] FuncInst.wasm types[31]! inst f664)

instance (e n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (mx : Option Nat) :
    Persistent (code232 (GF := GF) e n maxP inst mi A mx) := by
  unfold code232; infer_instance

/-- The statics 232 uses: the interface and its slots, the hook, `Dp`, the messages, the zero
`u128`, the tail's statics, the UTF-8 width table, the allocator's vtable. -/
def stat232 (n ta : Nat) (A : Nat → Nat) (lpc : UInt32) (Dp : IProp GF) (aidx : UInt32) : IProp GF :=
  iprop(iface n ta A ∗ Interface.slot n ta 12 38 (A 240) ∗ dslot n ta A ∗ pslot n ta A ∗ hslot n ta A ∗
    wslot n ta A ∗ LogStr.lslot n ta A ∗ panicSlot n ta A ∗ hookRes n ta A lpc ∗ Dp ∗
    n ↦[wms][ 1053000 ] balMsg ∗ zeroAt n ∗ tailStat n ta A ∗ n ↦[wms][ 1071704 ] utf8Width ∗
    vt n 1057464 aidx ta (A 578))

/-- The token at `self`: `total_supply` `(t0, t1)`, `account_storage_usage` `xb`, the accounts
map's prefix `Vec` and its bytes. -/
def selfCells (n : Nat) (self : UInt32) (tb xb : List UInt8) (pp pc pl : UInt32) (pre : List UInt8) : IProp GF :=
  iprop(n ↦[wms][ self.toNat ] tb ∗ n ↦[wms][ self.toNat + 16 ] xb ∗ prefixAt n (self + 24) pp pc pl ∗
    n ↦[wms][ pp.toNat ] pre)

end Res

/-! ## The hosts -/

open Near.TrieOverlay in
/-- What 232 leaves of the host on a registered account: `contains_key` (`h2`), 406 (`h3`), the
log. -/
def PostReg (e : Nat) (h : NearState) (key nv : List UInt8) (st : Near.TrieOverlay.State) (bud : Nat)
    (text : List UInt8) (h' : NearState) : Prop :=
  ∃ (h2 : NearState) (s2 : Near.TrieOverlay.State) (h3 : NearState),
    StorageHasKeyPost (predecessorHost h 0) key st h2 ∧ h2.storageAccounting = some s2 ∧ Canon s2 ∧
    StorageLink h2 s2 ∧ ProofBudget h2 s2 (bud - lookupProofBound (contractKey h.context.currentAccountId key)) ∧
    erase h2 = erase { predecessorHost h 0 with storageAccounting := some s2 } ∧
    Post406 e h2 key nv s2 (bud - lookupProofBound (contractKey h.context.currentAccountId key)) h3 ∧
    h' = LogStr.logged h3 text

theorem keep_predecessorHost (h : NearState) : keep (predecessorHost h 0) = keep h := by
  simp [predecessorHost, u64Max, NearState.setRegister, keep]

/-! ## The registered account -/

/-- The cost of 232 on a registered account, activation excluded, the function's exit included. -/
noncomputable def costReg (cfg : WasmConfig) (F : Nat) (pl : UInt32) (h : NearState) (key : List UInt8)
    (x0 x1 t0 t1 : UInt64) (ab : List UInt8) (K879 : Nat → NewBody.Keep → Nat) : Nat :=
  700 * cfg.regularOpCost + attachedDepositUse h + cost526 cfg F h +
    cost394 cfg F pl (UInt32.ofNat ab.length) (predecessorHost h 0) key +
    costSegAll cfg (F + 2) pl (UInt32.ofNat ab.length) h key x0 x1 t0 t1 (depLo h) (depHi h) ab K879

section Body

variable {GF : BundledGFunctors} [WasmGS NearState GF]

theorem stkJ2 {n a1 a2 k1 k2 : Nat} (a : Nat) (h1 : a1 = a) (h2 : a2 = a + k1) :
    stk (GF := GF) n a1 k1 ⊢ stk n a2 k2 -∗ stk n a (k1 + k2) := by
  rw [h1, h2]; iintro H1 H2; iapply stk_join n a k1 k2; iframe H1 H2

theorem stkA2 {n a b k k' : Nat} (h : a = b) (hk : k = k') : stk (GF := GF) n a k ⊢ stk n b k' := by
  subst h hk; exact .rfl

theorem mwpi_code_eq {cfg : WasmConfig} {lim : ExecLimits} {d : Nat} {f : Frame} {vs : List Value}
    {Φ : Post NearState GF} {code code' : List Instr} (h : code = code') :
    mwpi cfg lim d f vs code' Φ ⊢ mwpi cfg lim d f vs code Φ := by
  subst h; exact .rfl

theorem panicked_conv {Cg : Nat} {hX : NearState} {bs bs' : List UInt8} (h : bs = bs') :
    panicked (GF := GF) Cg hX bs ⊢ panicked Cg hX bs' := by
  subst h; exact .rfl

theorem stk_u64 (n a : Nat) (x : UInt64) : n ↦[wms][ a ] storeBytes (.i64 x) 8 ⊢ stk (GF := GF) n a 8 :=
  stkB _ rfl (by simp [storeBytes])

open Near.TrieAccounting Near.TrieConstruction Near.TrieOverlay in
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 64000000 in
/-- **232 on a registered account**: the deposit, the predecessor, `contains_key` true, then
`seg406_all` on the balance `B = x0 + 2^64 x1`. -/
theorem body232_reg (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (e inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (mx : Option Nat) (hm : IfaceMod mi A n g ta) (D : Nat)
    (hd : d + 27 + D < lim.maxCallDepth)
    (Cg R : Nat) (gt : GlobalType) (s self : UInt32) (SP : Nat) (hSP : 400 ≤ SP)
    (hs : 144 + 80 + SP ≤ s.toNat) (hs2 : s.toNat ≤ 2 ^ 32 - 16) (hal : s.toNat % 8 = 0)
    (hthis : self.toNat + 40 ≤ 2 ^ 32) (pp pc pl : UInt32) (pre : List UInt8)
    (hpre : pre.length = pl.toNat) (hpl : pl.toNat ≤ 4) (hl0 : 0 < pl.toNat) (hpp : pp.toNat + pl.toNat ≤ 2 ^ 32)
    (t0 t1 x0 x1 : UInt64) (xb : List UInt8) (aidx : UInt32)
    (maxP hl : Nat) (live : List (Nat × Nat)) (F : Nat) (hF : okG F) (hroom : HeapRoomK 18 hl maxP)
    (h : NearState) (st : Near.TrieOverlay.State) {bud : Nat}
    (hview : h.context.isView = false) (hacc : h.storageAccounting = some st) (hcanon : Canon st)
    (hlink : StorageLink h st) (hproof : ProofBudget h st bud)
    (hvalid : h.config.validAccountId h.context.predecessorAccountId = true)
    (hlimR : withinLimit h.config.maxRegisterLen h.context.predecessorAccountId.length = true)
    (hutf : Utf8.utf8Ok h.context.predecessorAccountId = true)
    (hab : h.context.predecessorAccountId.length ≤ 64) (hab0 : 0 < h.context.predecessorAccountId.length)
    (hlim : withinLimit h.config.maxStorageKeyLen
      (pre ++ (bytes32 (UInt32.ofNat h.context.predecessorAccountId.length) ++ h.context.predecessorAccountId)).length = true)
    (hvlim : withinLimit h.config.maxStorageValueLen 16 = true)
    (hreg : withinLimit h.config.maxRegisterLen 16 = true)
    (hbud : 4 * lookupProofBound (contractKey h.context.currentAccountId
      (pre ++ (bytes32 (UInt32.ofNat h.context.predecessorAccountId.length) ++ h.context.predecessorAccountId))) + 48 ≤ bud)
    (hsome : h.storage (pre ++ (bytes32 (UInt32.ofNat h.context.predecessorAccountId.length) ++
      h.context.predecessorAccountId)) = some (storeBytes (.i64 x0) 8 ++ storeBytes (.i64 x1) 8))
    (hdep : depLo h ||| depHi h ≠ 0)
    (hlog : ∀ lo hi : UInt64, LogStr.LogOk h (logText lo hi h.context.predecessorAccountId)
      (logText lo hi h.context.predecessorAccountId).length)
    (hfit16 : LogFits h 16) (hov16 : h.extCosts.cost "read_memory_byte" * 16 < 2 ^ 64)
    (hfitS : LogFits h textSupply.length) (hovS : h.extCosts.cost "read_memory_byte" * textSupply.length < 2 ^ 64)
    (C : IProp GF) [Persistent C] (lpc : UInt32) (Dp : IProp GF) (K879 : Nat → NewBody.Keep → Nat)
    (H879 : PanicSpecD cfg lim inst mi C n g ta A gt lpc maxP f879 SP Dp D 1053016 21 1053040 K879 textSupply)
    (Φ : Post NearState GF) :
    code232 e n maxP inst mi A mx ∗ C ∗
      credits Cg (costReg cfg F pl h
        (pre ++ (bytes32 (UInt32.ofNat h.context.predecessorAccountId.length) ++ h.context.predecessorAccountId))
        x0 x1 t0 t1 h.context.predecessorAccountId K879 + R) ∗
      g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - (224 + SP)) (224 + SP) ∗
      selfCells n self (storeBytes (.i64 t0) 8 ++ storeBytes (.i64 t1) 8) xb pp pc pl pre ∗
      stat232 n ta A lpc Dp aidx ∗ heapInv n maxP hl live F ∗ mhostPt h ∗
      (∀ (hl' F' : Nat) (h' : NearState) (f' : Frame),
        ⌜F' ≤ F + 13 ∧ LenUp hl 13 hl' ∧
          PostReg e h (pre ++ (bytes32 (UInt32.ofNat h.context.predecessorAccountId.length) ++
              h.context.predecessorAccountId))
            (StorageBalanceBounds.u128Of (x0.toNat + 2 ^ 64 * x1.toNat + depOf h)) st bud
            (logText (depLo h) (depHi h) h.context.predecessorAccountId) h' ∧
          dcase (depOf h) (some (x0.toNat + 2 ^ 64 * x1.toNat)) 0 (t0.toNat + 2 ^ 64 * t1.toNat) = .ok⌝ -∗
        credits Cg (cfg.regularOpCost + R) -∗ g ↦[wg] ⟨gt, .i32 s⟩ -∗
        stk n (s.toNat - (224 + SP)) (224 + SP) -∗
        selfCells n self (StorageBalanceBounds.u128Of (t0.toNat + 2 ^ 64 * t1.toNat + depOf h)) xb pp pc pl pre -∗
        stat232 n ta A lpc Dp aidx -∗ heapInv n maxP hl' live F' -∗ mhostPt h' -∗ Φ.ret [] f') ∗
      (∀ hX, ⌜keep hX = keep h ∧
          dcase (depOf h) (some (x0.toNat + 2 ^ 64 * x1.toNat)) 0 (t0.toNat + 2 ^ 64 * t1.toNat) ≠ .ok⌝ -∗
        panicked Cg hX (dcase (depOf h) (some (x0.toNat + 2 ^ 64 * x1.toNat)) 0 (t0.toNat + 2 ^ 64 * t1.toNat)).text -∗
        Φ.trap)
      ⊢ mwpi cfg lim d ⟨#[.i32 self, .i32 0, .i64 0, .i64 0, .i32 0, .i64 0, .i64 0], inst, mi⟩ [] f232.body Φ := by
  iintro ⟨#Hk, #HC, Hc, Hg, Stk, HS, HT, Hinv, Hh, Wok, Wtr⟩
  iunfold code232 at Hk
  icases Hk with ⟨#Hseg, #HD, #F444, #F529, #H526c, #F526, #H394c, #F394, -, -, -, -, -, -, -⟩
  ihave #HIC : ifaceCode e inst mi A n mx $$ []
  · iunfold codeSeg, tailCode at Hseg
    icases Hseg with ⟨-, ⟨-, -, -, #H, -⟩, -⟩
    iexact H
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold Interface.ifaceCode at HIC
    icases HIC with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩
    iexact Hi
  iunfold stat232 at HT
  icases HT with ⟨HI, H12, HDs, HPs, HHs, HWs, HLs, HPS, HH, HDp, HM, HZ, HSt, HU8, Hvt⟩
  iunfold selfCells at HS
  icases HS with ⟨HTb, HX, HP, HPre⟩
  icases splitB (a := self.toNat) (b := self.toNat + 8) (storeBytes (.i64 t0) 8) _ (by simp) $$ HTb with ⟨Ht0, Ht8⟩
  have hn := hm.mem
  have hg := hm.glob
  have hlt := s.toNat_lt
  have hLn : (UInt32.ofNat h.context.predecessorAccountId.length).toNat = h.context.predecessorAccountId.length := by
    simp; omega
  have e0 : (s - 144).toNat = s.toNat - 144 := by rw [StorageBalanceBounds.tsub' _ _ (by simp; omega)]; simp
  have e24 : (s - 144 + 24).toNat = s.toNat - 120 := by simp [UInt32.toNat_add, e0]; omega
  have e32 : (s - 144 + 32).toNat = s.toNat - 112 := by simp [UInt32.toNat_add, e0]; omega
  have e40 : (s - 144 + 40).toNat = s.toNat - 104 := by simp [UInt32.toNat_add, e0]; omega
  have e56 : (s - 144 + 56).toNat = s.toNat - 88 := by simp [UInt32.toNat_add, e0]; omega
  have es24 : (self + 24).toNat = self.toNat + 24 := by simp [UInt32.toNat_add]; omega
  -- the frame
  icases stkSp (80 + SP) 144 (by omega) $$ Stk with ⟨Lo, Fr⟩
  icases stkSp 24 120 rfl $$ Fr with ⟨F0, Fr⟩
  icases stkSp 8 112 rfl $$ Fr with ⟨O0, Fr⟩
  icases stkSp 8 104 rfl $$ Fr with ⟨O8, Fr⟩
  icases stkSp 8 96 rfl $$ Fr with ⟨U0, Fr⟩
  icases stkSp 8 88 rfl $$ Fr with ⟨U8, Fr⟩
  icases stkSp 12 76 rfl $$ Fr with ⟨V, Fr⟩
  icases stkSp 4 72 rfl $$ Fr with ⟨F68, Fr⟩
  icases stkSp 24 48 rfl $$ Fr with ⟨F72, Fr⟩
  icases stkSp 16 32 rfl $$ Fr with ⟨F96, Fr⟩
  icases stkSp 12 20 rfl $$ Fr with ⟨F112, Fr⟩
  icases stkSp 4 16 rfl $$ Fr with ⟨F124, F128⟩
  icases stk_bytes' $$ O0 with ⟨%ob0, %hob0, O0⟩
  icases stk_bytes' $$ O8 with ⟨%ob8, %hob8, O8⟩
  icases stk_bytes' $$ U0 with ⟨%ub0, %hub0, U0⟩
  icases stk_bytes' $$ U8 with ⟨%ub8, %hub8, U8⟩
  icases stk_bytes' $$ V with ⟨%vb, %hvb, V⟩
  iunfold costReg at Hc
  generalize hKD : attachedDepositUse h = KD
  generalize hK526 : cost526 cfg F h = K526
  generalize hK394 : cost394 cfg F pl (UInt32.ofNat h.context.predecessorAccountId.length) (predecessorHost h 0) (pre ++ (bytes32 (UInt32.ofNat h.context.predecessorAccountId.length) ++ h.context.predecessorAccountId)) = K394
  generalize hKS : costSegAll cfg (F + 2) pl (UInt32.ofNat h.context.predecessorAccountId.length) h (pre ++ (bytes32 (UInt32.ofNat h.context.predecessorAccountId.length) ++ h.context.predecessorAccountId)) x0 x1 t0 t1 (depLo h) (depHi h) h.context.predecessorAccountId K879 = KS
  simp only [f232]
  -- the prologue
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  -- 529: the deposit at sp + 24
  have t0' : types[0]!.params.length = 1 := rfl
  have ha529 := hm.funcs 529 (by decide)
  have ha526 := hm.funcs 526 (by decide)
  have ha394 := hm.funcs 394 (by decide)
  have t13 : types[13]!.params.length = 2 := rfl
  icases stkSp (80 + SP - 32) 32 (by omega) $$ Lo with ⟨Lo, L32⟩
  mstep; mstep; mstep
  mcall (EnvGetters.f529_spec_host cfg lim (d + 1) types[0]! rfl inst mi e A n g ta mx hm (by omega) Cg gt
      (s - 144) (by omega) (by omega) (s - 144 + 24) ob0 ob8 hob0 hob8 h hview) using [Hg HI HDs L32 O0 O8 Hh]
  · iunfold EnvGetters.pre529
    ihave L32 := stkA (b := (s - 144).toNat - 32) (by omega) $$ L32
    ihave O0 := memBytes_addr (b := (s - 144 + 24).toNat) (by omega) $$ O0
    ihave O8 := memBytes_addr (b := (s - 144 + 24).toNat + 8) (by omega) $$ O8
    iframe Hg HI HDs L32 O0 O8 Hh
    ipureintro; rfl
  iunfold EnvGetters.post529 at HQ
  icases HQ with ⟨%hrs, Hg, HI, HDs, L32, O0, O8, Hh⟩
  subst hrs
  ihave O0 := memBytes_addr (b := (s - 144).toNat + 24) (by omega) $$ O0
  ihave O8 := memBytes_addr (b := (s - 144 + 32).toNat + 0) (by omega) $$ O8
  ihave U0 := memBytes_addr (b := (s - 144).toNat + 40) (by omega) $$ U0
  ihave U8 := memBytes_addr (b := (s - 144).toNat + 48) (by omega) $$ U8
  mstep; mstep; mstep; mstep; mstep [O8] with simp [storeBytes]
  simp only [U128From.decodeLE_storeBytes_i64, UInt64.ofNat_toNat]
  mstep; mstep [U8] with simp [storeBytes]
  mstep; mstep; mstep [O0] with simp [storeBytes]
  simp only [U128From.decodeLE_storeBytes_i64, UInt64.ofNat_toNat]
  mstep; mstep [U0] with simp [storeBytes]
  -- the blocks, the test of the deposit
  mstep; mstep
  mstep; mstep; mstep; mstep; mstep
  mstep_not_taken with (simp [Numeric.bool, Numeric.irelop64, hdep])
  -- 526: the predecessor at sp + 56
  ihave Lo := stkJ2 (s.toNat - (224 + SP)) (by omega) (by omega) $$ Lo L32
  icases stkSp (80 + SP - 208) 208 (by omega) $$ Lo with ⟨Lo, L208⟩
  ihave HIR : ifaceR n ta A $$ [HI H12]
  · iunfold ifaceR; iframe HI H12
  have hroomR : roomFor hl maxP (UInt32.ofNat h.context.predecessorAccountId.length) :=
    LookupMapOps.roomFor_ofK (k := 18) (UInt32.ofNat h.context.predecessorAccountId.length) (by omega) hroom (LookupMapOps.lenIn_zero hl hroom.1) (by omega)
  mstep; mstep; mstep
  mcall (PredecessorId.f526_spec cfg lim (d + 1) types[0]! rfl inst mi e A n g ta mx hm (by omega) Cg gt (s - 144)
      (s - 144 + 56) (by omega) (by omega) (by omega) aidx maxP hl live F hF vb hvb h hview hvalid hlimR
      ⟨hab0, by omega, hroomR⟩ hutf) using [Hg HIR HPs L208 Hvt Hinv V HU8 Hh]
      with (rw [hK526]; mstep_norm_full; omega)
  · iunfold PredecessorId.pre526
    ihave L208 := stkA (b := (s - 144).toNat - 208) (by omega) $$ L208
    ihave V := memBytes_addr (b := (s - 144 + 56).toNat) (by omega) $$ V
    iframe Hg HIR HPs L208 Hvt Hinv V HU8 Hh
    ipureintro; rfl
  iunfold PredecessorId.post526 at HQ
  icases HQ with ⟨%hrs, Hg, HIR, HPs, L208, Hvt, HSA, HU8, Hh⟩
  subst hrs
  iunfold strAt at HSA
  icases HSA with ⟨%p, %hl1, %⟨hp0, hhl1⟩, Hinv, Hab, V0, V4, V8⟩
  have hlen1 : LenIn hl 1 hl1 := LookupMapOps.lenIn_step (UInt32.ofNat h.context.predecessorAccountId.length) (by omega) (LookupMapOps.lenIn_zero hl hroom.1) hhl1
  icases AllocZeroed.heapInv_bound n maxP hl1 _ F $$ Hinv with ⟨%⟨hbnd, -⟩, Hinv⟩
  have hpb : p.toNat + h.context.predecessorAccountId.length ≤ 2 ^ 32 := by
    have := hbnd p.toNat h.context.predecessorAccountId.length List.mem_cons_self
    have := hroom.2.2.2
    have := hlen1.2.1
    omega
  ihave V := joinB (a := (s - 144 + 56).toNat) (b := (s - 144 + 56).toNat + 4) (bytes32 p) _ (by simp [bytes32]) $$ [V0 V4 V8]
  · iframe V0
    iapply join64' (a := (s - 144 + 56).toNat + 4) (b := (s - 144 + 56).toNat + 4 + 4) _ _ rfl
    iframe V4 V8
  -- the host after 526
  have hk1 : keep (predecessorHost h 0) = keep h := keep_predecessorHost h
  have f1 : (predecessorHost h 0).storageAccounting = h.storageAccounting ∧ (predecessorHost h 0).config = h.config ∧ (predecessorHost h 0).storage = h.storage ∧
      (predecessorHost h 0).context = h.context ∧ (predecessorHost h 0).storageProofSize = h.storageProofSize := by
    simp [predecessorHost, u64Max, NearState.setRegister]
  obtain ⟨f1a, f1c, f1s, f1x, f1p⟩ := f1
  -- 394: contains_key
  icases stkSp 32 176 rfl $$ L208 with ⟨L32', L176⟩
  icases ReadRegister.iface_of_ifaceR n ta A $$ HIR with ⟨HI, H12⟩
  mstep; mstep
  mstep; mstep; mstep; mstep; mstep; mstep
  mcall (LookupMapContains.f394_spec cfg lim (d + 1) types[13]! rfl inst mi e A n g ta mx hm (by omega) Cg gt
      (s - 144) (self + 24) pp pc pl (s - 144 + 56) p (UInt32.ofNat h.context.predecessorAccountId.length) (UInt32.ofNat h.context.predecessorAccountId.length) aidx maxP hl1 ((p.toNat, h.context.predecessorAccountId.length) :: live) F hF pre h.context.predecessorAccountId
      (by omega) (by omega) hpre hLn.symm (by omega) hpl hl0 hpp (by omega) (by omega)
      (MeasureUsage.heapRoom_shift hroom hlen1 (by omega)) (predecessorHost h 0) st (by rw [f1a]; exact hacc)
      (by rw [f1c]; exact hlim) hcanon.1 hcanon.2 (by rw [f1s, f1x]; exact hlink _) (hproof.congr f1p f1c)
      (by rw [f1x]; omega)) using [Hg L176 HI HHs Hvt Hinv HP HPre V Hab Hh]
      with (simp only [t13]; rw [hK394]; mstep_norm_full; omega)
  · iunfold LookupMapContains.pre394
    ihave L176 := stkA (b := (s - 144).toNat - 176) (by omega) $$ L176
    iframe Hg L176 HI HHs Hvt Hinv HP HPre V Hab Hh
    ipureintro; rfl
  iunfold LookupMapContains.post394 at HQ
  icases HQ with ⟨%hrs, Hg, L176, HI, HHs, Hvt, ⟨%hl2, %hlen2, Hinv⟩, HP, HPre, V, Hab, ⟨%h2, %hq2, Hh⟩⟩
  subst hrs
  rw [show (predecessorHost h 0).storage (pre ++ (bytes32 (UInt32.ofNat h.context.predecessorAccountId.length) ++ h.context.predecessorAccountId)) = h.storage (pre ++ (bytes32 (UInt32.ofNat h.context.predecessorAccountId.length) ++ h.context.predecessorAccountId)) by rw [f1s], hsome]
  simp only [StorageRead.foundU64]
  mstep_taken with (simp)
  -- the host after 394
  obtain ⟨s2, hacc2, hcan2, hlink2, hp2, he2⟩ := StorageHasKeyPost.next hq2 hcanon
    (by intro k; rw [f1s, f1x]; exact hlink k) (hproof.congr f1p f1c) (by rw [f1x]; omega)
  have hk2 : keep h2 = keep h := by rw [keep_of_erase he2, keep_acc, hk1]
  have hs2 : h2.storage = h.storage := by rw [erase_field he2 NearState.storage fun _ => rfl]; exact f1s
  have hc2 : h2.config = h.config := by rw [erase_field he2 NearState.config fun _ => rfl]; exact f1c
  have hid2 : h2.context.currentAccountId = h.context.currentAccountId := by
    rw [erase_field he2 (fun x : NearState => x.context.currentAccountId) fun _ => rfl]; rw [f1x]
  have hv2 : h2.context.isView = h.context.isView := by
    rw [erase_field he2 (fun x : NearState => x.context.isView) fun _ => rfl]; rw [f1x]
  have hx2' : h2.extCosts = h.extCosts := congrArg NewBody.Keep.extCosts hk2
  have hKS' : costSegAll cfg (F + 2) pl (UInt32.ofNat h.context.predecessorAccountId.length) h2 (pre ++ (bytes32 (UInt32.ofNat h.context.predecessorAccountId.length) ++ h.context.predecessorAccountId)) x0 x1 t0 t1 (depLo h) (depHi h) h.context.predecessorAccountId K879 = KS := by
    rw [← hKS]; exact DepositCosts.costSegAll_congr cfg _ pl (UInt32.ofNat h.context.predecessorAccountId.length) hk2 (by rw [hs2]) _ _ _ _ _ _ _ _
  have hlen12 : LenUp hl 3 hl2 :=
    DepositSeg.lenUp_of_lenIn (MeasureUsage.lenIn_trans hlen1 hlen2) hroom.2.1
  -- the frame for the segment
  ihave Lo := stkJ2 (s.toNat - (224 + SP)) (by omega) (by omega) $$ Lo L32'
  ihave Lo := stkJ2 (s.toNat - (224 + SP)) (by omega) (by omega) $$ Lo L176
  ihave Lo : stk n ((s - 144).toNat - 80 - SP) (80 + SP) $$ [Lo]
  · iapply stkA2 (by omega) (by omega) $$ Lo
  ihave F0 := stkA (b := (s - 144).toNat) (by omega) $$ F0
  ihave O0 := stk_u64 (GF := GF) n _ _ $$ O0
  ihave O8 := stk_u64 (GF := GF) n _ _ $$ O8
  ihave H24 := stkJ (a := (s - 144).toNat + 24) (b := (s - 144 + 32).toNat + 0) (k1 := 8) (k2 := 8) (k := 16)
    (by omega) rfl $$ [O0 O8]
  · iframe O0 O8
  ihave Hu := joinB (a := (s - 144 + 40).toNat) (b := (s - 144).toNat + 48) (storeBytes (.i64 (depLo h)) 8) _
    (by simp; omega) $$ [U0 U8]
  · iframe U8
    iapply memBytes_addr (by omega) $$ U0
  ihave Hu : n ↦[wms][ (s - 144 + 40).toNat ] u128Bytes (depLo h) (depHi h) $$ [Hu]
  · simp only [u128Bytes]; iexact Hu
  ihave F68 := stkA (b := (s - 144).toNat + 68) (by omega) $$ F68
  ihave F72 := stkA (b := (s - 144).toNat + 72) (by omega) $$ F72
  ihave F96 := stkA (b := (s - 144).toNat + 96) (by omega) $$ F96
  ihave F112 := stkA (b := (s - 144).toNat + 112) (by omega) $$ F112
  ihave F124 := stkA (b := (s - 144).toNat + 124) (by omega) $$ F124
  ihave F128 := stkA (b := (s - 144).toNat + 128) (by omega) $$ F128
  have hdep0 : depOf h ≠ 0 := by
    intro h0
    apply hdep
    exact (EnvGetters.u64_or_eq_zero _ _).2 h0
  have hb2 : bud - lookupProofBound (contractKey (predecessorHost h 0).context.currentAccountId
      (pre ++ (bytes32 (UInt32.ofNat h.context.predecessorAccountId.length) ++ h.context.predecessorAccountId))) =
      bud - lookupProofBound (contractKey h.context.currentAccountId
      (pre ++ (bytes32 (UInt32.ofNat h.context.predecessorAccountId.length) ++ h.context.predecessorAccountId))) := by
    rw [f1x]
  rw [hb2] at hp2
  iapply mwpi_code_eq (code' := seg406 ++ tail232) ?_
  · rfl
  iapply seg406_all cfg lim d e inst mi A n g ta mx hm D (by omega) Cg (cfg.regularOpCost + R) gt (s - 144) self
    (depHi h) (depLo h) 0 0 0 SP hSP (by omega) (by omega) (by omega) (by omega) pp pc pl t0 t1 x0 x1 aidx maxP hl2
    ((p.toNat, h.context.predecessorAccountId.length) :: live) (F + 2) (by unfold okG at hF ⊢; omega) pre p h.context.predecessorAccountId hpre hab hab0 hpl hl0 hpp hpb
    List.mem_cons_self (DepositSeg.heapRoom_up hroom hlen12 (by omega)) h2 s2
    (by rw [hv2]; exact hview) hacc2 hcan2 hlink2 hp2
    (by rw [hid2, hs2, hsome]; simp [readProofCost, writeProofCost]; omega)
    (by rw [hc2]; exact hlim) (by rw [hc2]; exact hvlim) (by rw [hc2]; exact hreg) (by rw [hs2]; exact hsome)
    (fun _ _ => DepositSeg.LogOk.of_keep hk2 (hlog _ _))
    (InternalDepositOverflow.LogFits.of_keep hk2 hfit16) (by rw [hx2']; exact hov16)
    (InternalDepositOverflow.LogFits.of_keep hk2 hfitS) (by rw [hx2']; exact hovS) C lpc Dp K879 H879 _
  rw [hKS']
  iframe Hseg HC Hg Lo F0 H24 Hu V Hab F68 F72 F96 F112 F124 F128 HSt Hvt Hinv HI H12 HWs HLs HPS HH HDp HM Ht0 Ht8
    HP HPre Hh
  isplitl [Hc]
  · iapply credits_mono (by omega) $$ Hc
  isplitl [Wok HX HDs HPs HHs HZ HU8]
  · iintro %l2' %hl' %F' %h' %⟨hF', hup, hpost, hok1, hok2⟩ Hc Hg Lo HSt Hvt Hinv HI H12 HWs HLs HPS HH HDp HM HT HP HPre Hh
    ihave Lo := stkA2 (b := s.toNat - (224 + SP)) (k' := 224 + SP) (by omega) (by omega) $$ Lo
    rw [show s - 144 + 144 = s by simp, List.erase_cons_head]
    ihave HS : selfCells n self (StorageBalanceBounds.u128Of (t0.toNat + 2 ^ 64 * t1.toNat + depOf h)) xb pp pc pl pre
      $$ [HT HX HP HPre]
    · iunfold selfCells; iframe HT HX HP HPre
    ihave HB : stat232 n ta A lpc Dp aidx $$ [HI H12 HDs HPs HHs HWs HLs HPS HH HDp HM HZ HSt HU8 Hvt]
    · iunfold stat232; iframe HI H12 HDs HPs HHs HWs HLs HPS HH HDp HM HZ HSt HU8 Hvt
    simp only [Post.mblock, Post.mseq, List.nil_append]
    iapply Wok $$ %hl' %F' %(LogStr.logged h' (logText (depLo h) (depHi h) h.context.predecessorAccountId))
      %⟨#[.i32 self, .i32 (s - 144), .i64 l2', .i64 (depLo h), .i32 0, .i64 0, .i64 0], inst, mi⟩
      %⟨by omega, (hlen12.trans hup).mono (by omega), ⟨h2, s2, h', hq2, hacc2, hcan2, hlink2, hp2, he2, hpost, rfl⟩,
        dcase_reg_ok _ _ _ _ hdep0 hok1 hok2⟩
      Hc Hg Lo HS HB Hinv Hh
  · iintro %hX %⟨hkX, hno⟩ HTr
    simp only [Post.mblock, Post.mseq_trap]
    iapply Wtr $$ %hX %⟨hkX.trans hk2, dcase_reg_nok _ _ _ _ hdep0 hno⟩
    iapply panicked_conv ?_ $$ HTr
    exact (dcase_reg_text _ _ 0 _ hdep0 hno).symm

end Body

end WNear.Binary.DepositBody
