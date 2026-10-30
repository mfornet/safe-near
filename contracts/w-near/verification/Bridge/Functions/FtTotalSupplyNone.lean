import Bridge.Functions.FtTotalSupply
import Bridge.Functions.StateReadNone
import Bridge.Functions.UnwrapOrDefaultNone

/-!
# `ft_total_supply` (function 296) on an uninitialized contract

```wat
;; 296 ft_total_supply(): sp -= 144 (the frame at sp0 = sp - 144)
setup_panic_hook()                               ;; 522
set_blockchain_interface(1, 1050188)             ;; 520
state_read(sp0 + 72)                             ;; 219: None at sp0 + 72 (no "STATE")
unwrap_or_default(sp0 + 32, sp0 + 72)            ;; 155: Contract::default panics, a trap
...                                              ;; not reached
```

`body296None`: from the statics `f296_spec` starts from, plus the panic path's (`staticsP`: the
`panic_utf8` vtable slot and `PanicOnDefault`'s message), and a host with no value at `STATE`
(`ReadNone`), the body traps with the host after `storage_read` panicked with "The contract is
not initialized", the gas counter within `Cg`. Segment A (`FtTotalSupply.segA`) is unchanged;
`segBNone` runs `state_read`'s `None` branch (`f219_spec_none`) and `unwrap_or_default`'s
(`f155_spec_none`).
-/

namespace WNear.Binary.FtTotalSupply

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.Interface (IfaceMod iface ifaceCode)
open WNear.Binary.ReadRegister (ifaceR iface_of_ifaceR)
open WNear.Binary.VecFromElem (stk)
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.BorshFT (splitB stkJ stkW stkSp stkA)
open WNear.Binary.BorshInt (stk_bytes')
open WNear.Binary.StateRead (stateCode pre219 post219None noneAt)
open WNear.Binary.PanicStr (panicCode panicSlot panicked notInit)

open Near.TrieAccounting Near.TrieConstruction Near.TrieOverlay in
/-- What `ft_total_supply` needs of the host `h` on an uninitialized contract: no value at
`STATE`, the storage premises of `storage_read` (as `ReadOk`'s), and those of `panic_utf8` for
the 31 bytes of "The contract is not initialized" (they fit the log limit, and their
`read_memory_byte` cost a `u64`). -/
structure ReadNone (h : NearState) (st : Near.TrieOverlay.State) : Prop where
  value : h.storage WNear.stateKey = none
  acc : h.storageAccounting = some st
  keyLen : withinLimit h.config.maxStorageKeyLen 5 = true
  trie : build st.entries = .ok st.base
  zero : zeroHash ∉ st.base.witness.map Prod.fst
  link : h.storage WNear.stateKey = viewVal st (contractKey h.context.currentAccountId WNear.stateKey)
  proof : ProofBudget h st (lookupProofBound (contractKey h.context.currentAccountId WNear.stateKey))
  logFits : LogFits h 31
  readByte : h.extCosts.cost "read_memory_byte" * 31 < 2 ^ 64

/-- `storage_read` keeps the config, the logs, the ext costs and the execution issue. -/
theorem storageReadPost_fields {h h1 : NearState} {key : List UInt8} {r : UInt64}
    {st : Near.TrieOverlay.State} (H : StorageReadPost h key r st h1) :
    h1.config = h.config ∧ h1.logs = h.logs ∧ h1.extCosts = h.extCosts ∧
      h1.lastExecutionIssue = h.lastExecutionIssue := by
  obtain ⟨s2, -, -, he⟩ := H
  have hr : ∀ (x : NearState) v, (storageReadRegs x r v).config = x.config ∧
      (storageReadRegs x r v).logs = x.logs ∧ (storageReadRegs x r v).extCosts = x.extCosts ∧
      (storageReadRegs x r v).lastExecutionIssue = x.lastExecutionIssue := by
    intro x v; unfold storageReadRegs; split
    · split <;> exact ⟨rfl, rfl, rfl, rfl⟩
    · exact ⟨rfl, rfl, rfl, rfl⟩
  obtain ⟨r1, r2, r3, r4⟩ := hr { h with storageAccounting := some s2 } (h.storage key)
  exact ⟨(erase_field he NearState.config fun _ => rfl).trans r1,
    (erase_field he NearState.logs fun _ => rfl).trans r2,
    (erase_field he NearState.extCosts fun _ => rfl).trans r3,
    (erase_field he NearState.lastExecutionIssue fun _ => rfl).trans r4⟩

theorem logFits_of {h h1 : NearState} (hc : h1.config = h.config) (hl : h1.logs = h.logs) {k : Nat}
    (H : LogFits h k) : LogFits h1 k := by
  intro limit hm
  rw [hl]
  exact H limit (hc ▸ hm)

theorem panicUtf8Use_of {h h1 : NearState} (hx : h1.extCosts = h.extCosts) (k : Nat) :
    panicUtf8Use h1 k = panicUtf8Use h k := by
  simp [panicUtf8Use, panicUtf8Charges, chargesUse, chargeUse, hx]

section Res

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The code of the panic path (persistent): `Contract::default` (156), `env::panic_str`
(521), `LocalKey::with` (448), the trampoline and the `panic_utf8` host (`panicCode`). -/
def codeP (e inst : Nat) (mi : ModuleInst) (A : Nat → Nat) : IProp GF :=
  iprop(A 156 ↪[wf] FuncInst.wasm types[0]! inst f156 ∗ A 521 ↪[wf] FuncInst.wasm types[14]! inst f521 ∗
    A 448 ↪[wf] FuncInst.wasm types[14]! inst f448 ∗ panicCode e inst mi A)

instance (e inst : Nat) (mi : ModuleInst) (A : Nat → Nat) : Persistent (codeP (GF := GF) e inst mi A) := by
  unfold codeP; infer_instance

/-- The statics of the panic path: the `panic_utf8` vtable slot and the message of
`PanicOnDefault` at 1050868. -/
def staticsP (n ta : Nat) (A : Nat → Nat) : IProp GF :=
  iprop(panicSlot n ta A ∗ n ↦[wms][ 1050868 ] notInit)

end Res

/-! ## Segment B on `None` -/

section SegBNone

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The cost of segment B on `None`: `state_read`'s `None` branch, `unwrap_or_default`'s, and
`panic_utf8` of the 31-byte message. -/
def costBNone (cfg : WasmConfig) (h : NearState) : Nat :=
  600 * cfg.regularOpCost + storageReadUse h StateRead.stateKey 5 + panicUtf8Use h 31

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- Segment B on an absent `STATE`: `state_read` (219) leaves `None` at `sp0 + 72`, and
`unwrap_or_default` (155) traps through `Contract::default`, the host after `storage_read`
panicked. -/
theorem segBNone (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (e inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 18 < lim.maxCallDepth)
    (Cg R : Nat) (gt : GlobalType) (s : UInt32) (hs : 736 ≤ s.toNat) (hal : s.toNat % 8 = 0)
    (idx : UInt32) (maxP len : Nat) (h : NearState) (st : Near.TrieOverlay.State) (hr : ReadNone h st)
    (rest : List Instr) (Φ : Post NearState GF) :
    codeB e inst mi A n maxP ∗ ifaceCode e inst mi A n (some maxP) ∗ codeP e inst mi A ∗
      credits Cg (costBNone cfg h + R) ∗ g ↦[wg] ⟨gt, .i32 (s - 144)⟩ ∗ ifaceR n ta A ∗
      stk n (s.toNat - 736) 592 ∗ stk n (s.toNat - 72) 40 ∗ vt n 1057464 idx ta (A 578) ∗
      heapInv n maxP len [] 1 ∗ n ↦[wms][ 1049788 ] StateRead.stateKey ∗ staticsP n ta A ∗ mhostPt h ∗
      (∀ h1, ⌜StorageReadPost h StateRead.stateKey 0 st h1⌝ -∗ panicked Cg h1 notInit -∗ Φ.trap)
      ⊢ mwpi cfg lim d ⟨#[.i32 (s - 144)], inst, mi⟩ [] (bodyB ++ rest) Φ := by
  iintro ⟨#Hk, #HIC, #HP, Hc, Hg, HI, Lo, F72, Hvt, Hinv, Hkey, HSP, Hh, W⟩
  ihave #Hk' := Hk
  iunfold codeB at Hk'
  icases Hk' with ⟨#HSC, -, #F219, #F155, -, -, -, -, #Hi⟩
  ihave #HP' := HP
  iunfold codeP at HP'
  icases HP' with ⟨#F156, #F521, #F448, #Hpc⟩
  iunfold staticsP at HSP
  icases HSP with ⟨Hslot, Hmsg⟩
  obtain ⟨hv, hacc, hlim, hb, hz, hlink, hproof, hfit, hov⟩ := hr
  rw [← StateRead.stateKey_eq] at hv hlink hproof
  unfold costBNone
  have hn := hm.mem
  have hg := hm.glob
  have ha219 := hm.funcs 219 (by decide)
  have ha155 := hm.funcs 155 (by decide)
  have t0 : types[0]!.params.length = 1 := rfl
  have hlt := s.toNat_lt
  have e0 : (s - 144).toNat = s.toNat - 144 := by rw [tsub _ _ (by simp; omega)]; simp
  have e1 : (s - 144 - 16).toNat = s.toNat - 160 := by rw [tsub _ _ (by simp [e0]; omega), e0]; simp; omega
  have e2 : (s - 144 - 16 - 16).toNat = s.toNat - 176 := by
    rw [tsub _ _ (by simp [e1]; omega), e1]; simp; omega
  have a72 : (s - 144 + 72).toNat = s.toNat - 72 := by simp [UInt32.toNat_add, e0]; omega
  iapply mwpi_seq
  simp only [bodyB]
  -- state_read(sp0 + 72): None
  icases stk_bytes' $$ F72 with ⟨%ob, %hob, F72⟩
  mstep; mstep; mstep
  have S219 := StateRead.f219_spec_none (GF := GF) cfg lim (d + 1) types[0]! rfl inst mi e A n g ta (some maxP) hm
    (by omega) Cg gt (s - 144) (s - 144 + 72) (by omega) (by omega) (by omega) idx maxP len [] ob hob h hv st hacc
    hlim hb hz hlink hproof
  simp only [StorageReadWrap.costS] at S219
  mcall S219 using [Hg HI Lo Hvt Hinv F72 Hkey Hh]
  · iunfold pre219
    ihave Lo := stkA (b := (s - 144).toNat - 592) (by omega) $$ Lo
    ihave F72 := memBytes_addr (b := (s - 144 + 72).toNat) (by omega) $$ F72
    iframe Hg HI Lo Hvt Hinv F72 Hkey Hh
    ipureintro; rfl
  iunfold post219None at HQ
  icases HQ with ⟨%hrs, Hg, HI, Lo, -, -, Ho, -, ⟨%h1, %hq1, Hh⟩⟩
  subst hrs
  obtain ⟨hcfg, hlogs, hext, -⟩ := storageReadPost_fields hq1
  -- the zero niche at sp0 + 72 + 24
  iunfold noneAt at Ho
  icases splitB (a := (s - 144 + 72).toNat) (b := (s - 144 + 72).toNat + 28) (ob.take 24 ++ [0, 0, 0, 0])
    (ob.drop 28) (by simp [hob]) $$ Ho with ⟨Ho, -⟩
  icases splitB (a := (s - 144 + 72).toNat) (b := (s - 144 + 72).toNat + 24) (ob.take 24) [0, 0, 0, 0]
    (by simp [hob]) $$ Ho with ⟨-, H24⟩
  ihave H24 := (show (n ↦[wms][ (s - 144 + 72).toNat + 24 ] [0, 0, 0, 0] : IProp GF) ⊢
    n ↦[i32][ (s - 144 + 72).toNat + 24 ] 0 by rw [StateRead.bytes32_zero']) $$ H24
  -- the frames of `env::panic_str` and `LocalKey::with`, out of the stack
  icases stkSp 560 32 rfl $$ Lo with ⟨-, Lo⟩
  icases stkSp 4 28 rfl $$ Lo with ⟨W0, Lo⟩
  icases stkSp 4 24 rfl $$ Lo with ⟨W4, Lo⟩
  icases stkSp 4 20 rfl $$ Lo with ⟨W8, Lo⟩
  icases stkSp 4 16 rfl $$ Lo with ⟨W12, Lo⟩
  icases stkSp 8 8 rfl $$ Lo with ⟨-, Lo⟩
  icases stkSp 4 4 rfl $$ Lo with ⟨C0, C4⟩
  icases stk4_word $$ W0 with ⟨%w0, W0⟩
  icases stk4_word $$ W4 with ⟨%w4, W4⟩
  icases stk4_word $$ W8 with ⟨%w8, W8⟩
  icases stk4_word $$ W12 with ⟨%w12, W12⟩
  icases stk4_word $$ C0 with ⟨%c0, C0⟩
  icases stk4_word $$ C4 with ⟨%c4, C4⟩
  icases iface_of_ifaceR n ta A $$ HI with ⟨HI, -⟩
  -- unwrap_or_default(sp0 + 32, sp0 + 72): a trap
  mstep; mstep; mstep; mstep; mstep; mstep
  iapply mwpi_cons
  iapply (PanicStr.mwpi_callT' (i := 155) (a := A 155) (type := types[14]!) (inst := inst) (mi := mi)
    (code := f155) [.i32 (s - 144 + 32), .i32 (s - 144 + 72)])
  isplitr
  · iapply (UnwrapOrDefault.f155_spec_none cfg lim (d + 1) types[14]! inst mi e A n g ta (some maxP) hm
      (by omega) Cg ⟨gt, .i32 (s - 144)⟩ (s - 144) rfl (by omega) (by omega) (s - 144 + 32) (s - 144 + 72)
      c0 c4 w0 w4 w8 w12 h1 (logFits_of hcfg hlogs hfit) (by rw [hext]; exact hov))
    iframe F156 F521 F448 HIC Hpc
  isplitr
  · iexact F155
  isplitr
  · iexact Hi
  isplitr
  · ipureintro; exact ⟨rfl, ha155, rfl, by omega⟩
  isplitl [Hc]
  · iexact Hc
  isplitr
  · ipureintro; mstep_norm_full; rw [panicUtf8Use_of hext]; omega
  isplitl [H24 Hg HI Hslot C0 C4 W0 W4 W8 W12 Hmsg Hh]
  · iunfold UnwrapOrDefault.preNone, PanicStr.defaultPre, RegisterLen.frame4
    ihave C0 := memBytes_addr (b := (s - 144 - 16).toNat + 8) (by omega) $$ C0
    ihave C4 := memBytes_addr (b := (s - 144 - 16).toNat + 12) (by omega) $$ C4
    ihave W0 := memBytes_addr (b := (s - 144 - 16 - 16).toNat) (by omega) $$ W0
    ihave W4 := memBytes_addr (b := (s - 144 - 16 - 16).toNat + 4) (by omega) $$ W4
    ihave W8 := memBytes_addr (b := (s - 144 - 16 - 16).toNat + 8) (by omega) $$ W8
    ihave W12 := memBytes_addr (b := (s - 144 - 16 - 16).toNat + 12) (by omega) $$ W12
    iframe H24 Hg HI Hslot C0 C4 W0 W4 W8 W12 Hmsg Hh
    ipureintro; exact ⟨rfl, rfl⟩
  inext
  isplit
  · iintro %rs - HF
    iexfalso
    iexact HF
  · iintro HT
    simp only [Post.mseq_trap]
    iapply W $$ %h1 %hq1 HT

end SegBNone

/-! ## The body on `None` -/

section MainNone

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The cost of `ft_total_supply` (296) on an absent `STATE`, activation excluded: segment A's
475 `regular_op_cost`s and `costBNone`. -/
def cost296None (cfg : WasmConfig) (h : NearState) : Nat :=
  1075 * cfg.regularOpCost + storageReadUse h StateRead.stateKey 5 + panicUtf8Use h 31

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **The body of `ft_total_supply` on an uninitialized contract** (296), from its entry frame:
with the statics `body296` starts from, the panic path's (`staticsP`), 736 bytes of stack below
`s` and a host with no value at `STATE` (`ReadNone`), it traps, the host after `storage_read`
panicked with "The contract is not initialized". -/
theorem body296None (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (e inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 18 < lim.maxCallDepth)
    (Cg R : Nat) (gt : GlobalType) (s : UInt32) (hs : 736 ≤ s.toNat) (hal : s.toNat % 8 = 0)
    (old k3 idx ptr0 : UInt32) (maxP len : Nat) (h : NearState) (st : Near.TrieOverlay.State)
    (hr : ReadNone h st) (Φ : Post NearState GF) :
    code296 e inst mi A n maxP ∗ codeP e inst mi A ∗ credits Cg (cost296None cfg h + R) ∗
      g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 736) 736 ∗ statics n ta A old k3 idx ptr0 maxP len ∗
      staticsP n ta A ∗ mhostPt h ∗
      (∀ h1, ⌜StorageReadPost h StateRead.stateKey 0 st h1⌝ -∗ panicked Cg h1 notInit -∗ Φ.trap)
      ⊢ mwpi cfg lim d ⟨#[.i32 0], inst, mi⟩ [] f296.body Φ := by
  iintro ⟨#Hk, #HP, Hc, Hg, Stk, HS, HSP, Hh, W⟩
  iunfold code296 at Hk
  icases Hk with ⟨#KA, #KB, #KC⟩
  ihave #HIC : ifaceCode e inst mi A n (some maxP) $$ []
  · iunfold codeC at KC
    icases KC with ⟨#HIC, -⟩
    iexact HIC
  iunfold statics at HS
  icases HS with ⟨HH, Hkey, T116, T106, HB, HV, Hvt, Hinv, HsK, -⟩
  have hlt := s.toNat_lt
  icases stkSp 512 224 rfl $$ Stk with ⟨Lo512, Stk⟩
  icases stkSp 80 144 rfl $$ Stk with ⟨L2, Stk⟩
  icases stkSp 72 72 rfl $$ Stk with ⟨-, Stk⟩
  icases stkSp 40 32 rfl $$ Stk with ⟨F72, -⟩
  rw [f296_body]
  iapply segA cfg lim d inst mi A n g ta hm (by omega) Cg (costBNone cfg h + R) gt s hs hal old k3
    (bodyB ++ bodyC) Φ
  ihave L2 := stkA (b := s.toNat - 224) (by omega) $$ L2
  iframe KA Hg L2 HH Hkey T116 T106 HB HV
  isplitl [Hc]
  · iapply credits_mono (by unfold cost296None costBNone; omega) $$ Hc
  iintro Hc Hg L2 HI
  ihave Lo := stkJ (a := s.toNat - 736) (b := s.toNat - 736 + 512) (k1 := 512) (k2 := 80) (k := 592) rfl rfl
    $$ [Lo512 L2]
  · ihave L2 := stkA (b := s.toNat - 736 + 512) (by omega) $$ L2
    iframe Lo512 L2
  iapply segBNone cfg lim d e inst mi A n g ta hm hd Cg R gt s hs hal idx maxP len h st hr bodyC Φ
  ihave F72 := stkA (b := s.toNat - 72) (by omega) $$ F72
  iframe KB HIC HP Hc Hg HI Lo F72 Hvt Hinv HsK HSP Hh W

end MainNone

end WNear.Binary.FtTotalSupply
