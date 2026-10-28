import Bridge.Functions.NewBody
import Bridge.Functions.EnvGetters
import Bridge.Functions.StorageHasKey
import Bridge.Functions.FtTotalSupplyNone
import Bridge.Methods.NewData

/-!
# The body of `new` (function 290): the two panics

```wat
;; bodyA290: sp0 = sp - 64, setup_panic_hook, set_blockchain_interface
attached_deposit(sp0 + 8)                                        ;; 529
block
  block
    lo | hi == 0 ?  else br 0                                    ;; the deposit test
    state_exists() → br 1                                        ;; 552
    Contract::new(sp0 + 24); state_write; drop; sp += 64; return
  end
  panic_str(1050899, 33)  ;; "Method new doesn't accept deposit"
end
panic_str(1050932, 41)    ;; "The contract has already been initialized"
```

* `body290Dep`: a deposit (`depLo h ||| depHi h ≠ 0`): it traps, the host (unchanged by
  `attached_deposit`) panicked with "Method new doesn't accept deposit".
* `body290Init`: no deposit and `STATE` present: `state_exists` (552, `StorageHasKeyPost`) is
  true, it traps, the host after `storage_has_key` panicked with "The contract has already been
  initialized".

The code (`codeNewP`) and the statics (`staticsNewP`) of the two paths: the prologue's,
`attached_deposit`'s slot (`dslot`), `storage_has_key`'s (`hslot`), `panic_utf8`'s (`panicSlot`),
the two messages and the second `"STATE"` at 1056468.
-/

namespace WNear.Binary.NewBody

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv WNear.Binary.FtTotalSupply
open WNear.Binary.Interface (IfaceMod iface ifaceCode dataWord iface_of_setup)
open WNear.Binary.ReadRegister (ifaceR ifaceR_of_iface iface_of_ifaceR)
open WNear.Binary.SetBlockchainInterface (blockchainInterfaceCells frames)
open WNear.Binary.SetupPanicHook (hookCells)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_word stk_intro)
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.BorshFT (join64' split64' joinB splitB stkJ stkW stkB stkSp stkA)
open WNear.Binary.BorshInt (stk_bytes')
open WNear.Binary.FtTotalSupply (stk4_word)
open WNear.Binary.RegisterLen (frame4)
open WNear.Binary.PanicStr (panicCode panicSlot panicked)
open WNear.Binary.EnvGetters (dslot dCode depLo depHi)
open WNear.Binary.StorageHasKey (hslot hCode)
open WNear.Binary.InitialState (depositMsg initMsg)

/-- The rest of 290's body: `attached_deposit`, the two tests, the success path and the two
panics. -/
def bodyB290 : List Instr :=
  [.local_get 0, .i32_const 8, .i32_binop .add, .call 529,
    .block .empty
      [.block .empty
          [.local_get 0, .load .i64 none { align := 3, offset := 8 },
            .local_get 0, .i32_const 16, .i32_binop .add,
            .load .i64 none { align := 3, offset := 0 }, .i64_binop .or,
            .i64_eqz, .i32_eqz, .br_if 0, .call 552, .br_if 1,
            .local_get 0, .i32_const 24, .i32_binop .add, .call 289,
            .local_get 0, .i32_const 24, .i32_binop .add, .call 220,
            .local_get 0, .i32_const 48, .i32_binop .add, .call 68,
            .local_get 0, .i32_const 64, .i32_binop .add, .global_set 0, .return],
        .i32_const 1050899, .i32_const 33, .call 521, .unreachable],
    .i32_const 1050932, .i32_const 41, .call 521, .unreachable]

theorem f290_body : f290.body = bodyA290 ++ bodyB290 := rfl

theorem entryLocals_f290 : entryLocals f290 [] = #[.i32 0] := rfl

section Res

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The code the two panic paths run (persistent). -/
def codeNewP (e inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n : Nat) (mx : Option Nat) : IProp GF :=
  iprop(codeA inst mi A ∗ ifaceCode e inst mi A n mx ∗ dCode e inst A ∗
    A 444 ↪[wf] FuncInst.wasm types[14]! inst f444 ∗ A 529 ↪[wf] FuncInst.wasm types[0]! inst f529 ∗
    hCode e inst A ∗ A 436 ↪[wf] FuncInst.wasm types[30]! inst f436 ∗
    A 551 ↪[wf] FuncInst.wasm types[13]! inst f551 ∗ A 552 ↪[wf] FuncInst.wasm types[1]! inst f552 ∗
    A 521 ↪[wf] FuncInst.wasm types[14]! inst f521 ∗ A 448 ↪[wf] FuncInst.wasm types[14]! inst f448 ∗
    panicCode e inst mi A)

instance (e inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n : Nat) (mx : Option Nat) :
    Persistent (codeNewP (GF := GF) e inst mi A n mx) := by
  unfold codeNewP; infer_instance

/-- The statics the two panic paths own: the prologue's (as `FtTotalSupply.statics`), the slots
of `attached_deposit`, `storage_has_key` and `panic_utf8`, the two messages and the key `"STATE"`
`state_exists` passes. -/
noncomputable def staticsNewP (n ta : Nat) (A : Nat → Nat) (old k3 : UInt32) : IProp GF :=
  iprop(hookCells n 0 old 0 ∗ n ↦[i32][ 1055020 ] 116 ∗ ta ↦[wt][ 116 ] Ref.func (A 565) ∗
    ta ↦[wt][ 106 ] Ref.func (A 564) ∗ blockchainInterfaceCells n 0 0 0 k3 ∗ vtab n ta A ∗
    dslot n ta A ∗ hslot n ta A ∗ panicSlot n ta A ∗ n ↦[wms][ 1050899 ] depositMsg ∗
    n ↦[wms][ 1050932 ] initMsg ∗ n ↦[wms][ 1056468 ] StateRead.stateKey)

end Res

/-- The cost of the deposit panic, activation excluded. -/
def costDep290 (cfg : WasmConfig) (h : NearState) : Nat :=
  475 * cfg.regularOpCost + 506 * cfg.regularOpCost + attachedDepositUse h + panicUtf8Use h 33

section Dep

variable {GF : BundledGFunctors} [WasmGS NearState GF]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **`new` with a deposit** (290): it traps, the host panicked with "Method new doesn't accept
deposit". -/
theorem body290Dep (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (e inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (mx : Option Nat) (hm : IfaceMod mi A n g ta) (hd : d + 7 < lim.maxCallDepth)
    (Cg R : Nat) (gt : GlobalType) (s : UInt32) (hs : 736 ≤ s.toNat) (hal : s.toNat % 8 = 0)
    (old k3 : UInt32) (h : NearState) (hview : h.context.isView = false)
    (hdep : depLo h ||| depHi h ≠ 0) (hfit : LogFits h 33)
    (hov : h.extCosts.cost "read_memory_byte" * 33 < 2 ^ 64) (Φ : Post NearState GF) :
    codeNewP e inst mi A n mx ∗ credits Cg (costDep290 cfg h + R) ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
      stk n (s.toNat - 736) 736 ∗ staticsNewP n ta A old k3 ∗ mhostPt h ∗
      (panicked Cg h depositMsg -∗ Φ.trap)
      ⊢ mwpi cfg lim d ⟨#[.i32 0], inst, mi⟩ [] f290.body Φ := by
  iintro ⟨#Hk, Hc, Hg, Stk, HS, Hh, W⟩
  iunfold codeNewP at Hk
  icases Hk with ⟨#KA, #HIC, #HD, #F444, #F529, #HHC, #F436, #F551, #F552, #F521, #F448, #HPC⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold panicCode at HPC
    icases HPC with ⟨-, -, #Hi⟩
    iexact Hi
  iunfold staticsNewP at HS
  icases HS with ⟨HH0, Hkey, T116, T106, HBI, HV, DS, HSl, PS, MD, MI, K2⟩
  have hlt := s.toNat_lt
  have hn := hm.mem
  have hg := hm.glob
  have e0 : (s - 64).toNat = s.toNat - 64 := by rw [tsub _ _ (by simp; omega)]; simp
  have e8 : (s - 64 + 8).toNat = s.toNat - 56 := by simp [UInt32.toNat_add, e0]; omega
  have e16 : (s - 64 + 16).toNat = s.toNat - 48 := by simp [UInt32.toNat_add, e0]; omega
  icases stkSp 592 144 rfl $$ Stk with ⟨-, Stk⟩
  icases stkSp 80 64 rfl $$ Stk with ⟨L2, Fr⟩
  icases stkSp 8 56 rfl $$ Fr with ⟨-, Fr⟩
  icases stkSp 8 48 rfl $$ Fr with ⟨O0, Fr⟩
  icases stkSp 8 40 rfl $$ Fr with ⟨O8, -⟩
  icases stk_bytes' $$ O0 with ⟨%ob0, %hob0, O0⟩
  icases stk_bytes' $$ O8 with ⟨%ob8, %hob8, O8⟩
  rw [f290_body]
  iapply segA290 cfg lim d inst mi A n g ta hm (by omega) Cg
    (506 * cfg.regularOpCost + attachedDepositUse h + panicUtf8Use h 33 + R) gt s hs hal old k3
    bodyB290 Φ
  ihave L2 := stkA (b := s.toNat - 144) (by omega) $$ L2
  iframe KA Hg L2 HH0 Hkey T116 T106 HBI HV
  isplitl [Hc]
  · iapply credits_mono (by unfold costDep290; omega) $$ Hc
  iintro Hc Hg L2 HI
  icases iface_of_ifaceR n ta A $$ HI with ⟨HI, -⟩
  icases stkSp 48 32 rfl $$ L2 with ⟨-, L32⟩
  have t0 : types[0]!.params.length = 1 := rfl
  have ha529 := hm.funcs 529 (by decide)
  simp only [bodyB290]
  mstep; mstep; mstep
  mcall (EnvGetters.f529_spec_host cfg lim (d + 1) types[0]! rfl inst mi e A n g ta mx hm (by omega) Cg gt
      (s - 64) (by omega) (by omega) (s - 64 + 8) ob0 ob8 hob0 hob8 h hview) using [Hg HI DS L32 O0 O8 Hh]
  · iunfold EnvGetters.pre529
    ihave L32 := stkA (b := (s - 64).toNat - 32) (by omega) $$ L32
    ihave O0 := memBytes_addr (b := (s - 64 + 8).toNat) (by omega) $$ O0
    ihave O8 := memBytes_addr (b := (s - 64 + 8).toNat + 8) (by omega) $$ O8
    iframe Hg HI DS L32 O0 O8 Hh
    ipureintro; rfl
  iunfold EnvGetters.post529 at HQ
  icases HQ with ⟨%hrs, Hg, HI, DS, L32, O0, O8, Hh⟩
  subst hrs
  ihave O0 := memBytes_addr (b := (s - 64).toNat + 8) (by omega) $$ O0
  ihave O8 := memBytes_addr (b := (s - 64 + 16).toNat + 0) (by omega) $$ O8
  mstep
  mstep
  mstep; mstep [O0] with simp [storeBytes]
  simp only [U128From.decodeLE_storeBytes_i64, UInt64.ofNat_toNat]
  mstep; mstep; mstep; mstep [O8] with simp [storeBytes]
  simp only [U128From.decodeLE_storeBytes_i64, UInt64.ofNat_toNat]
  mstep; mstep; mstep
  have hdep' : (depLo h ||| depHi h == 0) = false := by simpa using hdep
  simp only [hdep']
  mstep
  -- panic_str(1050899, 33)
  icases stkSp 16 16 rfl $$ L32 with ⟨F16, L32⟩
  icases stkSp 8 8 rfl $$ L32 with ⟨-, L32⟩
  icases stkSp 4 4 rfl $$ L32 with ⟨C0, C4⟩
  icases stk4_word $$ C0 with ⟨%c0, C0⟩
  icases stk4_word $$ C4 with ⟨%c4, C4⟩
  have e32 : (s - 64 - 16 - 16).toNat = (s - 64).toNat - 32 := by
    rw [tsub _ _ (by rw [tsub _ _ (by simp [e0]; omega)]; simp [e0]; omega), tsub _ _ (by simp [e0]; omega)]
    simp [e0]; omega
  icases ReadRegister.stk_frame4 n _ (s - 64 - 16 - 16) e32 $$ F16 with ⟨%w0, %w4, %w8, %w12, F16⟩
  have ha521 := hm.funcs 521 (by decide)
  have e80 : (s - 64 - 16).toNat = s.toNat - 80 := by rw [tsub _ _ (by simp [e0]; omega), e0]; simp; omega
  mstep; mstep
  iapply mwpi_cons
  iapply (PanicStr.mwpi_callT' (i := 521) (a := A 521) (type := types[14]!) (inst := inst) (mi := mi)
    (code := f521) [.i32 1050899, .i32 33])
  isplitr
  · iapply (PanicStr.f521_spec cfg lim (d + 1) types[14]! inst mi e A n g ta mx hm (by omega) Cg
      ⟨gt, .i32 (s - 64)⟩ (s - 64) rfl (by omega) (by omega) 1050899 33 depositMsg rfl (by decide)
      InitialState.depositMsg_valid c0 c4 w0 w4 w8 w12 h hfit hov)
    iframe F448 HIC HPC
  isplitr
  · iexact F521
  isplitr
  · iexact Hi
  isplitr
  · ipureintro; exact ⟨rfl, ha521, rfl, by omega⟩
  isplitl [Hc]
  · iexact Hc
  isplitr
  · ipureintro; mstep_norm_full; omega
  isplitl [Hg HI PS C0 C4 F16 MD Hh]
  · iunfold PanicStr.pre
    ihave C0 := memBytes_addr (b := (s - 64 - 16).toNat + 8) (by omega) $$ C0
    ihave C4 := memBytes_addr (b := (s - 64 - 16).toNat + 12) (by omega) $$ C4
    ihave MD := memBytes_addr (a := 1050899) (b := (1050899 : UInt32).toNat) rfl $$ MD
    iframe Hg HI PS C0 C4 F16 MD Hh
    ipureintro; rfl
  inext
  isplit
  · iintro %rs - HF
    iexfalso
    iexact HF
  · iintro HT
    simp only [Post.mseq_trap, Post.mblock]
    iapply W $$ HT

end Dep

/-- What `storage_has_key` keeps of the host. -/
theorem storageHasKeyPost_fields {h h2 : NearState} {key : List UInt8} {st : Near.TrieOverlay.State}
    (hq : StorageHasKeyPost h key st h2) :
    h2.config = h.config ∧ h2.logs = h.logs ∧ h2.extCosts = h.extCosts ∧
      h2.lastExecutionIssue = h.lastExecutionIssue := by
  obtain ⟨s2, -, -, he⟩ := hq
  exact ⟨erase_field he NearState.config fun _ => rfl, erase_field he NearState.logs fun _ => rfl,
    erase_field he NearState.extCosts fun _ => rfl, erase_field he NearState.lastExecutionIssue fun _ => rfl⟩

/-- The cost of the "already initialized" panic, activation excluded. -/
def costInit290 (cfg : WasmConfig) (h : NearState) : Nat :=
  475 * cfg.regularOpCost + 822 * cfg.regularOpCost + attachedDepositUse h +
    storageHasKeyUse h StateRead.stateKey 5 + panicUtf8Use h 41

section Init

variable {GF : BundledGFunctors} [WasmGS NearState GF]

open Near.TrieAccounting Near.TrieConstruction Near.TrieOverlay in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **`new` on an initialized contract, no deposit** (290): `state_exists` is true, it traps,
the host after `storage_has_key` panicked with "The contract has already been initialized". -/
theorem body290Init (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (e inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (mx : Option Nat) (hm : IfaceMod mi A n g ta) (hd : d + 7 < lim.maxCallDepth)
    (Cg R : Nat) (gt : GlobalType) (s : UInt32) (hs : 736 ≤ s.toNat) (hal : s.toNat % 8 = 0)
    (old k3 : UInt32) (h : NearState) (hview : h.context.isView = false)
    (hdep : depLo h ||| depHi h = 0) (v : List UInt8) (hS : h.storage StateRead.stateKey = some v)
    (st : Near.TrieOverlay.State) {b : Nat} (hacc : h.storageAccounting = some st)
    (hlim : withinLimit h.config.maxStorageKeyLen 5 = true)
    (hb : build st.entries = .ok st.base) (hz : zeroHash ∉ st.base.witness.map Prod.fst)
    (hlink : h.storage StateRead.stateKey = viewVal st (contractKey h.context.currentAccountId StateRead.stateKey))
    (hproof : ProofBudget h st b)
    (hbud : lookupProofBound (contractKey h.context.currentAccountId StateRead.stateKey) ≤ b)
    (hfit : LogFits h 41) (hov : h.extCosts.cost "read_memory_byte" * 41 < 2 ^ 64) (Φ : Post NearState GF) :
    codeNewP e inst mi A n mx ∗ credits Cg (costInit290 cfg h + R) ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
      stk n (s.toNat - 736) 736 ∗ staticsNewP n ta A old k3 ∗ mhostPt h ∗
      (∀ h2, ⌜StorageHasKeyPost h StateRead.stateKey st h2⌝ -∗ panicked Cg h2 initMsg -∗ Φ.trap)
      ⊢ mwpi cfg lim d ⟨#[.i32 0], inst, mi⟩ [] f290.body Φ := by
  iintro ⟨#Hk, Hc, Hg, Stk, HS, Hh, W⟩
  iunfold codeNewP at Hk
  icases Hk with ⟨#KA, #HIC, #HD, #F444, #F529, #HHC, #F436, #F551, #F552, #F521, #F448, #HPC⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold panicCode at HPC
    icases HPC with ⟨-, -, #Hi⟩
    iexact Hi
  iunfold staticsNewP at HS
  icases HS with ⟨HH0, Hkey, T116, T106, HBI, HV, DS, HSl, PS, MD, MI, K2⟩
  have hlt := s.toNat_lt
  have hn := hm.mem
  have hg := hm.glob
  have e0 : (s - 64).toNat = s.toNat - 64 := by rw [tsub _ _ (by simp; omega)]; simp
  have e8 : (s - 64 + 8).toNat = s.toNat - 56 := by simp [UInt32.toNat_add, e0]; omega
  have e16 : (s - 64 + 16).toNat = s.toNat - 48 := by simp [UInt32.toNat_add, e0]; omega
  icases stkSp 592 144 rfl $$ Stk with ⟨-, Stk⟩
  icases stkSp 80 64 rfl $$ Stk with ⟨L2, Fr⟩
  icases stkSp 8 56 rfl $$ Fr with ⟨-, Fr⟩
  icases stkSp 8 48 rfl $$ Fr with ⟨O0, Fr⟩
  icases stkSp 8 40 rfl $$ Fr with ⟨O8, -⟩
  icases stk_bytes' $$ O0 with ⟨%ob0, %hob0, O0⟩
  icases stk_bytes' $$ O8 with ⟨%ob8, %hob8, O8⟩
  rw [f290_body]
  iapply segA290 cfg lim d inst mi A n g ta hm (by omega) Cg
    (822 * cfg.regularOpCost + attachedDepositUse h + storageHasKeyUse h StateRead.stateKey 5 +
      panicUtf8Use h 41 + R) gt s hs hal old k3 bodyB290 Φ
  ihave L2 := stkA (b := s.toNat - 144) (by omega) $$ L2
  iframe KA Hg L2 HH0 Hkey T116 T106 HBI HV
  isplitl [Hc]
  · iapply credits_mono (by unfold costInit290; omega) $$ Hc
  iintro Hc Hg L2 HI
  icases iface_of_ifaceR n ta A $$ HI with ⟨HI, -⟩
  icases stkSp 48 32 rfl $$ L2 with ⟨-, L32⟩
  have t0 : types[0]!.params.length = 1 := rfl
  have ha529 := hm.funcs 529 (by decide)
  simp only [bodyB290]
  mstep; mstep; mstep
  mcall (EnvGetters.f529_spec_host cfg lim (d + 1) types[0]! rfl inst mi e A n g ta mx hm (by omega) Cg gt
      (s - 64) (by omega) (by omega) (s - 64 + 8) ob0 ob8 hob0 hob8 h hview) using [Hg HI DS L32 O0 O8 Hh]
  · iunfold EnvGetters.pre529
    ihave L32 := stkA (b := (s - 64).toNat - 32) (by omega) $$ L32
    ihave O0 := memBytes_addr (b := (s - 64 + 8).toNat) (by omega) $$ O0
    ihave O8 := memBytes_addr (b := (s - 64 + 8).toNat + 8) (by omega) $$ O8
    iframe Hg HI DS L32 O0 O8 Hh
    ipureintro; rfl
  iunfold EnvGetters.post529 at HQ
  icases HQ with ⟨%hrs, Hg, HI, DS, L32, O0, O8, Hh⟩
  subst hrs
  ihave O0 := memBytes_addr (b := (s - 64).toNat + 8) (by omega) $$ O0
  ihave O8 := memBytes_addr (b := (s - 64 + 16).toNat + 0) (by omega) $$ O8
  mstep
  mstep
  mstep; mstep [O0] with simp [storeBytes]
  simp only [U128From.decodeLE_storeBytes_i64, UInt64.ofNat_toNat]
  mstep; mstep; mstep; mstep [O8] with simp [storeBytes]
  simp only [U128From.decodeLE_storeBytes_i64, UInt64.ofNat_toNat]
  mstep; mstep; mstep
  rw [hdep]
  mstep
  -- state_exists()
  have t1 : types[1]!.params.length = 0 := rfl
  have ha552 := hm.funcs 552 (by decide)
  mcall (StorageHasKey.f552_spec_host cfg lim (d + 1) types[1]! rfl inst mi e A n g ta mx hm (by omega) Cg gt
      (s - 64) (by omega) (by omega) h st hacc hlim hb hz hlink hproof hbud) using [Hg HI HSl L32 K2 Hh]
  · iunfold StorageHasKey.pre552
    ihave L32 := stkA (b := (s - 64).toNat - 32) (by omega) $$ L32
    iframe Hg HI HSl L32 K2 Hh
    ipureintro; rfl
  iunfold StorageHasKey.post552 at HQ
  icases HQ with ⟨%hrs, Hg, HI, HSl, L32, K2, ⟨%h2, %hq2, Hh⟩⟩
  subst hrs
  rw [hS]
  simp only [StorageRead.foundU64, show UInt64.toUInt32 1 = 1 from rfl]
  mstep
  -- panic_str(1050932, 41)
  obtain ⟨hcfg, hlogs, hext, -⟩ := storageHasKeyPost_fields hq2
  icases stkSp 16 16 rfl $$ L32 with ⟨F16, L32⟩
  icases stkSp 8 8 rfl $$ L32 with ⟨-, L32⟩
  icases stkSp 4 4 rfl $$ L32 with ⟨C0, C4⟩
  icases stk4_word $$ C0 with ⟨%c0, C0⟩
  icases stk4_word $$ C4 with ⟨%c4, C4⟩
  have e32 : (s - 64 - 16 - 16).toNat = (s - 64).toNat - 32 := by
    rw [tsub _ _ (by rw [tsub _ _ (by simp [e0]; omega)]; simp [e0]; omega), tsub _ _ (by simp [e0]; omega)]
    simp [e0]; omega
  icases ReadRegister.stk_frame4 n _ (s - 64 - 16 - 16) e32 $$ F16 with ⟨%w0, %w4, %w8, %w12, F16⟩
  have ha521 := hm.funcs 521 (by decide)
  have e80 : (s - 64 - 16).toNat = s.toNat - 80 := by rw [tsub _ _ (by simp [e0]; omega), e0]; simp; omega
  mstep; mstep
  iapply mwpi_cons
  iapply (PanicStr.mwpi_callT' (i := 521) (a := A 521) (type := types[14]!) (inst := inst) (mi := mi)
    (code := f521) [.i32 1050932, .i32 41])
  isplitr
  · iapply (PanicStr.f521_spec cfg lim (d + 1) types[14]! inst mi e A n g ta mx hm (by omega) Cg
      ⟨gt, .i32 (s - 64)⟩ (s - 64) rfl (by omega) (by omega) 1050932 41 initMsg rfl (by decide)
      InitialState.initMsg_valid c0 c4 w0 w4 w8 w12 h2 (FtTotalSupply.logFits_of hcfg hlogs hfit)
      (by rw [hext]; exact hov))
    iframe F448 HIC HPC
  isplitr
  · iexact F521
  isplitr
  · iexact Hi
  isplitr
  · ipureintro; exact ⟨rfl, ha521, rfl, by omega⟩
  isplitl [Hc]
  · iexact Hc
  isplitr
  · ipureintro; mstep_norm_full; rw [FtTotalSupply.panicUtf8Use_of hext]; omega
  isplitl [Hg HI PS C0 C4 F16 MI Hh]
  · iunfold PanicStr.pre
    ihave C0 := memBytes_addr (b := (s - 64 - 16).toNat + 8) (by omega) $$ C0
    ihave C4 := memBytes_addr (b := (s - 64 - 16).toNat + 12) (by omega) $$ C4
    ihave MI := memBytes_addr (a := 1050932) (b := (1050932 : UInt32).toNat) rfl $$ MI
    iframe Hg HI PS C0 C4 F16 MI Hh
    ipureintro; rfl
  inext
  isplit
  · iintro %rs - HF
    iexfalso
    iexact HF
  · iintro HT
    simp only [Post.mseq_trap, Post.mblock]
    iapply W $$ %h2 %hq2 HT

end Init

end WNear.Binary.NewBody
