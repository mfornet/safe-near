import Bridge.Functions.DepositPost
import Bridge.Functions.FtTotalSupply
import Bridge.Functions.StateWrite
import Bridge.Functions.HookSink

/-!
# `near_deposit` (234): the exported method's body (M8)

```wat
;; 234 near_deposit(): sp0 = sp - 80
522(); 520(1, 1050188)                     setup_panic_hook, set_blockchain_interface
219(sp0 + 40)                              state_read: Some(contract)
155(sp0, sp0 + 40)                         unwrap_or_default: the contract at sp0
232(sp0)                                   near_deposit
220(sp0)                                   state_write
68(sp0 + 24)                               the accounts map's prefix dropped
sp += 80
```

* `segA234`: `FtTotalSupply.segA` on an 80-byte frame, the hook's cells kept (`hookCells … 1 1055136`).
* `body234`: an initialized contract: on `ok` the contract written back (`StorageWritePost` on
  `STATE`), otherwise 232's trap.
-/

namespace WNear.Binary.DepositBody234

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

/-- The prologue, `setup_panic_hook` and `set_blockchain_interface`. -/
def bodyA234 : List Instr :=
  [.global_get 0, .i32_const 80, .i32_binop .sub, .local_tee 0, .global_set 0, .call 522,
    .i32_const 1, .i32_const 1050188, .call 520]

/-- The rest: `state_read`, `unwrap_or_default`, 232, `state_write`, the drop, the epilogue. -/
def bodyB234 : List Instr :=
  [.local_get 0, .i32_const 40, .i32_binop .add, .call 219,
    .local_get 0, .local_get 0, .i32_const 40, .i32_binop .add, .call 155,
    .local_get 0, .call 232, .local_get 0, .call 220,
    .local_get 0, .i32_const 24, .i32_binop .add, .call 68,
    .local_get 0, .i32_const 80, .i32_binop .add, .global_set 0]

theorem f234_body : f234.body = bodyA234 ++ bodyB234 := rfl

section SegA

variable {GF : BundledGFunctors} [WasmGS NearState GF]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- The prologue (`sp0 = s - 80`), `setup_panic_hook` (522) and `set_blockchain_interface(1,
1050188)` (520), in the 80 bytes below `sp0`: the interface installed (`ifaceR`). 475
`regular_op_cost`s. -/
theorem segA234 (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat)
    (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 7 < lim.maxCallDepth) (Cg R : Nat) (gt : GlobalType)
    (s : UInt32) (hs : 736 ≤ s.toNat) (hal : s.toNat % 8 = 0) (old k3 : UInt32) (rest : List Instr)
    (Φ : Post NearState GF) :
    codeA inst mi A ∗ credits Cg (475 * cfg.regularOpCost + R) ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
      stk n (s.toNat - 160) 80 ∗ hookCells n 0 old 0 ∗ n ↦[i32][ 1055020 ] 116 ∗
      ta ↦[wt][ 116 ] Ref.func (A 565) ∗ ta ↦[wt][ 106 ] Ref.func (A 564) ∗
      blockchainInterfaceCells n 0 0 0 k3 ∗ vtab n ta A ∗
      (credits Cg R -∗ g ↦[wg] ⟨gt, .i32 (s - 80)⟩ -∗ stk n (s.toNat - 160) 80 -∗ ifaceR n ta A -∗ hookCells n 0 1 1055136 -∗
        mwpi cfg lim d ⟨#[.i32 (s - 80)], inst, mi⟩ [] rest Φ)
      ⊢ mwpi cfg lim d ⟨#[.i32 0], inst, mi⟩ [] (bodyA234 ++ rest) Φ := by
  iintro ⟨#Hk, Hc, Hg, L2, HH, Hkey, T116, T106, HB, HV, W⟩
  iunfold codeA at Hk
  icases Hk with ⟨#F522, #F503, #F508, #F509, #F822, #F520, #F463, #F565, #F468, #F467, #F564, #F441,
    #F492, #F672, #F464, #F442, #F433, #Hi⟩
  have hn := hm.mem
  have hg := hm.glob
  have hta := hm.table
  have hlt := s.toNat_lt
  have ha522 := hm.funcs 522 (by decide)
  have ha520 := hm.funcs 520 (by decide)
  have t21 : types[21]!.params.length = 0 := rfl
  have t14 : types[14]!.params.length = 2 := rfl
  have e0 : (s - 80).toNat = s.toNat - 80 := by rw [tsub _ _ (by simp; omega)]; simp
  have e1 : (s - 80 - 16).toNat = s.toNat - 96 := by rw [tsub _ _ (by simp [e0]; omega), e0]; simp; omega
  have e2 : (s - 80 - 16 - 16).toNat = s.toNat - 112 := by rw [tsub _ _ (by simp [e1]; omega), e1]; simp; omega
  have e3 : (s - 80 - 32).toNat = s.toNat - 112 := by rw [tsub _ _ (by simp [e0]; omega), e0]; simp; omega
  have e4 : (s - 80 - 32 - 48).toNat = s.toNat - 160 := by rw [tsub _ _ (by simp [e3]; omega), e3]; simp; omega
  icases stkSp 4 76 rfl $$ L2 with ⟨W0, L2⟩
  icases stkSp 4 72 rfl $$ L2 with ⟨W4, L2⟩
  icases stkSp 4 68 rfl $$ L2 with ⟨W8, L2⟩
  icases stkSp 4 64 rfl $$ L2 with ⟨X12, L2⟩
  icases stkSp 4 60 rfl $$ L2 with ⟨W16, L2⟩
  icases stkSp 4 56 rfl $$ L2 with ⟨W20, L2⟩
  icases stkSp 4 52 rfl $$ L2 with ⟨W24, L2⟩
  icases stkSp 4 48 rfl $$ L2 with ⟨W28, L2⟩
  icases stkSp 24 24 rfl $$ L2 with ⟨M32, L2⟩
  icases stkSp 4 20 rfl $$ L2 with ⟨U56, L2⟩
  icases stkSp 4 16 rfl $$ L2 with ⟨U60, L2⟩
  icases stkSp 4 12 rfl $$ L2 with ⟨U64, L2⟩
  icases stkSp 4 8 rfl $$ L2 with ⟨U68, L2⟩
  icases stkSp 4 4 rfl $$ L2 with ⟨U72, U76⟩
  icases stk4_word $$ W0 with ⟨%w0, W0⟩
  icases stk4_word $$ W4 with ⟨%w4, W4⟩
  icases stk4_word $$ W8 with ⟨%w8, W8⟩
  icases stk4_word $$ W16 with ⟨%w16, W16⟩
  icases stk4_word $$ W20 with ⟨%w20, W20⟩
  icases stk4_word $$ W24 with ⟨%w24, W24⟩
  icases stk4_word $$ W28 with ⟨%w28, W28⟩
  icases stk4_word $$ U56 with ⟨%u56, U56⟩
  icases stk4_word $$ U60 with ⟨%u60, U60⟩
  icases stk4_word $$ U64 with ⟨%u64, U64⟩
  icases stk4_word $$ U68 with ⟨%u68, U68⟩
  icases stk4_word $$ U72 with ⟨%u72, U72⟩
  icases stk4_word $$ U76 with ⟨%u76, U76⟩
  iapply mwpi_seq
  simp only [bodyA234]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  -- setup_panic_hook
  mcall (SetupPanicHook.f522_spec cfg lim (d + 1) types[21]! rfl inst mi n g (A 503) (A 508) (A 509) (A 822)
      hn hg (hm.funcs 503 (by decide)) (hm.funcs 508 (by decide)) (hm.funcs 509 (by decide))
      (hm.funcs 822 (by decide)) types[13]! types[31]! types[45]! types[14]! rfl rfl rfl rfl rfl rfl rfl rfl
      (by omega) Cg ⟨gt, .i32 (s - 80)⟩ (s - 80) u72 u76 u56 u60 old rfl (by omega))
    using [Hg U72 U76 U56 U60 HH]
  · iunfold SetupPanicHook.pre
    ihave U72 := memBytes_addr (b := (s - 80 - 16).toNat + 8) (by omega) $$ U72
    ihave U76 := memBytes_addr (b := (s - 80 - 16).toNat + 12) (by omega) $$ U76
    ihave U56 := memBytes_addr (b := (s - 80 - 16 - 16).toNat + 8) (by omega) $$ U56
    ihave U60 := memBytes_addr (b := (s - 80 - 16 - 16).toNat + 12) (by omega) $$ U60
    iframe Hg U72 U76 U56 U60 HH
    ipureintro; rfl
  iunfold SetupPanicHook.post at HQ
  icases HQ with ⟨%hrs, Hg, U72, U76, U56, U60, HH⟩
  subst hrs
  mstep; mstep
  -- set_blockchain_interface(1, 1050188)
  mcall (SetBlockchainInterface.f520_spec cfg lim (d + 1) types[14]! rfl inst mi n g ta (A 564) (A 565)
      (A 467) (A 468) (A 463) (A 441) (A 492) (A 672) (A 464) (A 442) (A 433) hn hg hta
      (hm.funcs 467 (by decide)) (hm.funcs 468 (by decide)) (hm.funcs 463 (by decide))
      (hm.funcs 441 (by decide)) (hm.funcs 492 (by decide)) (hm.funcs 672 (by decide))
      (hm.funcs 464 (by decide)) (hm.funcs 442 (by decide)) (hm.funcs 433 (by decide))
      types[0]! types[1]! types[13]! types[13]! types[31]! types[31]! types[32]! types[13]! types[0]! types[0]!
      types[0]! (by rw [hm.types]) rfl rfl (by rw [hm.types]) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      rfl rfl rfl rfl rfl rfl rfl rfl (by omega) Cg ⟨gt, .i32 (s - 80)⟩ (s - 80) rfl (by omega) (by omega)
      1 1050188 k3 1 0 u64 u68 1 0 w0 w4 w8 w16 w20 w24 w28)
    using [Hg Hkey T116 T106 HB U56 U60 U64 U68 U72 U76 W0 W4 W8 W16 W20 W24 W28]
  · iunfold SetBlockchainInterface.pre, frames
    ihave U56 := memBytes_addr (b := (s - 80 - 32).toNat + 8) (by omega) $$ U56
    ihave U60 := memBytes_addr (b := (s - 80 - 32).toNat + 12) (by omega) $$ U60
    ihave U64 := memBytes_addr (b := (s - 80 - 32).toNat + 16) (by omega) $$ U64
    ihave U68 := memBytes_addr (b := (s - 80 - 32).toNat + 20) (by omega) $$ U68
    ihave U72 := memBytes_addr (b := (s - 80 - 32).toNat + 24) (by omega) $$ U72
    ihave U76 := memBytes_addr (b := (s - 80 - 32).toNat + 28) (by omega) $$ U76
    ihave W0 := memBytes_addr (b := (s - 80 - 32 - 48).toNat) (by omega) $$ W0
    ihave W4 := memBytes_addr (b := (s - 80 - 32 - 48).toNat + 4) (by omega) $$ W4
    ihave W8 := memBytes_addr (b := (s - 80 - 32 - 48).toNat + 8) (by omega) $$ W8
    ihave W16 := memBytes_addr (b := (s - 80 - 32 - 48).toNat + 16) (by omega) $$ W16
    ihave W20 := memBytes_addr (b := (s - 80 - 32 - 48).toNat + 20) (by omega) $$ W20
    ihave W24 := memBytes_addr (b := (s - 80 - 32 - 48).toNat + 24) (by omega) $$ W24
    ihave W28 := memBytes_addr (b := (s - 80 - 32 - 48).toNat + 28) (by omega) $$ W28
    iframe Hg Hkey T116 T106 HB U56 U60 U64 U68 U72 U76 W0 W4 W8 W16 W20 W24 W28
    ipureintro; rfl
  iunfold SetBlockchainInterface.post, frames at HQ
  icases HQ with ⟨%hrs, Hg, Hkey, T116, T106, HB, U56, U60, U64, U68, U72, U76, W0, W4, W8, W16, W20, W24,
    W28⟩
  subst hrs
  iunfold vtab at HV
  icases HV with ⟨V16, T39, V92, T58, V188, T82, V12, T38⟩
  ihave HI := iface_of_setup n ta A $$ [Hkey T116 HB V16 T39 V92 T58 V188 T82]
  · iframe Hkey T116 HB V16 T39 V92 T58 V188 T82
  ihave HI := ifaceR_of_iface n ta A $$ [HI V12 T38]
  · iframe HI V12 T38
  ihave W0 := stkW (b := s.toNat - 160) _ (by omega) $$ W0
  ihave W4 := stkW (b := s.toNat - 160 + 4) _ (by omega) $$ W4
  ihave W8 := stkW (b := s.toNat - 160 + 4 + 4) _ (by omega) $$ W8
  ihave W16 := stkW (b := s.toNat - 160 + 4 + 4 + 4 + 4) _ (by omega) $$ W16
  ihave W20 := stkW (b := s.toNat - 160 + 4 + 4 + 4 + 4 + 4) _ (by omega) $$ W20
  ihave W24 := stkW (b := s.toNat - 160 + 4 + 4 + 4 + 4 + 4 + 4) _ (by omega) $$ W24
  ihave W28 := stkW (b := s.toNat - 160 + 4 + 4 + 4 + 4 + 4 + 4 + 4) _ (by omega) $$ W28
  ihave U56 := stkW (b := s.toNat - 160 + 56) _ (by omega) $$ U56
  ihave U60 := stkW (b := s.toNat - 160 + 60) _ (by omega) $$ U60
  ihave U64 := stkW (b := s.toNat - 160 + 64) _ (by omega) $$ U64
  ihave U68 := stkW (b := s.toNat - 160 + 68) _ (by omega) $$ U68
  ihave U72 := stkW (b := s.toNat - 160 + 72) _ (by omega) $$ U72
  ihave U76 := stkW (b := s.toNat - 160 + 76) _ (by omega) $$ U76
  ihave L := stkJ (a := s.toNat - 160 + 72) (b := s.toNat - 160 + 76) (k1 := 4) (k2 := 4) (k := 8) (by omega) rfl $$ [U72 U76]
  · iframe U72 U76
  ihave L := stkJ (a := s.toNat - 160 + 68) (b := s.toNat - 160 + 72) (k1 := 4) (k2 := 8) (k := 12) (by omega) rfl $$ [U68 L]
  · iframe U68 L
  ihave L := stkJ (a := s.toNat - 160 + 64) (b := s.toNat - 160 + 68) (k1 := 4) (k2 := 12) (k := 16) (by omega) rfl $$ [U64 L]
  · iframe U64 L
  ihave L := stkJ (a := s.toNat - 160 + 60) (b := s.toNat - 160 + 64) (k1 := 4) (k2 := 16) (k := 20) (by omega) rfl $$ [U60 L]
  · iframe U60 L
  ihave L := stkJ (a := s.toNat - 160 + 56) (b := s.toNat - 160 + 60) (k1 := 4) (k2 := 20) (k := 24) (by omega) rfl $$ [U56 L]
  · iframe U56 L
  ihave L := stkJ (a := s.toNat - 160 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4) (b := s.toNat - 160 + 56) (k1 := 24) (k2 := 24) (k := 48) (by omega) rfl $$ [M32 L]
  · iframe M32 L
  ihave L := stkA (b := s.toNat - 160 + 32) (by omega) $$ L
  ihave L := stkJ (a := s.toNat - 160 + 4 + 4 + 4 + 4 + 4 + 4 + 4) (b := s.toNat - 160 + 32) (k1 := 4) (k2 := 48) (k := 52) (by omega) rfl $$ [W28 L]
  · iframe W28 L
  ihave L := stkA (b := s.toNat - 160 + 28) (by omega) $$ L
  ihave L := stkJ (a := s.toNat - 160 + 4 + 4 + 4 + 4 + 4 + 4) (b := s.toNat - 160 + 28) (k1 := 4) (k2 := 52) (k := 56) (by omega) rfl $$ [W24 L]
  · iframe W24 L
  ihave L := stkA (b := s.toNat - 160 + 24) (by omega) $$ L
  ihave L := stkJ (a := s.toNat - 160 + 4 + 4 + 4 + 4 + 4) (b := s.toNat - 160 + 24) (k1 := 4) (k2 := 56) (k := 60) (by omega) rfl $$ [W20 L]
  · iframe W20 L
  ihave L := stkA (b := s.toNat - 160 + 20) (by omega) $$ L
  ihave L := stkJ (a := s.toNat - 160 + 4 + 4 + 4 + 4) (b := s.toNat - 160 + 20) (k1 := 4) (k2 := 60) (k := 64) (by omega) rfl $$ [W16 L]
  · iframe W16 L
  ihave L := stkA (b := s.toNat - 160 + 16) (by omega) $$ L
  ihave L := stkJ (a := s.toNat - 160 + 4 + 4 + 4) (b := s.toNat - 160 + 16) (k1 := 4) (k2 := 64) (k := 68) (by omega) rfl $$ [X12 L]
  · iframe X12 L
  ihave L := stkA (b := s.toNat - 160 + 12) (by omega) $$ L
  ihave L := stkJ (a := s.toNat - 160 + 4 + 4) (b := s.toNat - 160 + 12) (k1 := 4) (k2 := 68) (k := 72) (by omega) rfl $$ [W8 L]
  · iframe W8 L
  ihave L := stkA (b := s.toNat - 160 + 8) (by omega) $$ L
  ihave L := stkJ (a := s.toNat - 160 + 4) (b := s.toNat - 160 + 8) (k1 := 4) (k2 := 72) (k := 76) (by omega) rfl $$ [W4 L]
  · iframe W4 L
  ihave L := stkA (b := s.toNat - 160 + 4) (by omega) $$ L
  ihave L := stkJ (a := s.toNat - 160) (b := s.toNat - 160 + 4) (k1 := 4) (k2 := 76) (k := 80) (by omega) rfl $$ [W0 L]
  · iframe W0 L
  mcredits R
  iapply W $$ Hc Hg L HI HH


end SegA

/-! ## The body on an initialized contract -/

open WNear.Binary.DepositBody
open WNear.Binary.DepositPanicSpec (MFunSpecT_persistent PanicSpecD hookRes)
open WNear.Binary.DepositSeg (LenUp)
open WNear.Binary.DepositTail (logText)
open WNear.Binary.PanicStr (panicked panicSlot)
open WNear.Binary.InternalDepositOverflow (textSupply balMsg)
open WNear.Binary.NewBody (keep Keep)
open WNear.Binary.LookupMapOps (HeapRoomK LenIn)
open WNear.Binary.VecWithCap (okG)
open WNear.Binary.StateReadLen (LenStep postModelL f219_spec_model_len)
open WNear.Binary.StateReadModel (contractBytes)
open WNear.Binary.StateRead (stateCode pre219)
open WNear.Binary.StateWrite (swCode pre220 post220 stateBytes)
open WNear.Binary.StorageWrite (evictedRegister wslot)
open WNear.Binary.StorageBalanceBounds (u128Of)
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.EnvGetters (dslot)
open WNear.Binary.EnvPredecessor (pslot)
open WNear.Binary.StorageHasKey (hslot)
open WNear.Binary.FromUtf8Gen (utf8Width)
open WNear.Binary.InternalDeposit (zeroAt)

/-- The account's storage key for the predecessor of `h`. -/
abbrev keyOf (h : NearState) : List UInt8 :=
  WNear.accountsPrefix ++ (bytes32 (UInt32.ofNat h.context.predecessorAccountId.length) ++ h.context.predecessorAccountId)

/-- `state_write`'s cost, from the host 234 starts on (the free cells at most 18). -/
def cost220B (cfg : WasmConfig) (h : NearState) : Nat :=
  100 * cfg.regularOpCost +
    (70 * cfg.regularOpCost + (35 * cfg.regularOpCost + (203 * cfg.regularOpCost +
      (940 * cfg.regularOpCost + AllocWalk.walkCost cfg 18 + cfg.linearOpBaseCost + cfg.linearOpUnitCost))) +
      (30 * cfg.regularOpCost + (800 * cfg.regularOpCost + BorshSer.cost48 cfg 1))) +
    (51 * cfg.regularOpCost + (257 * cfg.regularOpCost + storageWriteUse h StateRead.stateKey 5 29)) +
    315 * cfg.regularOpCost

/-- The cost of 234's body, activation excluded. -/
noncomputable def cost234 (cfg : WasmConfig) (h : NearState) (S : WNear.State) (reg : Option (UInt64 × UInt64))
    (K879 K664s K664p : Nat → Keep → Nat) : Nat :=
  2400 * cfg.regularOpCost + cost219 cfg h S +
    cost232 cfg 2 1 h (keyOf h) reg (WNear.Borsh.u64 S.accountStorageUsage) (loOf S) (hiOf S) K879 K664s K664p +
    cost220B cfg h

section Body

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The code of 234 (persistent). -/
def code234 (e inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n maxP : Nat) (mx : Option Nat) : IProp GF :=
  iprop(codeA inst mi A ∗ stateCode e inst mi A n maxP mx ∗ A 219 ↪[wf] FuncInst.wasm types[0]! inst f219 ∗
    A 155 ↪[wf] FuncInst.wasm types[14]! inst f155 ∗ A 951 ↪[wf] FuncInst.wasm types[15]! inst f951 ∗
    code232 e n maxP inst mi A mx ∗ A 232 ↪[wf] FuncInst.wasm types[0]! inst f232 ∗
    swCode e n maxP inst mi A mx ∗ A 220 ↪[wf] FuncInst.wasm types[0]! inst f220)

instance (e inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n maxP : Nat) (mx : Option Nat) :
    Persistent (code234 (GF := GF) e inst mi A n maxP mx) := by
  unfold code234; infer_instance

/-- The hook's cells past `hookCells`, and the payloads' `get` slots. -/
def hookX (n ta : Nat) (A : Nat → Nat) (lpc : UInt32) : IProp GF :=
  iprop(n ↦[i32][ 1074936 ] 0 ∗ n ↦[i32][ 1074940 ] lpc ∗ n ↦[i32][ 1055136 + 12 ] 118 ∗
    ta ↦[wt][ 118 ] Ref.func (A 473) ∗ n ↦[i32][ 1062968 + 16 ] 137 ∗ ta ↦[wt][ 137 ] Ref.func (A 679) ∗
    n ↦[i32][ 1066360 + 16 ] 179 ∗ ta ↦[wt][ 179 ] Ref.func (A 826))

/-- The statics 234 starts with. -/
noncomputable def statics234 (n ta : Nat) (A : Nat → Nat) (old k3 lpc : UInt32) (Dp : IProp GF) (aidx : UInt32) (maxP len : Nat) :
    IProp GF :=
  iprop(hookCells n 0 old 0 ∗ n ↦[i32][ 1055020 ] 116 ∗ ta ↦[wt][ 116 ] Ref.func (A 565) ∗
    ta ↦[wt][ 106 ] Ref.func (A 564) ∗ blockchainInterfaceCells n 0 0 0 k3 ∗ vtab n ta A ∗ hookX n ta A lpc ∗
    dslot n ta A ∗ pslot n ta A ∗ hslot n ta A ∗ wslot n ta A ∗ LogStr.lslot n ta A ∗ panicSlot n ta A ∗ Dp ∗
    n ↦[wms][ 1053000 ] balMsg ∗ zeroAt n ∗ DepositTail.tailStat n ta A ∗ n ↦[wms][ 1071704 ] utf8Width ∗
    vt n 1057464 aidx ta (A 578) ∗ heapInv n maxP len [] 1 ∗ n ↦[wms][ 1049788 ] StateRead.stateKey)

theorem sb_u128 (N : Nat) :
    WNear.Borsh.u128 N = storeBytes (.i64 (UInt64.ofNat (Memory.decodeLE ((WNear.Borsh.u128 N).take 8)))) 8 ++
      storeBytes (.i64 (UInt64.ofNat (Memory.decodeLE ((WNear.Borsh.u128 N).drop 8)))) 8 := by
  rw [DepositTail.sb64 _ (by simp [u128_length]), DepositTail.sb64 _ (by simp [u128_length]), List.take_append_drop]

theorem sb_lohi (S : WNear.State) :
    WNear.Borsh.u128 S.totalSupply = storeBytes (.i64 (loOf S)) 8 ++ storeBytes (.i64 (hiOf S)) 8 := by
  unfold loOf hiOf; exact sb_u128 _

open Near.TrieOverlay in
/-- What 234 leaves of the host on `ok`: `state_read` (`h1`), 232 (`h2`), `state_write` (`h3`). -/
def Post234 (e : Nat) (h : NearState) (st : Near.TrieOverlay.State) (bud : Nat) (S : WNear.State)
    (reg : Option (UInt64 × UInt64)) (h3 : NearState) : Prop :=
  ∃ (h1 : NearState) (s1 : Near.TrieOverlay.State) (h2 : NearState) (s2 : Near.TrieOverlay.State) (b0 b1 : List UInt8),
    StorageReadPost h StateRead.stateKey 0 st h1 ∧ h1.storageAccounting = some s1 ∧
    erase h1 = erase (storageReadRegs { h with storageAccounting := some s1 } 0 (h.storage StateRead.stateKey)) ∧
    Post232 e h1 (keyOf h) reg (WNear.Borsh.u64 S.accountStorageUsage) s1
      (bud - readProofCost (contractKey h.context.currentAccountId StateRead.stateKey) (h.storage StateRead.stateKey)) h2 ∧
    h2.storageAccounting = some s2 ∧
    b0 ++ b1 = u128Of ((loOf S).toNat + 2 ^ 64 * (hiOf S).toNat +
      amount232 h1 reg (WNear.Borsh.u64 S.accountStorageUsage)) ∧ b0.length = 8 ∧
    StorageWritePost e h2 StateRead.stateKey
      (stateBytes 1 WNear.accountsPrefix b0 b1 (WNear.Borsh.u64 S.accountStorageUsage)) evictedRegister s2 h3

theorem split8 {n a b : Nat} (bs : List UInt8) (hl : 8 ≤ bs.length) (hb : b = a + 8) :
    (n ↦[wms][ a ] bs : IProp GF) ⊢ n ↦[wms][ a ] (bs.take 8) ∗ n ↦[wms][ b ] (bs.drop 8) := by
  refine (DepositTail.memBytes_eq (List.take_append_drop 8 bs).symm).trans (BorshFT.splitB _ _ ?_)
  simp only [List.length_take]; omega

theorem accountsPrefix_eq : WNear.accountsPrefix = [97] := by decide +kernel

theorem stateKey_ne_key (h : NearState) : StateRead.stateKey ≠ keyOf h := by
  intro he
  have := congrArg List.head? he
  rw [keyOf, accountsPrefix_eq] at this
  simp [StateRead.stateKey] at this

open Near.TrieAccounting Near.TrieConstruction Near.TrieOverlay in
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 64000000 in
/-- **234 on an initialized contract**: the contract read, 232, on `ok` written back. -/
theorem body234 (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (e inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (mx : Option Nat) (hm : IfaceMod mi A n g ta) (D : Nat)
    (hd : d + 31 + D < lim.maxCallDepth)
    (Cg R : Nat) (gt : GlobalType) (s : UInt32) (SP : Nat) (hSP : 400 ≤ SP)
    (hs : 80 + 224 + SP ≤ s.toNat) (hs1 : 736 ≤ s.toNat) (hs2 : s.toNat ≤ 2 ^ 32 - 16) (hal : s.toNat % 8 = 0)
    (old k3 aidx : UInt32) (maxP len : Nat) (hroom : HeapRoomK 25 len maxP)
    (S : WNear.State) (h : NearState) (st : Near.TrieOverlay.State) {bud : Nat}
    (hv : h.storage WNear.stateKey = some (WNear.header S))
    (hview : h.context.isView = false) (hacc : h.storageAccounting = some st) (hcanon : Canon st)
    (hlink : StorageLink h st) (hproof : ProofBudget h st bud)
    (hlim5 : withinLimit h.config.maxStorageKeyLen 5 = true)
    (hreg29 : withinLimit h.config.maxRegisterLen 29 = true)
    (hvlim29 : withinLimit h.config.maxStorageValueLen 29 = true)
    (hvalid : h.config.validAccountId h.context.predecessorAccountId = true)
    (hlimR : withinLimit h.config.maxRegisterLen h.context.predecessorAccountId.length = true)
    (hutf : Utf8.utf8Ok h.context.predecessorAccountId = true)
    (hab : h.context.predecessorAccountId.length ≤ 64) (hab0 : 0 < h.context.predecessorAccountId.length)
    (hlim : withinLimit h.config.maxStorageKeyLen (keyOf h).length = true)
    (hvlim : withinLimit h.config.maxStorageValueLen 16 = true)
    (hreg : withinLimit h.config.maxRegisterLen 16 = true)
    (hbud : (lookupProofBound (contractKey h.context.currentAccountId StateRead.stateKey) + 29) +
      (4 * lookupProofBound (contractKey h.context.currentAccountId (keyOf h)) + 48) +
      (lookupProofBound (contractKey h.context.currentAccountId StateRead.stateKey) + 29) ≤ bud)
    (reg : Option (UInt64 × UInt64))
    (hstore : h.storage (keyOf h) = reg.map fun p => storeBytes (.i64 p.1) 8 ++ storeBytes (.i64 p.2) 8)
    (hlog : ∀ lo hi : UInt64, LogStr.LogOk h (logText lo hi h.context.predecessorAccountId)
      (logText lo hi h.context.predecessorAccountId).length)
    (hfit16 : LogFits h 16) (hov16 : h.extCosts.cost "read_memory_byte" * 16 < 2 ^ 64)
    (hfitS : LogFits h textSupply.length) (hovS : h.extCosts.cost "read_memory_byte" * textSupply.length < 2 ^ 64)
    (hfitT : LogFits h NearDepositPanics.textTooSmall.length)
    (hovT : h.extCosts.cost "read_memory_byte" * NearDepositPanics.textTooSmall.length < 2 ^ 64)
    (hfitP : LogFits h NearDepositPanics.textPositive.length)
    (hovP : h.extCosts.cost "read_memory_byte" * NearDepositPanics.textPositive.length < 2 ^ 64)
    (C : IProp GF) [Persistent C] (lpc : UInt32) (Dp : IProp GF) (K879 K664s K664p : Nat → Keep → Nat)
    (H879 : PanicSpecD cfg lim inst mi C n g ta A gt lpc maxP f879 SP Dp D 1053016 21 1053040 K879 textSupply)
    (H664s : PanicSpecD cfg lim inst mi C n g ta A gt lpc maxP f664 SP Dp D 1050556 21 1050580 K664s
      NearDepositPanics.textTooSmall)
    (H664p : PanicSpecD cfg lim inst mi C n g ta A gt lpc maxP f664 SP Dp D 1050492 34 1050540 K664p
      NearDepositPanics.textPositive)
    (Φ : Post NearState GF) :
    code234 e inst mi A n maxP mx ∗ C ∗ credits Cg (cost234 cfg h S reg K879 K664s K664p + R) ∗
      g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - (304 + SP)) (304 + SP) ∗
      statics234 n ta A old k3 lpc Dp aidx maxP len ∗ mhostPt h ∗
      (∀ h3, ⌜Post234 e h st bud S reg h3 ∧
          case232 h reg (WNear.Borsh.u64 S.accountStorageUsage) ((loOf S).toNat + 2 ^ 64 * (hiOf S).toNat) = .ok⌝ -∗
        credits Cg R -∗ g ↦[wg] ⟨gt, .i32 s⟩ -∗ mhostPt h3 -∗ Φ.normal [] ⟨#[.i32 (s - 80)], inst, mi⟩) ∗
      (∀ hX, ⌜keep hX = keep h ∧
          case232 h reg (WNear.Borsh.u64 S.accountStorageUsage) ((loOf S).toNat + 2 ^ 64 * (hiOf S).toNat) ≠ .ok⌝ -∗
        panicked Cg hX
          (case232 h reg (WNear.Borsh.u64 S.accountStorageUsage) ((loOf S).toNat + 2 ^ 64 * (hiOf S).toNat)).text -∗
        Φ.trap)
      ⊢ mwpi cfg lim d ⟨#[.i32 0], inst, mi⟩ [] f234.body Φ := by
  iintro ⟨#Hk, #HC, Hc, Hg, Stk, HS, Hh, Wok, Wtr⟩
  iunfold code234 at Hk
  icases Hk with ⟨#KA, #HSC, #F219, #F155, #F951, #H232c, #F232, #HSW, #F220⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold codeA at KA
    icases KA with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩
    iexact Hi
  ihave #Hdrop : DropVec.dropCode inst mi A $$ []
  · iunfold swCode at HSW
    icases HSW with ⟨-, #H, -⟩
    iexact H
  ihave #F68 : A 68 ↪[wf] FuncInst.wasm types[0]! inst f68 $$ []
  · iunfold swCode at HSW
    icases HSW with ⟨-, -, -, -, -, -, -, #H⟩
    iexact H
  iunfold statics234 at HS
  icases HS with ⟨HH0, Hkey, T116, T106, HBI, HV, HX, HDs, HPs, HHs, HWs, HLs, HPS, HDp, HM, HZ, HSt, HU8, Hvt,
    Hinv, HSK⟩
  have hn := hm.mem
  have hg := hm.glob
  have hlt := s.toNat_lt
  obtain ⟨r1, r2, r3, r4⟩ := hroom
  have e0 : (s - 80).toNat = s.toNat - 80 := by rw [tsub _ _ (by simp; omega)]; simp
  have a40 : (s - 80 + 40).toNat = s.toNat - 40 := by simp [UInt32.toNat_add, e0]; omega
  have a24 : (s - 80 + 24).toNat = s.toNat - 56 := by simp [UInt32.toNat_add, e0]; omega
  -- the stack: (224 + SP) below sp0, then the frame
  icases stkSp (224 + SP) 80 (by omega) $$ Stk with ⟨Lo, Fr⟩
  icases stkSp 40 40 rfl $$ Fr with ⟨F0, F40⟩
  icases stkSp (224 + SP - 80) 80 (by omega) $$ Lo with ⟨Lo, L2⟩
  iunfold cost234 at Hc
  generalize hK219 : cost219 cfg h S = K219
  generalize hK232 : cost232 cfg 2 1 h (keyOf h) reg (WNear.Borsh.u64 S.accountStorageUsage) (loOf S) (hiOf S)
    K879 K664s K664p = K232
  generalize hK220 : cost220B cfg h = K220
  rw [f234_body]
  iapply segA234 cfg lim d inst mi A n g ta hm (by omega) Cg (1925 * cfg.regularOpCost + K219 + K232 + K220 + R)
    gt s hs1 hal old k3 bodyB234 Φ
  ihave L2 := stkA (b := s.toNat - 160) (by omega) $$ L2
  iframe KA Hg L2 HH0 Hkey T116 T106 HBI HV
  isplitl [Hc]
  · iapply credits_mono (by omega) $$ Hc
  iintro Hc Hg L2 HI HH
  have ha219 := hm.funcs 219 (by decide)
  have ha155 := hm.funcs 155 (by decide)
  have ha232 := hm.funcs 232 (by decide)
  have ha220 := hm.funcs 220 (by decide)
  have ha68 := hm.funcs 68 (by decide)
  have t0 : types[0]!.params.length = 1 := rfl
  have t14 : types[14]!.params.length = 2 := rfl
  simp only [bodyB234]
  -- state_read(sp0 + 40)
  ihave Lo := DepositBody.stkJ2 (s.toNat - (304 + SP)) (by omega) (by omega) $$ Lo L2
  icases stkSp (224 + SP - 592) 592 (by omega) $$ Lo with ⟨Lo, L592⟩
  icases stk_bytes' $$ F40 with ⟨%ob, %hob, F40⟩
  have hR : HeapRoom len maxP := ⟨r1, r2, by omega, by omega⟩
  unfold cost219 at hK219
  mstep; mstep; mstep
  mcall (f219_spec_model_len cfg lim (d + 1) types[0]! rfl inst mi e A n g ta mx hm (by omega) Cg gt
      (s - 80) (s - 80 + 40) (by omega) (by omega) (by omega) aidx maxP len [] ob hob h S hv
      (roomFor_of len maxP len 29 (by decide) hR (by omega) (by omega) r1)
      (by
        intro l hl
        rw [grownLen_small _ _ (by decide)] at hl
        exact roomFor_of len maxP l 1 (by decide) hR (by omega) (by omega) (by omega))
      st hacc hlim5 hcanon.1 hcanon.2 (hlink _) (hproof.mono (by rw [← StateRead.stateKey_eq]; omega)) hreg29)
    using [Hg HI L592 Hvt Hinv F40 HSK Hh]
  · iunfold pre219
    ihave L592 := stkA (b := (s - 80).toNat - 592) (by omega) $$ L592
    ihave F40 := memBytes_addr (b := (s - 80 + 40).toNat) (by omega) $$ F40
    iframe Hg HI L592 Hvt Hinv F40 HSK Hh
    ipureintro; rfl
  iunfold postModelL at HQ
  icases HQ with ⟨%hrs, Hg, HI, L592, Hvt, HSK, ⟨%pv, %p, %pad, %len', %⟨hpad, hstep⟩, Hopt, Hinv, Hp⟩,
    ⟨%h1, %hq1, Hh⟩⟩
  subst hrs
  have hlive : ((p.toNat, 1) :: (pv.toNat, 29) :: ([] : List (Nat × Nat))).erase (pv.toNat, 29) =
      [(p.toNat, 1)] := by simp
  rw [hlive]
  icases AllocZeroed.heapInv_bound n maxP len' _ 2 $$ Hinv with ⟨%⟨hbnd, -⟩, Hinv⟩
  have hpb : p.toNat + 1 ≤ len' := hbnd p.toNat 1 (by simp)
  obtain ⟨hl1, hl2, hl3⟩ := lenStep_bounds len len' r1 hstep
  -- the host after state_read
  obtain ⟨s1, hacc1, hcan1, hlink1, hp1, he1⟩ := StorageReadPost.next hq1 hcanon hlink hproof
    (by rw [← StateRead.stateKey_eq] at hv; rw [hv]; simp [readProofCost, StateReadModel.header_length]; omega)
  have hk1 : keep h1 = keep h := by rw [NewBody.keep_of_erase he1, NewBody.keep_storageReadRegs, NewBody.keep_acc]
  have hst1 : h1.storage = h.storage :=
    (erase_field he1 NearState.storage fun _ => rfl).trans (storageReadRegs_field NearState.storage (fun _ _ _ => rfl) _ _ _)
  have hpred1 : h1.context.predecessorAccountId = h.context.predecessorAccountId :=
    (erase_field he1 (fun y : NearState => y.context.predecessorAccountId) fun _ => rfl).trans
      (storageReadRegs_field (fun y : NearState => y.context.predecessorAccountId) (fun _ _ _ => rfl) _ _ _)
  have hdep1 : h1.context.attachedDeposit = h.context.attachedDeposit :=
    (erase_field he1 (fun y : NearState => y.context.attachedDeposit) fun _ => rfl).trans
      (storageReadRegs_field (fun y : NearState => y.context.attachedDeposit) (fun _ _ _ => rfl) _ _ _)
  have hview1 : h1.context.isView = h.context.isView := congrArg Keep.isView hk1
  have hid1 : h1.context.currentAccountId = h.context.currentAccountId := congrArg Keep.id hk1
  have hcfg1 : h1.config = h.config := congrArg Keep.config hk1
  have hx1 : h1.extCosts = h.extCosts := congrArg Keep.extCosts hk1
  have hlg1 : h1.logs = h.logs := congrArg Keep.logs hk1
  -- unwrap_or_default(sp0, sp0 + 40)
  icases stk_bytes' $$ F0 with ⟨%ob0, %hob0, F0⟩
  have hsb : (contractBytes S p ++ pad).length = 40 := by rw [List.length_append, contractBytes_length, hpad]
  have hniche : ((contractBytes S p ++ pad).drop 24).take 4 = bytes32 p := by
    rw [contractBytes_split]; simp [List.drop_append, List.take_append, u128_length, u64_length]
  ihave Hinv := heapInv_live8 n maxP len' _ 2 $$ Hinv
  icases Hinv with ⟨%h8, Hinv⟩
  have hp8 : 8 ≤ p.toNat := h8 _ 1 (by simp)
  mstep; mstep; mstep; mstep
  mcall (UnwrapOrDefault.f155_spec cfg lim (d + 1) types[14]! rfl inst mi n (A 951) hn (hm.funcs 951 (by decide))
      types[15]! rfl rfl (by omega) Cg (s - 80) (s - 80 + 40) (by omega) (by omega) ob0
      (contractBytes S p ++ pad) hob0 hsb (by rw [hniche, decodeLE_bytes32]; omega))
    using [F0 Hopt]
  · iunfold UnwrapOrDefault.pre
    ihave F0 := memBytes_addr (b := (s - 80).toNat) (by omega) $$ F0
    iframe F0 Hopt
    ipureintro; rfl
  iunfold UnwrapOrDefault.post at HQ
  icases HQ with ⟨%hrs, C0, -⟩
  subst hrs
  -- the token at sp0, as 232 reads it
  rw [contractBytes_split, sb_lohi S] at *
  icases splitB (a := (s - 80).toNat) (b := (s - 80).toNat + 16) (storeBytes (.i64 (loOf S)) 8 ++
    storeBytes (.i64 (hiOf S)) 8) _ (by simp) $$ C0 with ⟨CT, C0⟩
  icases splitB (a := (s - 80).toNat + 16) (b := (s - 80).toNat + 16 + 8) (WNear.Borsh.u64 S.accountStorageUsage) _
    (by rw [u64_length]) $$ C0 with ⟨CX, C0⟩
  ihave C0 := DepositTail.memBytes_eq (bs' := (bytes32 p ++ (bytes32 1 ++ bytes32 1)) ++ pad)
    (by simp [List.append_assoc]) $$ C0
  icases splitB (a := (s - 80).toNat + 16 + 8) (b := (s - 80).toNat + 16 + 8 + 12)
    (bytes32 p ++ (bytes32 1 ++ bytes32 1)) pad (by simp [bytes32]) $$ C0 with ⟨CP, -⟩
  ihave HSC : selfCells n (s - 80) (storeBytes (.i64 (loOf S)) 8 ++ storeBytes (.i64 (hiOf S)) 8)
    (WNear.Borsh.u64 S.accountStorageUsage) p 1 1 WNear.accountsPrefix $$ [CT CX CP Hp]
  · iunfold selfCells, LookupMapLeaves.prefixAt
    iframe CT CX Hp
    iapply memBytes_addr (by simp [UInt32.toNat_add]; omega) $$ CP
  ihave HB : stat232 n ta A lpc Dp aidx $$ [HI HDs HPs HHs HWs HLs HPS HH HX HDp HM HZ HSt HU8 Hvt]
  · iunfold stat232, hookRes, PanicWithHook.hookInstalled
    icases ReadRegister.iface_of_ifaceR n ta A $$ HI with ⟨HI, H12⟩
    iunfold hookX at HX
    icases HX with ⟨X0, X1, X2, X3, X4, X5, X6, X7⟩
    iframe HI H12 HDs HPs HHs HWs HLs HPS HH X0 X1 X2 X3 X4 X5 X6 X7 HDp HM HZ HSt HU8 Hvt
  ihave Lo := DepositBody.stkJ2 (s.toNat - (304 + SP)) (by omega) (by omega) $$ Lo L592
  -- 232(sp0)
  have hv' : h.storage StateRead.stateKey = some (WNear.header S) := by rw [StateRead.stateKey_eq]; exact hv
  have hcase1 : ∀ T, case232 h1 reg (WNear.Borsh.u64 S.accountStorageUsage) T =
      case232 h reg (WNear.Borsh.u64 S.accountStorageUsage) T := by
    intro T; simp only [case232, depOf, EnvGetters.depLo, EnvGetters.depHi, hdep1]
  have hK232' : cost232 cfg 2 1 h1 (WNear.accountsPrefix ++ (bytes32 (UInt32.ofNat h1.context.predecessorAccountId.length) ++
      h1.context.predecessorAccountId)) reg (WNear.Borsh.u64 S.accountStorageUsage) (loOf S) (hiOf S) K879 K664s K664p
      = K232 := by
    rw [cost232_congr cfg 2 1 hk1 hpred1 hdep1 hst1, hpred1]; exact hK232
  have S232 := f232_spec (GF := GF) cfg lim (d + 1) types[0]! rfl e inst mi A n g ta mx hm D (by omega) Cg gt
    (s - 80) (s - 80) SP hSP (by omega) (by omega) (by omega) (by omega) p 1 1 WNear.accountsPrefix
    (by rw [accountsPrefix_eq]; rfl) (by decide) (by decide) (by simp only [UInt32.reduceToNat]; omega)
    (loOf S) (hiOf S) (WNear.Borsh.u64 S.accountStorageUsage) (u64_length _) aidx maxP len' [(p.toNat, 1)] 2
    (by decide) ⟨hl3, by omega, by omega, by omega⟩ h1 s1
    (bud := bud - readProofCost (contractKey h.context.currentAccountId StateRead.stateKey)
      (h.storage StateRead.stateKey))
    (hview1.trans hview) hacc1 hcan1 hlink1 hp1 (by rw [hcfg1, hpred1]; exact hvalid)
    (by rw [hcfg1, hpred1]; exact hlimR) (by rw [hpred1]; exact hutf) (by rw [hpred1]; exact hab)
    (by rw [hpred1]; exact hab0) (by rw [hcfg1, hpred1]; exact hlim) (by rw [hcfg1]; exact hvlim)
    (by rw [hcfg1]; exact hreg)
    (by rw [hid1, hpred1, hv']; simp only [readProofCost, Option.map_some, Option.getD_some, StateReadModel.header_length]
      ; change 4 * lookupProofBound (contractKey h.context.currentAccountId (keyOf h)) + 48 ≤ _; omega)
    reg (by rw [hst1, hpred1]; exact hstore)
    (fun lo hi => by rw [hpred1]; exact WNear.Binary.DepositSeg.LogOk.of_keep hk1 (hlog lo hi))
    (InternalDepositOverflow.LogFits.of_keep hk1 hfit16) (by rw [hx1]; exact hov16)
    (InternalDepositOverflow.LogFits.of_keep hk1 hfitS) (by rw [hx1]; exact hovS)
    (InternalDepositOverflow.LogFits.of_keep hk1 hfitT) (by rw [hx1]; exact hovT)
    (InternalDepositOverflow.LogFits.of_keep hk1 hfitP) (by rw [hx1]; exact hovP)
    C lpc Dp K879 K664s K664p H879 H664s H664p
  ihave #S232' := S232 $$ [H232c HC]
  · iframe H232c HC
  ihave Lo := StateWrite.stkL (a' := (s - 80).toNat - (224 + SP)) (k' := 224 + SP) (by omega) (by omega) $$ Lo
  mstep
  iapply mwpi_cons
  iapply (PanicStr.mwpi_callT' (i := 232) (a := A 232) (type := types[0]!) (inst := inst) (mi := mi)
    (code := f232) [.i32 (s - 80)])
  isplitr
  · iexact S232'
  isplitr
  · iexact F232
  isplitr
  · iexact Hi
  isplitr
  · ipureintro; exact ⟨rfl, ha232, rfl, by omega⟩
  isplitl [Hc]
  · iexact Hc
  isplitr
  · ipureintro; rw [entryLocals_f232, hK232']; mstep_norm_full; omega
  isplitl [Hg Lo HSC HB Hinv Hh]
  · iunfold pre232
    iframe Hg Lo HSC HB Hinv Hh
    ipureintro; rfl
  inext
  isplit
  · iintro %rs Hc HQ
    simp only [Post.mseq_normal]
    iunfold Q232 at HQ
    icases HQ with ⟨%⟨hrs, hok⟩, %hl2, %F2, %h2, %⟨hF2, hup2, hpost2⟩, Hg, Lo, HSC, HB, Hinv, Hh⟩
    subst hrs
    obtain ⟨o1, -, -, o4, s2, hacc2, hcan2, hlink2, hp2⟩ := post232_out hpost2
      (by rw [hid1, hpred1, hv']; simp only [readProofCost, Option.map_some, Option.getD_some, StateReadModel.header_length]
        ; change 4 * lookupProofBound (contractKey h.context.currentAccountId (keyOf h)) + 48 ≤ _; omega)
      (by rw [hst1, hpred1]; exact hstore)
    -- the host after 232
    have hkey : StateRead.stateKey ≠ WNear.accountsPrefix ++
        (bytes32 (UInt32.ofNat h1.context.predecessorAccountId.length) ++ h1.context.predecessorAccountId) := by
      rw [hpred1]; exact stateKey_ne_key h
    have hs2 : h2.storage StateRead.stateKey = some (WNear.header S) := by rw [o1, if_neg hkey, hst1]; exact hv'
    have hid2 : h2.context.currentAccountId = h.context.currentAccountId := (congrArg Keep.id o4).trans hid1
    have hcfg2 : h2.config = h.config := (congrArg Keep.config o4).trans hcfg1
    have hview2 : h2.context.isView = false := (congrArg Keep.isView o4).trans (hview1.trans hview)
    have hc2 : NewBody.SameCost h2 h := NewBody.SameCost.trans (NewBody.sameCost_of_keep o4)
      (NewBody.SameCost.trans (⟨rfl, rfl, rfl⟩ : NewBody.SameCost (LogStr.logged h1 (text232 h1 reg (WNear.Borsh.u64 S.accountStorageUsage))) h1)
        (NewBody.sameCost_of_keep hk1))
    have hW : storageWriteUse h2 WNear.stateKey 5 29 = storageWriteUse h StateRead.stateKey 5 29 := by
      rw [← StateRead.stateKey_eq]; exact NewBody.storageWriteUse_congr hc2 (by rw [hs2, hv']) _ _
    have hbudE := hbud
    simp only [keyOf] at hbudE
    unfold cost220B at hK220
    have hal2 := HookSink.costAllocF_le cfg (le_refl 18) (1024 : UInt32) (by decide)
    have hR2 : HeapRoomK 5 hl2 maxP :=
      DepositSeg.heapRoom_up (k := 21) ⟨hl3, by omega, by omega, by omega⟩ hup2 (by omega)
    rw [entryLocals_f232, hK232']
    ihave Hc : credits _ (500 * cfg.regularOpCost + K220 + R) $$ [Hc]
    · iapply credits_le
      isplitl [Hc]
      · iexact Hc
      · ipureintro; mstep_norm_full; omega
    -- state_write(sp0)
    ihave Hinv := AllocInv.heapInv_mono n maxP hl2 _ F2 18 (by omega) $$ Hinv
    icases stkSp (80 + SP) 144 (by omega) $$ Lo with ⟨Lo, X144⟩
    ihave X144 := stkA (b := (s - 80).toNat - 144) (by omega) $$ X144
    iunfold stat232 at HB
    icases HB with ⟨HI, H12, HDs, HPs, HHs, HWs, HLs, HPS, HH, HDp, HM, HZ, HSt, HU8, Hvt⟩
    iunfold selfCells at HSC
    icases HSC with ⟨CT, CX, CP, Hp⟩
    iunfold LookupMapLeaves.prefixAt at CP
    icases split8 (b := (s - 80).toNat + 8)
      (u128Of ((loOf S).toNat + 2 ^ 64 * (hiOf S).toNat + amount232 h1 reg (WNear.Borsh.u64 S.accountStorageUsage)))
      (by simp) rfl $$ CT with ⟨C0, C8⟩
    ihave Hft : BorshSer.ftAt n (s - 80)
        ((u128Of ((loOf S).toNat + 2 ^ 64 * (hiOf S).toNat + amount232 h1 reg (WNear.Borsh.u64 S.accountStorageUsage))).take 8)
        ((u128Of ((loOf S).toNat + 2 ^ 64 * (hiOf S).toNat + amount232 h1 reg (WNear.Borsh.u64 S.accountStorageUsage))).drop 8)
        (WNear.Borsh.u64 S.accountStorageUsage) p 1 $$ [C0 C8 CX CP]
    · iunfold BorshSer.ftAt
      iframe C0 C8 CX
      iapply memBytes_addr (by simp [UInt32.toNat_add]; omega) $$ CP
    ihave #S220 := StateWrite.f220_spec cfg lim (d + 1) types[0]! rfl inst mi e A n g ta mx hm (by omega) Cg gt
      (s - 80) (s - 80) p 1 aidx maxP hl2 [(p.toNat, 1)] 18 (by decide)
      ((u128Of ((loOf S).toNat + 2 ^ 64 * (hiOf S).toNat + amount232 h1 reg (WNear.Borsh.u64 S.accountStorageUsage))).take 8)
      ((u128Of ((loOf S).toNat + 2 ^ 64 * (hiOf S).toNat + amount232 h1 reg (WNear.Borsh.u64 S.accountStorageUsage))).drop 8)
      (WNear.Borsh.u64 S.accountStorageUsage) WNear.accountsPrefix
      (by omega) (by omega) (by simp) (by simp) (u64_length _) (by rw [accountsPrefix_eq]; rfl) (by decide)
      (by omega) (by simp only [UInt32.reduceToNat]; omega)
      (LookupMapOps.roomFor_ofK (j := 0) 1024 (by decide) hR2 ⟨le_refl _, by omega, hR2.1⟩ (by omega)) h2 s2
      hview2 hacc2 (by rw [hcfg2]; exact hlim5) (by rw [hcfg2]; exact hvlim29)
      hcan2.1 hcan2.2 (hlink2 _) hp2
      (by rw [← StateRead.stateKey_eq, hs2, hid2, hid1, hpred1, hv']
          simp only [writeProofCost, readProofCost, Option.map_some, Option.getD_some, StateReadModel.header_length]
          omega)
      (by intro v hv2; rw [← StateRead.stateKey_eq, hs2] at hv2; cases hv2; rw [hcfg2, StateReadModel.header_length]; exact hreg29) $$ HSW
    ihave HSK : n ↦[wms][ 1049788 ] WNear.stateKey $$ [HSK]
    · rw [← StateRead.stateKey_eq]; iexact HSK
    mstep
    mcall S220 using [Hg X144 HI HWs Hvt Hinv Hft Hp HSK Hh]
      with (mstep_norm_full; (try simp only [UInt32.reduceToNat, Nat.reduceAdd]); omega)
    · iunfold pre220
      iframe Hg X144 HI HWs Hvt Hinv Hft Hp HSK Hh
      ipureintro; rfl
    iunfold post220 at HQ
    icases HQ with ⟨%hrs, Hg, X144, HI, HWs, Hvt, ⟨%len3, %hlen3, Hinv⟩, Hft, Hp, HSK, ⟨%h3, %hq3, Hh⟩⟩
    subst hrs
    -- drop(sp0 + 24): the prefix `Vec` freed
    iunfold BorshSer.ftAt at Hft
    icases Hft with ⟨F0, F8, F16, F24⟩
    ihave F24 := BorshFT.splitB (n := n) (a := (s - 80).toNat + 24) (b := (s - 80).toNat + 24 + 4)
      (bytes32 p) (bytes32 1 ++ bytes32 1) (by simp [bytes32]) $$ F24
    icases F24 with ⟨P0, P48⟩
    ihave P48 := KeyGet.split64 n ((s - 80).toNat + 24 + 4) 1 1 $$ P48
    icases P48 with ⟨P4, P8⟩
    ihave Blk : AllocInv.block n p.toNat 1 $$ [Hp]
    · iunfold AllocInv.block
      iexists WNear.accountsPrefix
      iframe Hp
      ipureintro; rw [accountsPrefix_eq]; rfl
    mstep; mstep; mstep
    mcall (DropVec.f68_spec cfg lim (d + 1) types[0]! rfl inst mi A n g ta hm (by omega) Cg maxP len3
        [(p.toNat, UInt32.toNat 1)] 19 (s - 80 + 24) p 1 1 (by decide) (by omega)) using [P0 P4 P8 Hinv Blk]
    · iunfold DropVec.pre747
      ihave P0 := memBytes_addr (b := (s - 80 + 24).toNat) (by omega) $$ P0
      ihave P4 := memBytes_addr (b := (s - 80 + 24).toNat + 4) (by omega) $$ P4
      ihave P8 := memBytes_addr (b := (s - 80 + 24).toNat + 8) (by omega) $$ P8
      simp only [UInt32.reduceToNat]
      iframe P0 P4 P8 Hinv Blk
      ipureintro; exact List.mem_cons_self
    iunfold DropVec.post747 at HQ
    icases HQ with ⟨%hrs, -, -, -, -⟩
    subst hrs
    -- sp += 80; return
    mstep; mstep; mstep; mstep [Hg]
    rw [show s - 80 + 80 = s by simp]
    mcredits R
    iapply Wok $$ %h3 %⟨⟨h1, s1, h2, s2,
      (u128Of ((loOf S).toNat + 2 ^ 64 * (hiOf S).toNat + amount232 h1 reg (WNear.Borsh.u64 S.accountStorageUsage))).take 8,
      (u128Of ((loOf S).toNat + 2 ^ 64 * (hiOf S).toNat + amount232 h1 reg (WNear.Borsh.u64 S.accountStorageUsage))).drop 8, hq1, hacc1, he1, by rw [hpred1] at hpost2; exact hpost2, hacc2,
      List.take_append_drop _ _, by simp, by rw [StateRead.stateKey_eq]; exact hq3⟩, by rw [← hcase1]; exact hok⟩ Hc Hg Hh
  · iintro HT
    simp only [Post.mseq_trap]
    iunfold T232 at HT
    icases HT with ⟨%hnok, %hX, %hkX, HT⟩
    iapply Wtr $$ %hX %⟨hkX.trans hk1, by rw [← hcase1]; exact hnok⟩
    iapply panicked_conv ?_ $$ HT
    rw [hcase1]

end Body

end WNear.Binary.DepositBody234
