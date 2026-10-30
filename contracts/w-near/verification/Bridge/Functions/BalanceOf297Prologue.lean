import Bridge.Functions.BalanceOf297InputSetup
import Bridge.Functions.FtTotalSupply

/-! Function 297's initial frame, panic-hook and blockchain-interface setup. -/
namespace WNear.Binary.BalanceOf297AbsentCall
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.Interface (IfaceMod iface ifaceCode dataWord iface_of_setup)
open WNear.Binary.ReadRegister (ifaceR ifaceR_of_iface)
open WNear.Binary.EnvInput (ifaceI)
open WNear.Binary.SetBlockchainInterface (blockchainInterfaceCells frames)
open WNear.Binary.SetupPanicHook (hookCells)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_word stk_intro)
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.BorshFT (stkJ stkW stkSp stkA)
open WNear.Binary.FtTotalSupply (tsub stk4_word vtab codeA)

def body297Prologue : List Instr :=
  [.global_get 0, .i32_const 160, .i32_binop .sub, .local_tee 0, .global_set 0, .call 522,
    .i32_const 1, .i32_const 1050188, .call 520]

theorem body297Prologue_eq : f297.body.take 9 = body297Prologue := by rfl
section Spec
variable {GF : BundledGFunctors} [WasmGS NearState GF]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem prologue297 (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat)
    (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 7 < lim.maxCallDepth) (Cg R : Nat) (gt : GlobalType)
    (s x1 : UInt32) (x2 : UInt64) (x3 : UInt32) (hs : 752 ≤ s.toNat) (hal : s.toNat % 8 = 0) (old k3 : UInt32) (rest : List Instr)
    (Φ : Post NearState GF) :
    codeA inst mi A ∗ credits Cg (475 * cfg.regularOpCost + R) ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
      stk n (s.toNat - 240) 80 ∗ hookCells n 0 old 0 ∗ n ↦[i32][ 1055020 ] 116 ∗
      ta ↦[wt][ 116 ] Ref.func (A 565) ∗ ta ↦[wt][ 106 ] Ref.func (A 564) ∗
      blockchainInterfaceCells n 0 0 0 k3 ∗ vtab n ta A ∗ n ↦[wms][ 1050188 + 36 ] dataWord (1050188 + 36) ∗
      ta ↦[wt][ 44 ] Ref.func (A 246) ∗
      (credits Cg R -∗ g ↦[wg] ⟨gt, .i32 (s - 160)⟩ -∗ stk n (s.toNat - 240) 80 -∗ ifaceI n ta A -∗
        mwpi cfg lim d ⟨#[.i32 (s - 160), .i32 x1, .i64 x2, .i32 x3], inst, mi⟩ [] rest Φ)
      ⊢ mwpi cfg lim d ⟨#[.i32 0, .i32 x1, .i64 x2, .i32 x3], inst, mi⟩ [] (body297Prologue ++ rest) Φ := by
  iintro ⟨#Hk, Hc, Hg, L2, HH, Hkey, T116, T106, HB, HV, V36, T44, W⟩
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
  have e0 : (s - 160).toNat = s.toNat - 160 := by rw [tsub _ _ (by simp; omega)]; simp
  have e1 : (s - 160 - 16).toNat = s.toNat - 176 := by rw [tsub _ _ (by simp [e0]; omega), e0]; simp; omega
  have e2 : (s - 160 - 16 - 16).toNat = s.toNat - 192 := by rw [tsub _ _ (by simp [e1]; omega), e1]; simp; omega
  have e3 : (s - 160 - 32).toNat = s.toNat - 192 := by rw [tsub _ _ (by simp [e0]; omega), e0]; simp; omega
  have e4 : (s - 160 - 32 - 48).toNat = s.toNat - 240 := by rw [tsub _ _ (by simp [e3]; omega), e3]; simp; omega
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
  simp only [body297Prologue]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  -- setup_panic_hook
  mcall (SetupPanicHook.f522_spec cfg lim (d + 1) types[21]! rfl inst mi n g (A 503) (A 508) (A 509) (A 822)
      hn hg (hm.funcs 503 (by decide)) (hm.funcs 508 (by decide)) (hm.funcs 509 (by decide))
      (hm.funcs 822 (by decide)) types[13]! types[31]! types[45]! types[14]! rfl rfl rfl rfl rfl rfl rfl rfl
      (by omega) Cg ⟨gt, .i32 (s - 160)⟩ (s - 160) u72 u76 u56 u60 old rfl (by omega))
    using [Hg U72 U76 U56 U60 HH]
  · iunfold SetupPanicHook.pre
    ihave U72 := memBytes_addr (b := (s - 160 - 16).toNat + 8) (by omega) $$ U72
    ihave U76 := memBytes_addr (b := (s - 160 - 16).toNat + 12) (by omega) $$ U76
    ihave U56 := memBytes_addr (b := (s - 160 - 16 - 16).toNat + 8) (by omega) $$ U56
    ihave U60 := memBytes_addr (b := (s - 160 - 16 - 16).toNat + 12) (by omega) $$ U60
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
      rfl rfl rfl rfl rfl rfl rfl rfl (by omega) Cg ⟨gt, .i32 (s - 160)⟩ (s - 160) rfl (by omega) (by omega)
      1 1050188 k3 1 0 u64 u68 1 0 w0 w4 w8 w16 w20 w24 w28)
    using [Hg Hkey T116 T106 HB U56 U60 U64 U68 U72 U76 W0 W4 W8 W16 W20 W24 W28]
  · iunfold SetBlockchainInterface.pre, frames
    ihave U56 := memBytes_addr (b := (s - 160 - 32).toNat + 8) (by omega) $$ U56
    ihave U60 := memBytes_addr (b := (s - 160 - 32).toNat + 12) (by omega) $$ U60
    ihave U64 := memBytes_addr (b := (s - 160 - 32).toNat + 16) (by omega) $$ U64
    ihave U68 := memBytes_addr (b := (s - 160 - 32).toNat + 20) (by omega) $$ U68
    ihave U72 := memBytes_addr (b := (s - 160 - 32).toNat + 24) (by omega) $$ U72
    ihave U76 := memBytes_addr (b := (s - 160 - 32).toNat + 28) (by omega) $$ U76
    ihave W0 := memBytes_addr (b := (s - 160 - 32 - 48).toNat) (by omega) $$ W0
    ihave W4 := memBytes_addr (b := (s - 160 - 32 - 48).toNat + 4) (by omega) $$ W4
    ihave W8 := memBytes_addr (b := (s - 160 - 32 - 48).toNat + 8) (by omega) $$ W8
    ihave W16 := memBytes_addr (b := (s - 160 - 32 - 48).toNat + 16) (by omega) $$ W16
    ihave W20 := memBytes_addr (b := (s - 160 - 32 - 48).toNat + 20) (by omega) $$ W20
    ihave W24 := memBytes_addr (b := (s - 160 - 32 - 48).toNat + 24) (by omega) $$ W24
    ihave W28 := memBytes_addr (b := (s - 160 - 32 - 48).toNat + 28) (by omega) $$ W28
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
  ihave HI := EnvInput.ifaceI_of_ifaceR n ta A $$ [HI V36 T44]
  · iframe HI V36 T44
  ihave W0 := stkW (b := s.toNat - 240) _ (by omega) $$ W0
  ihave W4 := stkW (b := s.toNat - 240 + 4) _ (by omega) $$ W4
  ihave W8 := stkW (b := s.toNat - 240 + 4 + 4) _ (by omega) $$ W8
  ihave W16 := stkW (b := s.toNat - 240 + 4 + 4 + 4 + 4) _ (by omega) $$ W16
  ihave W20 := stkW (b := s.toNat - 240 + 4 + 4 + 4 + 4 + 4) _ (by omega) $$ W20
  ihave W24 := stkW (b := s.toNat - 240 + 4 + 4 + 4 + 4 + 4 + 4) _ (by omega) $$ W24
  ihave W28 := stkW (b := s.toNat - 240 + 4 + 4 + 4 + 4 + 4 + 4 + 4) _ (by omega) $$ W28
  ihave U56 := stkW (b := s.toNat - 240 + 56) _ (by omega) $$ U56
  ihave U60 := stkW (b := s.toNat - 240 + 60) _ (by omega) $$ U60
  ihave U64 := stkW (b := s.toNat - 240 + 64) _ (by omega) $$ U64
  ihave U68 := stkW (b := s.toNat - 240 + 68) _ (by omega) $$ U68
  ihave U72 := stkW (b := s.toNat - 240 + 72) _ (by omega) $$ U72
  ihave U76 := stkW (b := s.toNat - 240 + 76) _ (by omega) $$ U76
  ihave L := stkJ (a := s.toNat - 240 + 72) (b := s.toNat - 240 + 76) (k1 := 4) (k2 := 4) (k := 8) (by omega) rfl $$ [U72 U76]
  · iframe U72 U76
  ihave L := stkJ (a := s.toNat - 240 + 68) (b := s.toNat - 240 + 72) (k1 := 4) (k2 := 8) (k := 12) (by omega) rfl $$ [U68 L]
  · iframe U68 L
  ihave L := stkJ (a := s.toNat - 240 + 64) (b := s.toNat - 240 + 68) (k1 := 4) (k2 := 12) (k := 16) (by omega) rfl $$ [U64 L]
  · iframe U64 L
  ihave L := stkJ (a := s.toNat - 240 + 60) (b := s.toNat - 240 + 64) (k1 := 4) (k2 := 16) (k := 20) (by omega) rfl $$ [U60 L]
  · iframe U60 L
  ihave L := stkJ (a := s.toNat - 240 + 56) (b := s.toNat - 240 + 60) (k1 := 4) (k2 := 20) (k := 24) (by omega) rfl $$ [U56 L]
  · iframe U56 L
  ihave L := stkJ (a := s.toNat - 240 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4) (b := s.toNat - 240 + 56) (k1 := 24) (k2 := 24) (k := 48) (by omega) rfl $$ [M32 L]
  · iframe M32 L
  ihave L := stkA (b := s.toNat - 240 + 32) (by omega) $$ L
  ihave L := stkJ (a := s.toNat - 240 + 4 + 4 + 4 + 4 + 4 + 4 + 4) (b := s.toNat - 240 + 32) (k1 := 4) (k2 := 48) (k := 52) (by omega) rfl $$ [W28 L]
  · iframe W28 L
  ihave L := stkA (b := s.toNat - 240 + 28) (by omega) $$ L
  ihave L := stkJ (a := s.toNat - 240 + 4 + 4 + 4 + 4 + 4 + 4) (b := s.toNat - 240 + 28) (k1 := 4) (k2 := 52) (k := 56) (by omega) rfl $$ [W24 L]
  · iframe W24 L
  ihave L := stkA (b := s.toNat - 240 + 24) (by omega) $$ L
  ihave L := stkJ (a := s.toNat - 240 + 4 + 4 + 4 + 4 + 4) (b := s.toNat - 240 + 24) (k1 := 4) (k2 := 56) (k := 60) (by omega) rfl $$ [W20 L]
  · iframe W20 L
  ihave L := stkA (b := s.toNat - 240 + 20) (by omega) $$ L
  ihave L := stkJ (a := s.toNat - 240 + 4 + 4 + 4 + 4) (b := s.toNat - 240 + 20) (k1 := 4) (k2 := 60) (k := 64) (by omega) rfl $$ [W16 L]
  · iframe W16 L
  ihave L := stkA (b := s.toNat - 240 + 16) (by omega) $$ L
  ihave L := stkJ (a := s.toNat - 240 + 4 + 4 + 4) (b := s.toNat - 240 + 16) (k1 := 4) (k2 := 64) (k := 68) (by omega) rfl $$ [X12 L]
  · iframe X12 L
  ihave L := stkA (b := s.toNat - 240 + 12) (by omega) $$ L
  ihave L := stkJ (a := s.toNat - 240 + 4 + 4) (b := s.toNat - 240 + 12) (k1 := 4) (k2 := 68) (k := 72) (by omega) rfl $$ [W8 L]
  · iframe W8 L
  ihave L := stkA (b := s.toNat - 240 + 8) (by omega) $$ L
  ihave L := stkJ (a := s.toNat - 240 + 4) (b := s.toNat - 240 + 8) (k1 := 4) (k2 := 72) (k := 76) (by omega) rfl $$ [W4 L]
  · iframe W4 L
  ihave L := stkA (b := s.toNat - 240 + 4) (by omega) $$ L
  ihave L := stkJ (a := s.toNat - 240) (b := s.toNat - 240 + 4) (k1 := 4) (k2 := 76) (k := 80) (by omega) rfl $$ [W0 L]
  · iframe W0 L
  mcredits R
  iapply W $$ Hc Hg L HI

end Spec
end WNear.Binary.BalanceOf297AbsentCall
