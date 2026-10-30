import Bridge.Functions.StorageBalanceBoundsBody
import Bridge.Functions.MetadataFields

/-!
# The body of `ft_metadata` (function 309)

```wat
;; sp -= 160 (the frame at sp0 = sp - 160, three locals)
setup_panic_hook(); local 1 := 1; set_blockchain_interface(1, 1050188)   ;; bodyA309
state_read(sp0 + 48); unwrap_or_default(sp0 + 8, sp0 + 48)             ;; bodyB309
metadata(sp0 + 48, sp0)                                                ;; 308: the struct at sp0 + 48
Vec::with_capacity(sp0 + 144, 128); [sp0 + 128] := sp0 + 144            ;; 94; the serializer
r := serialize(sp0 + 48, sp0 + 128)                                    ;; 102: the JSON into the Vec
r = 0: [sp0 + 132 .. 144] := [sp0 + 144 .. 156]; local 1 := 0          ;; Ok(vec) at sp0 + 128
[sp0 + 128] := local 1                                                 ;; bodyM309
expect(sp0 + 144, sp0 + 128, 1051320); deref(sp0, sp0 + 144); value_return
drop the Vec, spec, name, symbol (68), icon, reference (147), reference_hash (68 unless None),
the prefix's Vec at sp0 + 32 (68)                                      ;; bodyC309
sp += 160
```

The shape of `storage_balance_bounds` (306, StorageBalanceBoundsBody.lean) with a frame of 160
bytes. Here: the prologue (`segA309`) and the path on an absent `STATE` (`segBNone309`,
`body309None`): `unwrap_or_default` panics before the metadata is built.
-/

namespace WNear.Binary.FtMetadataBody

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv WNear.Binary.FtTotalSupply
open WNear.Binary.Interface (IfaceMod iface ifaceCode dataWord iface_of_setup)
open WNear.Binary.ReadRegister (ifaceR ifaceR_of_iface iface_of_ifaceR)
open WNear.Binary.SetBlockchainInterface (blockchainInterfaceCells frames)
open WNear.Binary.SetupPanicHook (hookCells)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_word stk_intro roomFor grownLen)
open WNear.Binary.AllocNewCell (memBytes_addr cellPages cellPages_toNat cellBytes_toNat)
open WNear.Binary.AllocAlloc (wordsOf)
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.BorshFT (join64' split64' joinB splitB stkJ stkW stkB stkSp stkA)
open WNear.Binary.BorshInt (stk_bytes')
open WNear.Binary.StateRead (stateCode pre219 post219None noneAt)
open WNear.Binary.DropVec (dropCode pre747 post747 f68_spec)
open WNear.Binary.RegisterLen (frame4)
open WNear.Binary.PanicStr (panicCode panicSlot panicked notInit)

/-! ## The body -/

/-- The prologue: the frame, `setup_panic_hook`, `local 1 := 1`, `set_blockchain_interface`. -/
def bodyA309 : List Instr :=
  [.global_get 0, .i32_const 160, .i32_binop .sub, .local_tee 0, .global_set 0, .call 522,
    .i32_const 1, .local_set 1, .i32_const 1, .i32_const 1050188, .call 520]

/-- `state_read` and `unwrap_or_default`. -/
def bodyB309 : List Instr :=
  [.local_get 0, .i32_const 48, .i32_binop .add, .call 219,
    .local_get 0, .i32_const 8, .i32_binop .add, .local_get 0, .i32_const 48, .i32_binop .add, .call 155]

/-- The metadata (308), the `Vec` (94), the serializer, the struct (102), `Ok(vec)` at `sp0 + 128`. -/
def bodyM309 : List Instr :=
  [.local_get 0, .i32_const 48, .i32_binop .add, .local_get 0, .call 308,
    .local_get 0, .i32_const 144, .i32_binop .add, .i32_const 128, .call 94,
    .local_get 0, .local_get 0, .i32_const 144, .i32_binop .add, .store .i32 none { align := 2, offset := 128 },
    .block .empty
      [.block .empty
        [.local_get 0, .i32_const 48, .i32_binop .add, .local_get 0, .i32_const 128, .i32_binop .add, .call 102,
          .local_tee 2, .i32_eqz, .br_if 0,
          .local_get 0, .local_get 2, .store .i32 none { align := 2, offset := 132 },
          .local_get 0, .i32_const 144, .i32_binop .add, .call 68, .br 1],
        .local_get 0, .i32_const 128, .i32_binop .add, .i32_const 4, .i32_binop .or, .local_tee 1,
        .local_get 0, .load .i64 none { align := 3, offset := 144 }, .store .i64 none { align := 2, offset := 0 },
        .local_get 1, .i32_const 8, .i32_binop .add, .local_get 0, .i32_const 144, .i32_binop .add,
        .i32_const 8, .i32_binop .add, .load .i32 none { align := 2, offset := 0 },
        .store .i32 none { align := 2, offset := 0 }, .i32_const 0, .local_set 1],
    .local_get 0, .local_get 1, .store .i32 none { align := 2, offset := 128 }]

/-- `expect`, `deref`, `value_return`, the drops and the epilogue. -/
def bodyC309 : List Instr :=
  [.local_get 0, .i32_const 144, .i32_binop .add, .local_get 0, .i32_const 128, .i32_binop .add,
    .i32_const 1051320, .call 158,
    .local_get 0, .local_get 0, .i32_const 144, .i32_binop .add, .call 779,
    .local_get 0, .load .i32 none { align := 2, offset := 0 }, .local_get 0,
    .load .i32 none { align := 2, offset := 4 }, .call 545,
    .local_get 0, .i32_const 144, .i32_binop .add, .call 68,
    .local_get 0, .i32_const 48, .i32_binop .add, .call 68,
    .local_get 0, .i32_const 60, .i32_binop .add, .call 68,
    .local_get 0, .i32_const 48, .i32_binop .add, .i32_const 24, .i32_binop .add, .call 68,
    .local_get 0, .i32_const 84, .i32_binop .add, .call 147,
    .local_get 0, .i32_const 96, .i32_binop .add, .call 147,
    .block .empty
      [.local_get 0, .load .i32 none { align := 2, offset := 108 }, .i32_eqz, .br_if 0,
        .local_get 0, .i32_const 108, .i32_binop .add, .call 68],
    .local_get 0, .i32_const 8, .i32_binop .add, .i32_const 24, .i32_binop .add, .call 68,
    .local_get 0, .i32_const 160, .i32_binop .add, .global_set 0]

theorem f309_body : f309.body = bodyA309 ++ ((bodyB309 ++ bodyM309) ++ bodyC309) := rfl

theorem entryLocals_f309 : entryLocals f309 [] = #[.i32 0, .i32 0, .i32 0] := rfl

/-! ## Segment A -/

section SegA

variable {GF : BundledGFunctors} [WasmGS NearState GF]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- The prologue (`sp0 = s - 160`), `setup_panic_hook` (522) and `set_blockchain_interface(1,
1050188)` (520), in the 80 bytes below `sp0`: the interface installed (`ifaceR`). 475
`regular_op_cost`s. -/
theorem segA309 (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat)
    (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 7 < lim.maxCallDepth) (Cg R : Nat) (gt : GlobalType)
    (s : UInt32) (hs : 784 ≤ s.toNat) (hal : s.toNat % 8 = 0) (old k3 : UInt32) (rest : List Instr)
    (Φ : Post NearState GF) :
    codeA inst mi A ∗ credits Cg (477 * cfg.regularOpCost + R) ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
      stk n (s.toNat - 240) 80 ∗ hookCells n 0 old 0 ∗ n ↦[i32][ 1055020 ] 116 ∗
      ta ↦[wt][ 116 ] Ref.func (A 565) ∗ ta ↦[wt][ 106 ] Ref.func (A 564) ∗
      blockchainInterfaceCells n 0 0 0 k3 ∗ vtab n ta A ∗
      (credits Cg R -∗ g ↦[wg] ⟨gt, .i32 (s - 160)⟩ -∗ stk n (s.toNat - 240) 80 -∗ ifaceR n ta A -∗
        mwpi cfg lim d ⟨#[.i32 (s - 160), .i32 1, .i32 0], inst, mi⟩ [] rest Φ)
      ⊢ mwpi cfg lim d ⟨#[.i32 0, .i32 0, .i32 0], inst, mi⟩ [] (bodyA309 ++ rest) Φ := by
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
  simp only [bodyA309]
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
  mstep; mstep; mstep; mstep
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

end SegA

/-! ## The code of the path on an absent `STATE` -/

section CodeN

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The code `state_read` and `unwrap_or_default` run (persistent). -/
def codeN309 (e inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n maxP : Nat) : IProp GF :=
  iprop(stateCode e inst mi A n maxP (some maxP) ∗ A 219 ↪[wf] FuncInst.wasm types[0]! inst f219 ∗
    A 155 ↪[wf] FuncInst.wasm types[14]! inst f155 ∗ inst ↪[inst] mi)

instance (e inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n maxP : Nat) :
    Persistent (codeN309 (GF := GF) e inst mi A n maxP) := by
  unfold codeN309; infer_instance

end CodeN

/-! ## On an absent `STATE` -/

section None

variable {GF : BundledGFunctors} [WasmGS NearState GF]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- `FtTotalSupply.segBNone` for the shared prefix `bodyB309` followed by anything: `state_read`
(219) leaves `None`, and `unwrap_or_default` (155) traps through `Contract::default`, the host
after `storage_read` panicked. -/
theorem segBNone309 (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (e inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 18 < lim.maxCallDepth)
    (Cg R : Nat) (gt : GlobalType) (s : UInt32) (hs : 784 ≤ s.toNat) (hal : s.toNat % 8 = 0)
    (idx : UInt32) (maxP len : Nat) (h : NearState) (st : Near.TrieOverlay.State) (hr : ReadNone h st)
    (rest : List Instr) (Φ : Post NearState GF) :
    codeN309 e inst mi A n maxP ∗ ifaceCode e inst mi A n (some maxP) ∗ codeP e inst mi A ∗
      credits Cg (costBNone cfg h + R) ∗ g ↦[wg] ⟨gt, .i32 (s - 160)⟩ ∗ ifaceR n ta A ∗
      stk n (s.toNat - 752) 592 ∗ stk n (s.toNat - 112) 40 ∗ vt n 1057464 idx ta (A 578) ∗
      heapInv n maxP len [] 1 ∗ n ↦[wms][ 1049788 ] StateRead.stateKey ∗ staticsP n ta A ∗ mhostPt h ∗
      (∀ h1, ⌜StorageReadPost h StateRead.stateKey 0 st h1⌝ -∗ panicked Cg h1 notInit -∗ Φ.trap)
      ⊢ mwpi cfg lim d ⟨#[.i32 (s - 160), .i32 1, .i32 0], inst, mi⟩ [] (bodyB309 ++ rest) Φ := by
  iintro ⟨#Hk, #HIC, #HP, Hc, Hg, HI, Lo, F48, Hvt, Hinv, Hkey, HSP, Hh, W⟩
  ihave #Hk' := Hk
  iunfold codeN309 at Hk'
  icases Hk' with ⟨#HSC, #F219, #F155, #Hi⟩
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
  have e0 : (s - 160).toNat = s.toNat - 160 := by rw [tsub _ _ (by simp; omega)]; simp
  have e1 : (s - 160 - 16).toNat = s.toNat - 176 := by rw [tsub _ _ (by simp [e0]; omega), e0]; simp; omega
  have e2 : (s - 160 - 16 - 16).toNat = s.toNat - 192 := by
    rw [tsub _ _ (by simp [e1]; omega), e1]; simp; omega
  have a48 : (s - 160 + 48).toNat = s.toNat - 112 := by simp [UInt32.toNat_add, e0]; omega
  iapply mwpi_seq
  simp only [bodyB309]
  -- state_read(sp0 + 48): None
  icases stk_bytes' $$ F48 with ⟨%ob, %hob, F48⟩
  mstep; mstep; mstep
  have S219 := StateRead.f219_spec_none (GF := GF) cfg lim (d + 1) types[0]! rfl inst mi e A n g ta (some maxP) hm
    (by omega) Cg gt (s - 160) (s - 160 + 48) (by omega) (by omega) (by omega) idx maxP len [] ob hob h hv st hacc
    hlim hb hz hlink hproof
  simp only [StorageReadWrap.costS] at S219
  mcall S219 using [Hg HI Lo Hvt Hinv F48 Hkey Hh]
  · iunfold pre219
    ihave Lo := stkA (b := (s - 160).toNat - 592) (by omega) $$ Lo
    ihave F48 := memBytes_addr (b := (s - 160 + 48).toNat) (by omega) $$ F48
    iframe Hg HI Lo Hvt Hinv F48 Hkey Hh
    ipureintro; rfl
  iunfold post219None at HQ
  icases HQ with ⟨%hrs, Hg, HI, Lo, -, -, Ho, -, ⟨%h1, %hq1, Hh⟩⟩
  subst hrs
  obtain ⟨hcfg, hlogs, hext, -⟩ := storageReadPost_fields hq1
  -- the zero niche at sp0 + 48 + 24
  iunfold noneAt at Ho
  icases splitB (a := (s - 160 + 48).toNat) (b := (s - 160 + 48).toNat + 28) (ob.take 24 ++ [0, 0, 0, 0])
    (ob.drop 28) (by simp [hob]) $$ Ho with ⟨Ho, -⟩
  icases splitB (a := (s - 160 + 48).toNat) (b := (s - 160 + 48).toNat + 24) (ob.take 24) [0, 0, 0, 0]
    (by simp [hob]) $$ Ho with ⟨-, H24⟩
  ihave H24 := (show (n ↦[wms][ (s - 160 + 48).toNat + 24 ] [0, 0, 0, 0] : IProp GF) ⊢
    n ↦[i32][ (s - 160 + 48).toNat + 24 ] 0 by rw [StateRead.bytes32_zero']) $$ H24
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
  -- unwrap_or_default(sp0 + 8, sp0 + 48): a trap
  mstep; mstep; mstep; mstep; mstep; mstep
  iapply mwpi_cons
  iapply (PanicStr.mwpi_callT' (i := 155) (a := A 155) (type := types[14]!) (inst := inst) (mi := mi)
    (code := f155) [.i32 (s - 160 + 8), .i32 (s - 160 + 48)])
  isplitr
  · iapply (UnwrapOrDefault.f155_spec_none cfg lim (d + 1) types[14]! inst mi e A n g ta (some maxP) hm
      (by omega) Cg ⟨gt, .i32 (s - 160)⟩ (s - 160) rfl (by omega) (by omega) (s - 160 + 8) (s - 160 + 48)
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
    ihave C0 := memBytes_addr (b := (s - 160 - 16).toNat + 8) (by omega) $$ C0
    ihave C4 := memBytes_addr (b := (s - 160 - 16).toNat + 12) (by omega) $$ C4
    ihave W0 := memBytes_addr (b := (s - 160 - 16 - 16).toNat) (by omega) $$ W0
    ihave W4 := memBytes_addr (b := (s - 160 - 16 - 16).toNat + 4) (by omega) $$ W4
    ihave W8 := memBytes_addr (b := (s - 160 - 16 - 16).toNat + 8) (by omega) $$ W8
    ihave W12 := memBytes_addr (b := (s - 160 - 16 - 16).toNat + 12) (by omega) $$ W12
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

end None

/-! ## The body on an absent `STATE` -/

/-- The cost of `ft_metadata` on an absent `STATE`, activation excluded: segment A's and
`costBNone`. -/
def cost309None (cfg : WasmConfig) (h : NearState) : Nat :=
  477 * cfg.regularOpCost + costBNone cfg h

section Main

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The code `ft_metadata` runs on an absent `STATE` (persistent). -/
def code309N (e inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n maxP : Nat) : IProp GF :=
  iprop(codeA inst mi A ∗ codeN309 e inst mi A n maxP ∗ ifaceCode e inst mi A n (some maxP))

instance (e inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n maxP : Nat) :
    Persistent (code309N (GF := GF) e inst mi A n maxP) := by
  unfold code309N; infer_instance

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **The body of `ft_metadata` on an uninitialized contract** (309): it traps in
`unwrap_or_default`, the host after `storage_read` panicked with "The contract is not
initialized", at `cost309None`. The statics are `ft_total_supply`'s; 784 bytes of stack. -/
theorem body309None (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (e inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 18 < lim.maxCallDepth)
    (Cg R : Nat) (gt : GlobalType) (s : UInt32) (hs : 784 ≤ s.toNat) (hal : s.toNat % 8 = 0)
    (old k3 idx ptr0 : UInt32) (maxP len : Nat) (h : NearState) (st : Near.TrieOverlay.State)
    (hr : ReadNone h st) (Φ : Post NearState GF) :
    code309N e inst mi A n maxP ∗ codeP e inst mi A ∗ credits Cg (cost309None cfg h + R) ∗
      g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 784) 784 ∗ statics n ta A old k3 idx ptr0 maxP len ∗
      staticsP n ta A ∗ mhostPt h ∗
      (∀ h1, ⌜StorageReadPost h StateRead.stateKey 0 st h1⌝ -∗ panicked Cg h1 notInit -∗ Φ.trap)
      ⊢ mwpi cfg lim d ⟨#[.i32 0, .i32 0, .i32 0], inst, mi⟩ [] f309.body Φ := by
  iintro ⟨#Hk, #HP, Hc, Hg, Stk, HS, HSP, Hh, W⟩
  iunfold code309N at Hk
  icases Hk with ⟨#KA, #KN, #HIC⟩
  iunfold statics at HS
  icases HS with ⟨HH, Hkey, T116, T106, HBI, HV, Hvt, Hinv, HsK, -⟩
  have hlt := s.toNat_lt
  icases stkSp 32 752 rfl $$ Stk with ⟨-, Stk⟩
  icases stkSp 512 240 rfl $$ Stk with ⟨Lo512, Stk⟩
  icases stkSp 80 160 rfl $$ Stk with ⟨L2, Stk⟩
  icases stkSp 48 112 rfl $$ Stk with ⟨-, Stk⟩
  icases stkSp 40 72 rfl $$ Stk with ⟨F48, -⟩
  rw [f309_body]
  iapply segA309 cfg lim d inst mi A n g ta hm (by omega) Cg (costBNone cfg h + R) gt s hs hal old k3
    ((bodyB309 ++ bodyM309) ++ bodyC309) Φ
  ihave L2 := stkA (b := s.toNat - 240) (by omega) $$ L2
  iframe KA Hg L2 HH Hkey T116 T106 HBI HV
  isplitl [Hc]
  · iapply credits_mono (by unfold cost309None; omega) $$ Hc
  iintro Hc Hg L2 HI
  ihave L2 := stkA (b := s.toNat - 784 + 32 + 512) (by omega) $$ L2
  ihave Lo := stkJ (a := s.toNat - 784 + 32) (b := s.toNat - 784 + 32 + 512) (k1 := 512) (k2 := 80) (k := 592)
    rfl rfl $$ [Lo512 L2]
  · iframe Lo512 L2
  ihave Lo := stkA (b := s.toNat - 752) (by omega) $$ Lo
  rw [List.append_assoc]
  iapply segBNone309 cfg lim d e inst mi A n g ta hm hd Cg R gt s hs hal idx maxP len h st hr
    (bodyM309 ++ bodyC309) Φ
  ihave F48 := stkA (b := s.toNat - 112) (by omega) $$ F48
  iframe KN HIC HP Hc Hg HI Lo F48 Hvt Hinv HsK HSP Hh W

end Main

end WNear.Binary.FtMetadataBody
