import Bridge.Functions.StorageMinimumBalance
import Bridge.Functions.SerdeStruct

/-!
# The body of `storage_balance_bounds` (function 306)

```wat
;; sp -= 128 (the frame at sp0 = sp - 128, three locals)
setup_panic_hook(); local 1 := 1; set_blockchain_interface(1, 1050188)   ;; bodyA306
state_read(sp0 + 56); unwrap_or_default(sp0 + 16, sp0 + 56)            ;; bodyB306
storage_balance_bounds(sp0 + 56, sp0 + 16)                             ;; 418: the bounds at sp0 + 56
Vec::with_capacity(sp0 + 112, 128); [sp0 + 96] := sp0 + 112             ;; 94; the serializer
r := serialize(sp0 + 56, sp0 + 96)                                     ;; 108: the JSON into the Vec
r = 0: [sp0 + 100 .. 112] := [sp0 + 112 .. 124]; local 1 := 0          ;; Ok(vec) at sp0 + 96
[sp0 + 96] := local 1                                                  ;; bodyM306
expect(sp0 + 112, sp0 + 96, 1051200); deref; value_return; drops        ;; bodyC306 loc
sp += 128
```

The segments are `FtTotalSupply.segA` and `U128View.segCG`/`segBNoneG` for this frame (128
bytes, three locals; the result at `sp0 + 96`, the `Vec` at `sp0 + 112`, the prefix at
`sp0 + 40`), and the middle `segM306`: `state_read`, `unwrap_or_default`, the bounds (418), the
`Vec` (94) and the struct serializer (108, `SerdeStruct.f108_bounds`).
-/

namespace WNear.Binary.StorageBalanceBoundsBody

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
open WNear.Binary.StateReadLen (LenStep postModelL f219_spec_model_len)
open WNear.Binary.StateReadModel (contractBytes)
open WNear.Binary.StateRead (stateCode pre219 post219None noneAt)
open WNear.Binary.FmtDigits (decDigits)
open WNear.Binary.FmtU128 (val)
open WNear.Binary.FmtString (kOf)
open WNear.Binary.FmtGrow (newCap)
open WNear.Binary.U128From (u128Bytes)
open WNear.Binary.DropVec (dropCode pre747 post747 f68_spec)
open WNear.Binary.RegisterLen (frame4)
open WNear.Binary.PanicStr (panicCode panicSlot panicked notInit)
open WNear.Binary.U128View (codeBG)
open WNear.Binary.ToString (tsData)

/-! ## The body -/

/-- The prologue: the frame, `setup_panic_hook`, `local 1 := 1`, `set_blockchain_interface`. -/
def bodyA306 : List Instr :=
  [.global_get 0, .i32_const 128, .i32_binop .sub, .local_tee 0, .global_set 0, .call 522,
    .i32_const 1, .local_set 1, .i32_const 1, .i32_const 1050188, .call 520]

/-- `state_read` and `unwrap_or_default`. -/
def bodyB306 : List Instr :=
  [.local_get 0, .i32_const 56, .i32_binop .add, .call 219,
    .local_get 0, .i32_const 16, .i32_binop .add, .local_get 0, .i32_const 56, .i32_binop .add, .call 155]

/-- The bounds (418), the `Vec` (94), the serializer, the struct (108), `Ok(vec)` at `sp0 + 96`. -/
def bodyM306 : List Instr :=
  [.local_get 0, .i32_const 56, .i32_binop .add, .local_get 0, .i32_const 16, .i32_binop .add, .call 418,
    .local_get 0, .i32_const 112, .i32_binop .add, .i32_const 128, .call 94,
    .local_get 0, .local_get 0, .i32_const 112, .i32_binop .add, .store .i32 none { align := 2, offset := 96 },
    .block .empty
      [.block .empty
        [.local_get 0, .i32_const 56, .i32_binop .add, .local_get 0, .i32_const 96, .i32_binop .add, .call 108,
          .local_tee 2, .i32_eqz, .br_if 0,
          .local_get 0, .local_get 2, .store .i32 none { align := 2, offset := 100 },
          .local_get 0, .i32_const 112, .i32_binop .add, .call 68, .br 1],
        .local_get 0, .i32_const 96, .i32_binop .add, .i32_const 4, .i32_binop .or, .local_tee 1,
        .local_get 0, .load .i64 none { align := 3, offset := 112 }, .store .i64 none { align := 2, offset := 0 },
        .local_get 1, .i32_const 8, .i32_binop .add, .local_get 0, .i32_const 112, .i32_binop .add,
        .i32_const 8, .i32_binop .add, .load .i32 none { align := 2, offset := 0 },
        .store .i32 none { align := 2, offset := 0 }, .i32_const 0, .local_set 1],
    .local_get 0, .local_get 1, .store .i32 none { align := 2, offset := 96 }]

/-- `expect`, `deref`, `value_return`, the two drops and the epilogue. -/
def bodyC306 (loc : UInt32) : List Instr :=
  [.local_get 0, .i32_const 112, .i32_binop .add, .local_get 0, .i32_const 96, .i32_binop .add,
    .i32_const loc, .call 158,
    .local_get 0, .i32_const 8, .i32_binop .add, .local_get 0, .i32_const 112, .i32_binop .add, .call 779,
    .local_get 0, .load .i32 none { align := 2, offset := 8 }, .local_get 0,
    .load .i32 none { align := 2, offset := 12 }, .call 545,
    .local_get 0, .i32_const 112, .i32_binop .add, .call 68,
    .local_get 0, .i32_const 40, .i32_binop .add, .call 68,
    .local_get 0, .i32_const 128, .i32_binop .add, .global_set 0]

/-! ## Segment A -/

section SegA

variable {GF : BundledGFunctors} [WasmGS NearState GF]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- The prologue (`sp0 = s - 128`), `setup_panic_hook` (522) and `set_blockchain_interface(1,
1050188)` (520), in the 80 bytes below `sp0`: the interface installed (`ifaceR`). 475
`regular_op_cost`s. -/
theorem segA306 (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat)
    (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 7 < lim.maxCallDepth) (Cg R : Nat) (gt : GlobalType)
    (s : UInt32) (hs : 736 ≤ s.toNat) (hal : s.toNat % 8 = 0) (old k3 : UInt32) (rest : List Instr)
    (Φ : Post NearState GF) :
    codeA inst mi A ∗ credits Cg (477 * cfg.regularOpCost + R) ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
      stk n (s.toNat - 208) 80 ∗ hookCells n 0 old 0 ∗ n ↦[i32][ 1055020 ] 116 ∗
      ta ↦[wt][ 116 ] Ref.func (A 565) ∗ ta ↦[wt][ 106 ] Ref.func (A 564) ∗
      blockchainInterfaceCells n 0 0 0 k3 ∗ vtab n ta A ∗
      (credits Cg R -∗ g ↦[wg] ⟨gt, .i32 (s - 128)⟩ -∗ stk n (s.toNat - 208) 80 -∗ ifaceR n ta A -∗
        mwpi cfg lim d ⟨#[.i32 (s - 128), .i32 1, .i32 0], inst, mi⟩ [] rest Φ)
      ⊢ mwpi cfg lim d ⟨#[.i32 0, .i32 0, .i32 0], inst, mi⟩ [] (bodyA306 ++ rest) Φ := by
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
  have e0 : (s - 128).toNat = s.toNat - 128 := by rw [tsub _ _ (by simp; omega)]; simp
  have e1 : (s - 128 - 16).toNat = s.toNat - 144 := by rw [tsub _ _ (by simp [e0]; omega), e0]; simp; omega
  have e2 : (s - 128 - 16 - 16).toNat = s.toNat - 160 := by rw [tsub _ _ (by simp [e1]; omega), e1]; simp; omega
  have e3 : (s - 128 - 32).toNat = s.toNat - 160 := by rw [tsub _ _ (by simp [e0]; omega), e0]; simp; omega
  have e4 : (s - 128 - 32 - 48).toNat = s.toNat - 208 := by rw [tsub _ _ (by simp [e3]; omega), e3]; simp; omega
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
  simp only [bodyA306]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  -- setup_panic_hook
  mcall (SetupPanicHook.f522_spec cfg lim (d + 1) types[21]! rfl inst mi n g (A 503) (A 508) (A 509) (A 822)
      hn hg (hm.funcs 503 (by decide)) (hm.funcs 508 (by decide)) (hm.funcs 509 (by decide))
      (hm.funcs 822 (by decide)) types[13]! types[31]! types[45]! types[14]! rfl rfl rfl rfl rfl rfl rfl rfl
      (by omega) Cg ⟨gt, .i32 (s - 128)⟩ (s - 128) u72 u76 u56 u60 old rfl (by omega))
    using [Hg U72 U76 U56 U60 HH]
  · iunfold SetupPanicHook.pre
    ihave U72 := memBytes_addr (b := (s - 128 - 16).toNat + 8) (by omega) $$ U72
    ihave U76 := memBytes_addr (b := (s - 128 - 16).toNat + 12) (by omega) $$ U76
    ihave U56 := memBytes_addr (b := (s - 128 - 16 - 16).toNat + 8) (by omega) $$ U56
    ihave U60 := memBytes_addr (b := (s - 128 - 16 - 16).toNat + 12) (by omega) $$ U60
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
      rfl rfl rfl rfl rfl rfl rfl rfl (by omega) Cg ⟨gt, .i32 (s - 128)⟩ (s - 128) rfl (by omega) (by omega)
      1 1050188 k3 1 0 u64 u68 1 0 w0 w4 w8 w16 w20 w24 w28)
    using [Hg Hkey T116 T106 HB U56 U60 U64 U68 U72 U76 W0 W4 W8 W16 W20 W24 W28]
  · iunfold SetBlockchainInterface.pre, frames
    ihave U56 := memBytes_addr (b := (s - 128 - 32).toNat + 8) (by omega) $$ U56
    ihave U60 := memBytes_addr (b := (s - 128 - 32).toNat + 12) (by omega) $$ U60
    ihave U64 := memBytes_addr (b := (s - 128 - 32).toNat + 16) (by omega) $$ U64
    ihave U68 := memBytes_addr (b := (s - 128 - 32).toNat + 20) (by omega) $$ U68
    ihave U72 := memBytes_addr (b := (s - 128 - 32).toNat + 24) (by omega) $$ U72
    ihave U76 := memBytes_addr (b := (s - 128 - 32).toNat + 28) (by omega) $$ U76
    ihave W0 := memBytes_addr (b := (s - 128 - 32 - 48).toNat) (by omega) $$ W0
    ihave W4 := memBytes_addr (b := (s - 128 - 32 - 48).toNat + 4) (by omega) $$ W4
    ihave W8 := memBytes_addr (b := (s - 128 - 32 - 48).toNat + 8) (by omega) $$ W8
    ihave W16 := memBytes_addr (b := (s - 128 - 32 - 48).toNat + 16) (by omega) $$ W16
    ihave W20 := memBytes_addr (b := (s - 128 - 32 - 48).toNat + 20) (by omega) $$ W20
    ihave W24 := memBytes_addr (b := (s - 128 - 32 - 48).toNat + 24) (by omega) $$ W24
    ihave W28 := memBytes_addr (b := (s - 128 - 32 - 48).toNat + 28) (by omega) $$ W28
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
  ihave W0 := stkW (b := s.toNat - 208) _ (by omega) $$ W0
  ihave W4 := stkW (b := s.toNat - 208 + 4) _ (by omega) $$ W4
  ihave W8 := stkW (b := s.toNat - 208 + 4 + 4) _ (by omega) $$ W8
  ihave W16 := stkW (b := s.toNat - 208 + 4 + 4 + 4 + 4) _ (by omega) $$ W16
  ihave W20 := stkW (b := s.toNat - 208 + 4 + 4 + 4 + 4 + 4) _ (by omega) $$ W20
  ihave W24 := stkW (b := s.toNat - 208 + 4 + 4 + 4 + 4 + 4 + 4) _ (by omega) $$ W24
  ihave W28 := stkW (b := s.toNat - 208 + 4 + 4 + 4 + 4 + 4 + 4 + 4) _ (by omega) $$ W28
  ihave U56 := stkW (b := s.toNat - 208 + 56) _ (by omega) $$ U56
  ihave U60 := stkW (b := s.toNat - 208 + 60) _ (by omega) $$ U60
  ihave U64 := stkW (b := s.toNat - 208 + 64) _ (by omega) $$ U64
  ihave U68 := stkW (b := s.toNat - 208 + 68) _ (by omega) $$ U68
  ihave U72 := stkW (b := s.toNat - 208 + 72) _ (by omega) $$ U72
  ihave U76 := stkW (b := s.toNat - 208 + 76) _ (by omega) $$ U76
  ihave L := stkJ (a := s.toNat - 208 + 72) (b := s.toNat - 208 + 76) (k1 := 4) (k2 := 4) (k := 8) (by omega) rfl $$ [U72 U76]
  · iframe U72 U76
  ihave L := stkJ (a := s.toNat - 208 + 68) (b := s.toNat - 208 + 72) (k1 := 4) (k2 := 8) (k := 12) (by omega) rfl $$ [U68 L]
  · iframe U68 L
  ihave L := stkJ (a := s.toNat - 208 + 64) (b := s.toNat - 208 + 68) (k1 := 4) (k2 := 12) (k := 16) (by omega) rfl $$ [U64 L]
  · iframe U64 L
  ihave L := stkJ (a := s.toNat - 208 + 60) (b := s.toNat - 208 + 64) (k1 := 4) (k2 := 16) (k := 20) (by omega) rfl $$ [U60 L]
  · iframe U60 L
  ihave L := stkJ (a := s.toNat - 208 + 56) (b := s.toNat - 208 + 60) (k1 := 4) (k2 := 20) (k := 24) (by omega) rfl $$ [U56 L]
  · iframe U56 L
  ihave L := stkJ (a := s.toNat - 208 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4) (b := s.toNat - 208 + 56) (k1 := 24) (k2 := 24) (k := 48) (by omega) rfl $$ [M32 L]
  · iframe M32 L
  ihave L := stkA (b := s.toNat - 208 + 32) (by omega) $$ L
  ihave L := stkJ (a := s.toNat - 208 + 4 + 4 + 4 + 4 + 4 + 4 + 4) (b := s.toNat - 208 + 32) (k1 := 4) (k2 := 48) (k := 52) (by omega) rfl $$ [W28 L]
  · iframe W28 L
  ihave L := stkA (b := s.toNat - 208 + 28) (by omega) $$ L
  ihave L := stkJ (a := s.toNat - 208 + 4 + 4 + 4 + 4 + 4 + 4) (b := s.toNat - 208 + 28) (k1 := 4) (k2 := 52) (k := 56) (by omega) rfl $$ [W24 L]
  · iframe W24 L
  ihave L := stkA (b := s.toNat - 208 + 24) (by omega) $$ L
  ihave L := stkJ (a := s.toNat - 208 + 4 + 4 + 4 + 4 + 4) (b := s.toNat - 208 + 24) (k1 := 4) (k2 := 56) (k := 60) (by omega) rfl $$ [W20 L]
  · iframe W20 L
  ihave L := stkA (b := s.toNat - 208 + 20) (by omega) $$ L
  ihave L := stkJ (a := s.toNat - 208 + 4 + 4 + 4 + 4) (b := s.toNat - 208 + 20) (k1 := 4) (k2 := 60) (k := 64) (by omega) rfl $$ [W16 L]
  · iframe W16 L
  ihave L := stkA (b := s.toNat - 208 + 16) (by omega) $$ L
  ihave L := stkJ (a := s.toNat - 208 + 4 + 4 + 4) (b := s.toNat - 208 + 16) (k1 := 4) (k2 := 64) (k := 68) (by omega) rfl $$ [X12 L]
  · iframe X12 L
  ihave L := stkA (b := s.toNat - 208 + 12) (by omega) $$ L
  ihave L := stkJ (a := s.toNat - 208 + 4 + 4) (b := s.toNat - 208 + 12) (k1 := 4) (k2 := 68) (k := 72) (by omega) rfl $$ [W8 L]
  · iframe W8 L
  ihave L := stkA (b := s.toNat - 208 + 8) (by omega) $$ L
  ihave L := stkJ (a := s.toNat - 208 + 4) (b := s.toNat - 208 + 8) (k1 := 4) (k2 := 72) (k := 76) (by omega) rfl $$ [W4 L]
  · iframe W4 L
  ihave L := stkA (b := s.toNat - 208 + 4) (by omega) $$ L
  ihave L := stkJ (a := s.toNat - 208) (b := s.toNat - 208 + 4) (k1 := 4) (k2 := 76) (k := 80) (by omega) rfl $$ [W0 L]
  · iframe W0 L
  mcredits R
  iapply W $$ Hc Hg L HI

end SegA

/-! ## The middle segment: the bounds and their JSON -/

/-- Room for six grows of one page under the limit `maxP` (and `2^32`): `state_read`'s two, the
`Vec`'s and the two `to_string`s'. -/
def HeapRoom6 (len maxP : Nat) : Prop :=
  len % 65536 = 0 ∧ 0 < len ∧ len + 5 * 65536 ≤ maxP * 65536 ∧ len + 6 * 65536 ≤ 2 ^ 32

theorem heapRoom_of6 {len maxP : Nat} (h : HeapRoom6 len maxP) : HeapRoom len maxP := by
  obtain ⟨a, b, c, e⟩ := h; exact ⟨a, b, by omega, by omega⟩

theorem roomFor_of6 (len maxP L : Nat) (size : UInt32) (h : size.toNat ≤ 128) (hr : HeapRoom6 len maxP)
    (h1 : len ≤ L) (h2 : L ≤ len + 4 * 65536) (h3 : L % 65536 = 0) : roomFor L maxP size := by
  obtain ⟨r1, r2, r3, r4⟩ := hr
  refine ⟨h3, by omega, ?_, ?_⟩ <;> (rw [cellPages_small size h]; omega)

/-- The bounds `storage_balance_bounds` computes from `S`: `minS S` (the `u64` storage usage times
`10^19`), as the two words of a `u128`. -/
def loN (S : WNear.State) : UInt64 := UInt64.ofNat (StorageMinimumBalance.minS S)
def hiN (S : WNear.State) : UInt64 := UInt64.ofNat (StorageMinimumBalance.minS S / 2 ^ 64)

theorem val_N (S : WNear.State) : val (loN S) (hiN S) = StorageMinimumBalance.minS S := by
  have h := StorageMinimumBalance.minS_lt S
  simp only [val, loN, hiN, UInt64.toNat_ofNat']
  omega

theorem u128Of_N (S : WNear.State) :
    StorageBalanceBounds.u128Of (StorageMinimumBalance.minS S) = u128Bytes (loN S) (hiN S) := rfl

/-- The JSON `storage_balance_bounds` returns on `S`. -/
def boundsJ (S : WNear.State) : List UInt8 :=
  SerdeStruct.boundsJson (StorageMinimumBalance.minS S) (StorageMinimumBalance.minS S)

theorem boundsJ_length (S : WNear.State) : (boundsJ S).length ≤ 97 := by
  have hk := FmtString.kOf_toNat (loN S) (hiN S)
  have hl := kOf_le (val (loN S) (hiN S))
  rw [val_N] at hk hl
  simp only [boundsJ, SerdeStruct.boundsJson, SerdeStruct.jstr, SerdeStruct.keyMin, SerdeStruct.keyMax,
    List.length_append, List.length_cons, List.length_nil]
  omega

section SegM

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The code of the middle segment (persistent). -/
def codeM306 (e inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n maxP : Nat) : IProp GF :=
  iprop(stateCode e inst mi A n maxP (some maxP) ∗ A 219 ↪[wf] FuncInst.wasm types[0]! inst f219 ∗
    A 155 ↪[wf] FuncInst.wasm types[14]! inst f155 ∗ A 951 ↪[wf] FuncInst.wasm types[15]! inst f951 ∗
    A 418 ↪[wf] FuncInst.wasm types[14]! inst f418 ∗ A 553 ↪[wf] FuncInst.wasm types[0]! inst f553 ∗
    A 954 ↪[wf] FuncInst.wasm types[8]! inst f954 ∗ A 566 ↪[wf] FuncInst.wasm types[4]! inst f566 ∗
    VecWithCap.vecCode2 n maxP inst mi A ∗ A 94 ↪[wf] FuncInst.wasm types[14]! inst f94 ∗
    SerdeStruct.structCode n maxP inst mi A ∗ A 108 ↪[wf] FuncInst.wasm types[13]! inst f108 ∗
    inst ↪[inst] mi)

instance (e inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n maxP : Nat) :
    Persistent (codeM306 (GF := GF) e inst mi A n maxP) := by
  unfold codeM306; infer_instance

/-- The cost of `state_read`, `unwrap_or_default`, the bounds, the `Vec` and the JSON. -/
noncomputable def costM306 (cfg : WasmConfig) (h : NearState) (S : WNear.State) : Nat :=
  1500 * cfg.regularOpCost + cost219 cfg h S + StorageBalanceBounds.cost418 cfg +
    VecWithCap.costAllocF cfg 2 128 + SerdeStruct.cost108 cfg 2 (loN S) (hiN S) (loN S) (hiN S)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
open Near.TrieAccounting Near.TrieConstruction Near.TrieOverlay in
/-- The middle segment (`bodyB306 ++ bodyM306`): `state_read` (219) on the model state `S`,
`unwrap_or_default` (155), the bounds (418), `Vec::with_capacity(128)` (94), the serializer
`&mut vec` at `sp0 + 96` and the struct serializer (108, `SerdeStruct.f108_bounds`), the
result `Ok(vec)` at `sp0 + 96`. -/
theorem segM306 (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (e inst : Nat) (mi : ModuleInst) (A : Nat → Nat)
    (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 30 < lim.maxCallDepth)
    (Cg R : Nat) (gt : GlobalType) (s : UInt32) (hs : 736 ≤ s.toNat)
    (hal : s.toNat % 8 = 0) (idx ptr0 : UInt32) (maxP len : Nat) (hroom : HeapRoom6 len maxP)
    (h : NearState) (S : WNear.State)
    (hv : h.storage WNear.stateKey = some (WNear.header S))
    (st : Near.TrieOverlay.State) (hacc : h.storageAccounting = some st)
    (hlim : withinLimit h.config.maxStorageKeyLen 5 = true)
    (hb : build st.entries = .ok st.base) (hz : zeroHash ∉ st.base.witness.map Prod.fst)
    (hlink : h.storage WNear.stateKey = viewVal st (contractKey h.context.currentAccountId WNear.stateKey))
    (hproof : ProofBudget h st (lookupProofBound (contractKey h.context.currentAccountId WNear.stateKey)))
    (hreg : withinLimit h.config.maxRegisterLen 29 = true)
    (rest : List Instr) (Φ : Post NearState GF) :
    codeM306 e inst mi A n maxP ∗ credits Cg (costM306 cfg h S + R) ∗
      g ↦[wg] ⟨gt, .i32 (s - 128)⟩ ∗ ifaceR n ta A ∗ stk n (s.toNat - 720) 592 ∗
      stk n (s.toNat - 112) 40 ∗ stk n (s.toNat - 72) 40 ∗ stk n (s.toNat - 32) 16 ∗ stk n (s.toNat - 16) 12 ∗
      vt n 1057464 idx ta (A 578) ∗ heapInv n maxP len [] 1 ∗ n ↦[wms][ 1049788 ] StateRead.stateKey ∗
      tsData n ta ptr0 (A 759) (A 353) ∗ n ↦[wms][ 1070974 ] FmtDigits.lut ∗ n ↦[wms][ 1051817 ] [34] ∗
      n ↦[wms][ 1061856 ] SerializeStr.esc ∗ SerdeStruct.boundsData n ∗ mhostPt h ∗
      (∀ (q p : UInt32) (rst : List UInt8) (hl F : Nat) (h1 : NearState),
        ⌜StorageReadPost h StateRead.stateKey 0 st h1 ∧ (boundsJ S).length + rst.length = 128⌝ -∗
        credits Cg R -∗ g ↦[wg] ⟨gt, .i32 (s - 128)⟩ -∗ ifaceR n ta A -∗ stk n (s.toNat - 720) 592 -∗
        n ↦[i32][ s.toNat - 32 ] 0 -∗ n ↦[i32][ s.toNat - 28 ] q -∗ n ↦[i32][ s.toNat - 24 ] 128 -∗
        n ↦[i32][ s.toNat - 20 ] UInt32.ofNat (boundsJ S).length -∗ stk n (s.toNat - 16) 12 -∗
        n ↦[i32][ s.toNat - 88 ] p -∗ n ↦[i32][ s.toNat - 84 ] 1 -∗ n ↦[i32][ s.toNat - 80 ] 1 -∗
        n ↦[wms][ q.toNat ] (boundsJ S ++ rst) -∗ n ↦[wms][ p.toNat ] WNear.accountsPrefix -∗
        heapInv n maxP hl [(q.toNat, 128), (p.toNat, 1)] F -∗ mhostPt h1 -∗
        mwpi cfg lim d ⟨#[.i32 (s - 128), .i32 0, .i32 0], inst, mi⟩ [] rest Φ)
      ⊢ mwpi cfg lim d ⟨#[.i32 (s - 128), .i32 1, .i32 0], inst, mi⟩ [] ((bodyB306 ++ bodyM306) ++ rest) Φ := by
  iintro ⟨#Hk, Hc, Hg, HI, Lo, F16, F56, F96, F112, Hvt, Hinv, Hkey, HT, Hlut, Hq, He, HB, Hh, W⟩
  ihave #Hk' := Hk
  iunfold codeM306 at Hk'
  icases Hk' with ⟨#HSC, #F219, #F155, #F951, #F418, #F553, #F954, #F566, #HV2, #F94, #HSt, #F108, #Hi⟩
  unfold costM306 cost219
  have hn := hm.mem
  have hg := hm.glob
  have ha219 := hm.funcs 219 (by decide)
  have ha155 := hm.funcs 155 (by decide)
  have ha418 := hm.funcs 418 (by decide)
  have ha94 := hm.funcs 94 (by decide)
  have ha108 := hm.funcs 108 (by decide)
  have t0 : types[0]!.params.length = 1 := rfl
  have t14 : types[14]!.params.length = 2 := rfl
  have t13 : types[13]!.params.length = 2 := rfl
  have hlt := s.toNat_lt
  have hr4 := heapRoom_of6 hroom
  obtain ⟨r1, r2, r3, r4⟩ := hroom
  have e0 : (s - 128).toNat = s.toNat - 128 := by rw [tsub _ _ (by simp; omega)]; simp
  have a56 : (s - 128 + 56).toNat = s.toNat - 72 := by simp [UInt32.toNat_add, e0]; omega
  have a16 : (s - 128 + 16).toNat = s.toNat - 112 := by simp [UInt32.toNat_add, e0]; omega
  have a96 : (s - 128 + 96).toNat = s.toNat - 32 := by simp [UInt32.toNat_add, e0]; omega
  have a112 : (s - 128 + 112).toNat = s.toNat - 16 := by simp [UInt32.toNat_add, e0]; omega
  iapply mwpi_seq
  simp only [bodyB306, bodyM306, List.cons_append, List.nil_append]
  -- state_read(sp0 + 56)
  icases stk_bytes' $$ F56 with ⟨%ob, %hob, F56⟩
  mstep; mstep; mstep
  mcall (f219_spec_model_len cfg lim (d + 1) types[0]! rfl inst mi e A n g ta (some maxP) hm (by omega) Cg gt
      (s - 128) (s - 128 + 56) (by omega) (by omega) (by omega) idx maxP len [] ob hob h S hv
      (roomFor_of len maxP len 29 (by decide) hr4 (by omega) (by omega) r1)
      (by
        intro l hl
        rw [grownLen_small _ _ (by decide)] at hl
        exact roomFor_of len maxP l 1 (by decide) hr4 (by omega) (by omega) (by omega))
      st hacc hlim hb hz hlink hproof hreg)
    using [Hg HI Lo Hvt Hinv F56 Hkey Hh]
  · iunfold pre219
    ihave Lo := stkA (b := (s - 128).toNat - 592) (by omega) $$ Lo
    ihave F56 := memBytes_addr (b := (s - 128 + 56).toNat) (by omega) $$ F56
    iframe Hg HI Lo Hvt Hinv F56 Hkey Hh
    ipureintro; rfl
  iunfold postModelL at HQ
  icases HQ with ⟨%hrs, Hg, HI, Lo, Hvt, Hkey, ⟨%pv, %p, %pad, %len', %⟨hpad, hstep⟩, Hopt, Hinv, Hp⟩,
    ⟨%h1, %hq1, Hh⟩⟩
  subst hrs
  have hlive : ((p.toNat, 1) :: (pv.toNat, 29) :: ([] : List (Nat × Nat))).erase (pv.toNat, 29) =
      [(p.toNat, 1)] := by simp
  rw [hlive]
  ihave Hinv := heapInv_live8 n maxP len' _ 2 $$ Hinv
  icases Hinv with ⟨%h8, Hinv⟩
  have hp8 : 8 ≤ p.toNat := h8 _ 1 (by simp)
  obtain ⟨hl1, hl2, hl3⟩ := lenStep_bounds len len' r1 hstep
  -- unwrap_or_default(sp0 + 16, sp0 + 56)
  icases stk_bytes' $$ F16 with ⟨%ob16, %hob16, F16⟩
  have hsb : (contractBytes S p ++ pad).length = 40 := by rw [List.length_append, contractBytes_length, hpad]
  have hniche : ((contractBytes S p ++ pad).drop 24).take 4 = bytes32 p := by
    rw [contractBytes_split]; simp [List.drop_append, List.take_append, u128_length, u64_length]
  mstep; mstep; mstep; mstep; mstep; mstep
  mcall (UnwrapOrDefault.f155_spec cfg lim (d + 1) types[14]! rfl inst mi n (A 951) hn (hm.funcs 951 (by decide))
      types[15]! rfl rfl (by omega) Cg (s - 128 + 16) (s - 128 + 56) (by omega) (by omega) ob16
      (contractBytes S p ++ pad) hob16 hsb (by rw [hniche, decodeLE_bytes32]; omega))
    using [F16 Hopt]
  · iunfold UnwrapOrDefault.pre
    ihave F16 := memBytes_addr (b := (s - 128 + 16).toNat) (by omega) $$ F16
    iframe F16 Hopt
    ipureintro; rfl
  iunfold UnwrapOrDefault.post at HQ
  icases HQ with ⟨%hrs, C16, Hopt⟩
  subst hrs
  -- storage_balance_bounds(sp0 + 56, sp0 + 16)
  rw [contractBytes_split]
  ihave C16 := memBytes_addr (b := s.toNat - 112) (by omega) $$ C16
  icases splitB (a := s.toNat - 112) (b := s.toNat - 96) (WNear.Borsh.u128 S.totalSupply) _
    (by rw [u128_length]; omega) $$ C16 with ⟨C0, C16⟩
  icases splitB (a := s.toNat - 96) (b := s.toNat - 88) (WNear.Borsh.u64 S.accountStorageUsage) _
    (by rw [u64_length]; omega) $$ C16 with ⟨Cx, C24⟩
  icases stkSp 512 80 rfl $$ Lo with ⟨Lo512, L80⟩
  mstep; mstep; mstep; mstep; mstep; mstep
  mcall (StorageBalanceBounds.f418_spec cfg lim (d + 1) types[14]! rfl inst mi n g (A 553) (A 954) (A 566) hn hg
      (hm.funcs 553 (by decide)) (hm.funcs 954 (by decide)) (hm.funcs 566 (by decide)) (by omega) Cg gt (s - 128)
      (s - 128 + 56) (s - 128 + 16) (by omega) (by omega)
      (WNear.Borsh.u128 S.totalSupply ++ (WNear.Borsh.u64 S.accountStorageUsage ++ (bytes32 p ++ (bytes32 1 ++ (bytes32 1 ++ pad)))))
      (WNear.Borsh.u64 S.accountStorageUsage) (by rw [← contractBytes_split]; exact hsb) (u64_length _))
    using [Hg L80 Hopt Cx]
  · iunfold StorageBalanceBounds.pre418
    ihave L80 := stkA (b := (s - 128).toNat - 80) (by omega) $$ L80
    ihave Hopt := memBytes_addr (b := (s - 128 + 56).toNat) (by omega) $$ Hopt
    ihave Cx := memBytes_addr (b := (s - 128 + 16).toNat + 16) (by omega) $$ Cx
    iframe Hg L80 Hopt Cx
    ipureintro; rfl
  iunfold StorageBalanceBounds.post418 at HQ
  icases HQ with ⟨%hrs, Hg, L80, Hbd, Cx⟩
  subst hrs
  have hN : (StorageBalanceBounds.xOf (WNear.Borsh.u64 S.accountStorageUsage)).toNat * 10000000000000000000 =
      StorageMinimumBalance.minS S := by
    rw [StorageBalanceBounds.xOf, WNear.Borsh.u64, decodeLE_leBytes, StorageMinimumBalance.minS]
    simp only [UInt64.toNat_ofNat']
    norm_num
  rw [hN]
  -- Vec::with_capacity(sp0 + 112, 128)
  icases stk_bytes' $$ F112 with ⟨%ob12, %hob12, F112⟩
  mstep; mstep; mstep; mstep
  mcall (SerdeLeaves.f94_spec cfg lim (d + 1) types[14]! rfl inst mi A n g ta hm (by omega) Cg gt (s - 128)
      (s - 128 + 112) 128 idx maxP len' [(p.toNat, 1)] ob12 hob12 (by omega) (by decide)
      (fun _ => roomFor_of6 len maxP len' 128 (by decide) ⟨r1, r2, r3, r4⟩ hl1 (by omega) hl3) (F := 2)
      (hF := by decide))
    using [Hg L80 Hvt Hinv F112]
  · iunfold VecWithCap.pre373
    ihave F112 := memBytes_addr (b := (s - 128 + 112).toNat) (by omega) $$ F112
    iframe Hg L80 Hvt Hinv F112
    ipureintro; rfl
  iunfold VecWithCap.post373 at HQ
  icases HQ with ⟨%hrs, %q, Hg, L80, Hvt, V0, V4, V8, Ha⟩
  subst hrs
  icases FmtSink.heapAfter_grown (by simp) $$ Ha with ⟨%⟨hq0, hqb⟩, Hblk, Hgr⟩
  iunfold FmtSink.grown at Hgr
  icases Hgr with ⟨%hl1, %hhl1, Hinv⟩
  rw [grownLen_small _ _ (by decide)] at hhl1
  iunfold block at Hblk
  icases Hblk with ⟨%bs, %hbs, Hqb⟩
  have h128 : (128 : UInt32).toNat = 128 := rfl
  rw [h128] at hbs hqb
  rw [h128]
  have hl1' : len' ≤ hl1 ∧ hl1 ≤ len' + 65536 ∧ hl1 % 65536 = 0 := by omega
  -- the serializer: [sp0 + 96] := sp0 + 112
  icases stkSp 4 12 rfl $$ F96 with ⟨W96, F96⟩
  icases stkSp 8 4 rfl $$ F96 with ⟨Q100, L108⟩
  icases stk_bytes' $$ W96 with ⟨%w96, %hw96, W96⟩
  ihave W96 := memBytes_addr (b := (s - 128).toNat + 96) (by omega) $$ W96
  mstep; mstep; mstep; mstep; mstep [W96]
  -- serialize(sp0 + 56, sp0 + 96)
  have hk1 := kOf_le (val (loN S) (hiN S))
  have S108 := SerdeStruct.f108_bounds (GF := GF) cfg lim (d + 1) types[13]! rfl inst mi A n g ta hm (by omega) Cg gt
    (s - 128) (s - 128 + 56) (s - 128 + 96) ptr0 idx (s - 128 + 112) q 128 [] maxP hl1
    [(q.toNat, 128), (p.toNat, 1)] (loN S) (hiN S) (loN S) (hiN S) (by omega) (by omega)
    (roomFor_of6 len maxP hl1 _ (newCap_le _) ⟨r1, r2, r3, r4⟩ (by omega) (by omega) (by omega))
    (by
      intro l hl
      rw [grownLen_small _ _ (newCap_le _)] at hl
      exact roomFor_of6 len maxP l _ (newCap_le _) ⟨r1, r2, r3, r4⟩ (by omega) (by omega) (by omega))
    (by simp; omega) (by omega) 2 (by decide)
  ihave #S108 := S108 $$ HSt
  ihave L80 := stkA (b := (s - 128).toNat - 592 + 512) (by omega) $$ L80
  ihave Lo := stkJ (a := (s - 128).toNat - 592) (b := (s - 128).toNat - 592 + 512) (k1 := 512) (k2 := 80)
    (k := 592) rfl rfl $$ [Lo512 L80]
  · iframe Lo512 L80
  icases stkSp 176 416 rfl $$ Lo with ⟨Lo176, L416⟩
  ihave L416 := stkA (b := (s - 128).toNat - 416) (by omega) $$ L416
  rw [StorageBalanceBounds.boundsBytes]
  icases splitB (a := (s - 128 + 56).toNat) (b := (s - 128 + 56).toNat + 24)
    (StorageBalanceBounds.u128Of (StorageMinimumBalance.minS S) ++ storeBytes (.i64 1) 8)
    (StorageBalanceBounds.u128Of (StorageMinimumBalance.minS S)) (by simp) $$ Hbd with ⟨Hb01, Hb24⟩
  icases splitB (a := (s - 128 + 56).toNat) (b := (s - 128 + 56).toNat + 16)
    (StorageBalanceBounds.u128Of (StorageMinimumBalance.minS S)) (storeBytes (.i64 1) 8) (by simp) $$ Hb01
    with ⟨Hb0, Hb16⟩
  rw [u128Of_N]
  repeat mstep
  mcall S108 using [Hg L416 HB HT Hvt Hlut Hinv Hb0 Hb16 Hb24 Hq He W96 V0 V4 V8 Hqb]
  · iframe Hg L416 HB Hinv Hb0 Hb16 Hb24
    isplitl [HT Hvt Hlut]
    · iunfold SerdeStruct.valIn; iframe HT Hvt Hlut
    iunfold SerdeStruct.strIn
    iframe Hq He
    isplitl [W96]
    · iapply memBytes_addr (show (s - 128).toNat + 96 = (s - 128 + 96).toNat by omega) $$ W96
    iunfold SerdeStruct.outV
    iexists bs
    iframe V0 V4
    isplitr
    · ipureintro; simp; omega
    simp only [List.nil_append]
    iframe Hqb V8
  icases HQ with ⟨%hrs, Hg, L416, -, -, ⟨%hl2, Hinv⟩, -, -, -, HS⟩
  subst hrs
  mcredits (100 * cfg.regularOpCost + R)
  rw [val_N]
  iunfold SerdeStruct.strIn at HS
  icases HS with ⟨-, -, Hser, Ho⟩
  iunfold SerdeStruct.outV at Ho
  icases Ho with ⟨%rst, %⟨hrst, -, -⟩, V0, V4, V8, Hqj⟩
  generalize hL : UInt32.ofNat (SerdeStruct.boundsJson (StorageMinimumBalance.minS S) (StorageMinimumBalance.minS S)).length = Lw
  -- `Ok(vec)` at sp0 + 96
  have hor : (s - 128 + 96) ||| 4 = s - 128 + 96 + 4 := by
    apply UInt32.toNat_inj.1
    simp only [UInt32.toNat_or, UInt32.toNat_add, UInt32.reduceToNat]
    have hx : ((s - 128).toNat + 96) % 2 ^ 32 = (s - 128).toNat + 96 := Nat.mod_eq_of_lt (by omega)
    rw [hx, Nat.mod_eq_of_lt (by omega)]
    have ee := Nat.two_pow_add_eq_or_of_lt (i := 3) (b := 4) (by decide) (((s - 128).toNat + 96) / 8)
    have m : 2 ^ 3 * (((s - 128).toNat + 96) / 8) = (s - 128).toNat + 96 := by omega
    rw [m] at ee
    omega
  repeat mstep
  rw [hor]
  have a100 : (s - 128 + 96 + 4).toNat = (s - 128).toNat + 100 := by simp [UInt32.toNat_add]; omega
  have a108 : (s - 128 + 96 + 4 + 8).toNat = (s - 128).toNat + 108 := by simp [UInt32.toNat_add]; omega
  have a120 : (s - 128 + 112 + 8).toNat = (s - 128).toNat + 120 := by simp [UInt32.toNat_add]; omega
  ihave V0 := memBytes_addr (b := (s - 128).toNat + 112) (by omega) $$ V0
  ihave V4 := memBytes_addr (b := (s - 128).toNat + 112 + 4) (by omega) $$ V4
  ihave V8 := memBytes_addr (b := (s - 128).toNat + 120) (by omega) $$ V8
  ihave V04 := join64' (a := (s - 128).toNat + 112) (b := (s - 128).toNat + 112 + 4) q 128 rfl $$ [V0 V4]
  · iframe V0 V4
  icases stk_bytes' $$ Q100 with ⟨%qb, %hqb8, Q100⟩
  ihave Q100 := memBytes_addr (b := (s - 128).toNat + 100) (by omega) $$ Q100
  icases stk_bytes' $$ L108 with ⟨%lb, %hlb, L108⟩
  ihave L108 := memBytes_addr (b := (s - 128).toNat + 108) (by omega) $$ L108
  mstep [V04]
  mstep [Q100]
  rw [ResultExpect.bytes64_decode _ (by simp)]
  repeat mstep
  mstep [V8]
  mstep [L108]
  repeat mstep
  ihave Hser := memBytes_addr (b := (s - 128).toNat + 96) (by omega) $$ Hser
  mstep [Hser]
  -- hand over to segment C
  subst hL
  ihave L416 := stkA (b := (s - 128).toNat - 592 + 176) (by omega) $$ L416
  ihave Lo := stkJ (a := (s - 128).toNat - 592) (b := (s - 128).toNat - 592 + 176) (k1 := 176) (k2 := 416)
    (k := 592) rfl rfl $$ [Lo176 L416]
  · iframe Lo176 L416
  ihave Lo := stkA (b := s.toNat - 720) (by omega) $$ Lo
  ihave Hser := memBytes_addr (b := s.toNat - 32) (by omega) $$ Hser
  icases split64' (a := (s - 128).toNat + 100) (b := s.toNat - 24) q 128 (by omega) $$ Q100 with ⟨R4, R8⟩
  ihave R4 := memBytes_addr (b := s.toNat - 28) (by omega) $$ R4
  ihave L108 := memBytes_addr (b := s.toNat - 20) (by omega) $$ L108
  ihave V04 := stkB (b := s.toNat - 16) (k := 8) _ (by omega) (by simp [bytes32]) $$ V04
  ihave V8 := stkW (b := s.toNat - 16 + 8) _ (by omega) $$ V8
  ihave V := stkJ (a := s.toNat - 16) (b := s.toNat - 16 + 8) (k1 := 8) (k2 := 4) (k := 12) rfl rfl $$ [V04 V8]
  · iframe V04 V8
  icases splitB (a := s.toNat - 88) (b := s.toNat - 84) (bytes32 p) _ (by simp; omega) $$ C24 with ⟨P0, C28⟩
  icases splitB (a := s.toNat - 84) (b := s.toNat - 80) (bytes32 1) _ (by simp; omega) $$ C28 with ⟨P4, C32⟩
  icases splitB (a := s.toNat - 80) (b := s.toNat - 76) (bytes32 1) _ (by simp; omega) $$ C32 with ⟨P8, -⟩
  rw [show SerdeStruct.boundsJson (StorageMinimumBalance.minS S) (StorageMinimumBalance.minS S) = boundsJ S from rfl]
  mcredits R
  iapply W $$ %q %p %rst %hl2 %4 %h1 [] Hc Hg HI Lo Hser R4 R8 L108 V P0 P4 P8 [Hqj] Hp Hinv Hh
  · ipureintro; exact ⟨hq1, by simpa [boundsJ] using hrst⟩
  · iexact Hqj

end SegM

/-! ## Segment C -/

section SegC

variable {GF : BundledGFunctors} [WasmGS NearState GF]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- `FtTotalSupply.segC` for `bodyC306`. -/
theorem segC306 (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (e inst : Nat) (mi : ModuleInst) (A : Nat → Nat)
    (n g ta : Nat) (mx : Option Nat) (hm : IfaceMod mi A n g ta) (hd : d + 8 < lim.maxCallDepth)
    (Cg R : Nat) (gt : GlobalType) (s : UInt32) (hs : 736 ≤ s.toNat) (hal : s.toNat % 8 = 0)
    (q L p : UInt32) (bs rest : List UInt8) (hbs : bs.length = L.toNat) (hpos : 0 < L.toNat)
    (hrest : bs.length + rest.length = 128) (maxP hl F : Nat) (h1 : NearState)
    (hlim : withinLimit h1.config.maxReturnLen L.toNat = true) (loc x1 x2 : UInt32) (Φ : Post NearState GF) :
    codeC e inst mi A n mx ∗ credits Cg (1010 * cfg.regularOpCost + valueReturnUse h1 L.toNat + R) ∗
      g ↦[wg] ⟨gt, .i32 (s - 128)⟩ ∗ ifaceR n ta A ∗ stk n (s.toNat - 208) 80 ∗ stk n (s.toNat - 120) 8 ∗
      n ↦[i32][ s.toNat - 32 ] 0 ∗ n ↦[i32][ s.toNat - 28 ] q ∗ n ↦[i32][ s.toNat - 24 ] 128 ∗
      n ↦[i32][ s.toNat - 20 ] L ∗ stk n (s.toNat - 16) 12 ∗
      n ↦[i32][ s.toNat - 88 ] p ∗ n ↦[i32][ s.toNat - 84 ] 1 ∗ n ↦[i32][ s.toNat - 80 ] 1 ∗
      n ↦[wms][ q.toNat ] (bs ++ rest) ∗ n ↦[wms][ p.toNat ] WNear.accountsPrefix ∗
      heapInv n maxP hl [(q.toNat, 128), (p.toNat, 1)] F ∗ mhostPt h1 ∗
      (credits Cg R -∗ g ↦[wg] ⟨gt, .i32 s⟩ -∗ mhostPt (h1.selectReturnValue bs) -∗
        Φ.normal [] ⟨#[.i32 (s - 128), .i32 x1, .i32 x2], inst, mi⟩)
      ⊢ mwpi cfg lim d ⟨#[.i32 (s - 128), .i32 x1, .i32 x2], inst, mi⟩ [] (bodyC306 loc) Φ := by
  iintro ⟨#Hk, Hc, Hg, HI, L2, F8, R0, R4, R8, R12, F128, V0, V4, V8, Hq, Hp, Hinv, Hh, W⟩
  ihave #Hk' := Hk
  iunfold codeC at Hk'
  icases Hk' with ⟨#HIC, #Hdr, #F456, #F158, #F779, #F545, #F68⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold dropCode at Hdr; icases Hdr with ⟨#Hi, -⟩; iexact Hi
  have hn := hm.mem
  have hg := hm.glob
  have ha158 := hm.funcs 158 (by decide)
  have ha779 := hm.funcs 779 (by decide)
  have ha545 := hm.funcs 545 (by decide)
  have ha68 := hm.funcs 68 (by decide)
  have t31 : types[31]!.params.length = 3 := rfl
  have t14 : types[14]!.params.length = 2 := rfl
  have t0 : types[0]!.params.length = 1 := rfl
  have hlt := s.toNat_lt
  have e0 : (s - 128).toNat = s.toNat - 128 := by rw [tsub _ _ (by simp; omega)]; simp
  have e1 : (s - 128 - 16).toNat = s.toNat - 144 := by rw [tsub _ _ (by simp [e0]; omega), e0]; simp; omega
  have e2 : (s - 128 - 16 - 16).toNat = s.toNat - 160 := by rw [tsub _ _ (by simp [e1]; omega), e1]; simp; omega
  have a128 : (s - 128 + 112).toNat = s.toNat - 16 := by simp [UInt32.toNat_add, e0]; omega
  have a72 : (s - 128 + 96).toNat = s.toNat - 32 := by simp [UInt32.toNat_add, e0]; omega
  have a8 : (s - 128 + 8).toNat = s.toNat - 120 := by simp [UInt32.toNat_add, e0]; omega
  have a56 : (s - 128 + 40).toNat = s.toNat - 88 := by simp [UInt32.toNat_add, e0]; omega
  have hLb : L.toNat ≤ 128 := by omega
  have hq := q.toNat_lt
  simp only [bodyC306]
  -- expect(sp0 + 128, sp0 + 72, loc)
  ihave PL := join64' (a := s.toNat - 28) (b := s.toNat - 24) q 128 (by omega) $$ [R4 R8]
  · iframe R4 R8
  ihave PL := joinB (a := s.toNat - 28) (b := s.toNat - 20) (bytes32 q ++ bytes32 128) (bytes32 L)
    (by simp; omega) $$ [PL R12]
  · iframe PL R12
  icases stk_bytes' $$ F128 with ⟨%ob, %hob, F128⟩
  mstep; mstep; mstep; mstep; mstep; mstep; mstep
  mcall (ResultExpect.f158_spec cfg lim (d + 1) types[31]! rfl inst mi n g hn hg Cg ⟨gt, .i32 (s - 128)⟩
      (s - 128) (s - 128 + 112) (s - 128 + 96) loc rfl (by omega) (by omega) (bytes32 0)
      (bytes32 q ++ bytes32 128 ++ bytes32 L) ob (by simp) (by simp) hob (by simp [decodeLE_bytes32]))
    using [Hg R0 PL F128]
  · iunfold ResultExpect.pre
    ihave R0 := memBytes_addr (b := (s - 128 + 96).toNat) (by omega) $$ R0
    ihave PL := memBytes_addr (b := (s - 128 + 96).toNat + 4) (by omega) $$ PL
    ihave F128 := memBytes_addr (b := (s - 128 + 112).toNat) (by omega) $$ F128
    iframe Hg R0 PL F128
    ipureintro; rfl
  iunfold ResultExpect.post at HQ
  icases HQ with ⟨%hrs, Hg, R0, PL, V128⟩
  subst hrs
  -- deref(sp0 + 8, sp0 + 128)
  icases stk_bytes' $$ F8 with ⟨%o8, %ho8, F8⟩
  mstep; mstep; mstep; mstep; mstep; mstep
  mcall (VecDeref.f779_spec cfg lim (d + 1) types[14]! rfl inst mi n hn Cg (s - 128 + 8) (s - 128 + 112) o8
      (bytes32 q ++ bytes32 128 ++ bytes32 L) ho8 (by simp)) using [F8 V128]
  · iunfold VecDeref.pre
    ihave F8 := memBytes_addr (b := (s - 128 + 8).toNat) (by omega) $$ F8
    iframe F8 V128
    ipureintro; rfl
  iunfold VecDeref.post at HQ
  icases HQ with ⟨%hrs, O8, V128⟩
  subst hrs
  have hvb : (bytes32 q ++ (bytes32 128 ++ bytes32 L)).take 4 ++ (bytes32 q ++ (bytes32 128 ++ bytes32 L)).drop 8 =
      bytes32 q ++ bytes32 L := by
    simp [List.take_append, List.drop_append, bytes32_length]
  rw [hvb]
  ihave O8 := memBytes_addr (b := s.toNat - 120) (by omega) $$ O8
  icases split64' (a := s.toNat - 120) (b := s.toNat - 116) q L (by omega) $$ O8 with ⟨O8, O12⟩
  mstep; mstep [O8]; mstep; mstep [O12]
  -- value_return(q, L)
  icases stkSp 48 32 rfl $$ L2 with ⟨L48, L2⟩
  icases stkSp 4 28 rfl $$ L2 with ⟨X48, L2⟩
  icases stkSp 4 24 rfl $$ L2 with ⟨X52, L2⟩
  icases stkSp 4 20 rfl $$ L2 with ⟨X56, L2⟩
  icases stkSp 4 16 rfl $$ L2 with ⟨X60, L2⟩
  icases stkSp 8 8 rfl $$ L2 with ⟨Y64, L2⟩
  icases stkSp 4 4 rfl $$ L2 with ⟨X72, X76⟩
  icases stk4_word $$ X48 with ⟨%x48, X48⟩
  icases stk4_word $$ X52 with ⟨%x52, X52⟩
  icases stk4_word $$ X56 with ⟨%x56, X56⟩
  icases stk4_word $$ X60 with ⟨%x60, X60⟩
  icases stk4_word $$ X72 with ⟨%x72, X72⟩
  icases stk4_word $$ X76 with ⟨%x76, X76⟩
  ihave HI := iface_of_ifaceR n ta A $$ HI
  icases HI with ⟨HI, HS12⟩
  icases splitB (a := q.toNat) (b := q.toNat + bs.length) bs rest rfl $$ Hq with ⟨Hb, Hr⟩
  ihave #S545 := ValueReturn.f545_spec cfg lim (d + 1) types[14]! rfl inst mi e A n g ta mx hm (by omega) Cg
    ⟨gt, .i32 (s - 128)⟩ (s - 128) rfl (by omega) (by omega) h1 q L bs hbs hlim hpos x72 x76 x48 x52 x56 x60
    $$ []
  · iframe F456 HIC
  mcall S545 using [Hg HI X72 X76 X48 X52 X56 X60 Hb Hh]
  · iunfold ValueReturn.pre, frame4
    ihave X72 := memBytes_addr (b := (s - 128 - 16).toNat + 8) (by omega) $$ X72
    ihave X76 := memBytes_addr (b := (s - 128 - 16).toNat + 12) (by omega) $$ X76
    ihave X48 := memBytes_addr (b := (s - 128 - 16 - 16).toNat) (by omega) $$ X48
    ihave X52 := memBytes_addr (b := (s - 128 - 16 - 16).toNat + 4) (by omega) $$ X52
    ihave X56 := memBytes_addr (b := (s - 128 - 16 - 16).toNat + 8) (by omega) $$ X56
    ihave X60 := memBytes_addr (b := (s - 128 - 16 - 16).toNat + 12) (by omega) $$ X60
    iframe Hg HI X72 X76 X48 X52 X56 X60 Hb Hh
    ipureintro; rfl
  iunfold ValueReturn.post at HQ
  icases HQ with ⟨%hrs, Hg, HI, X72, X76, HF4, Hb, Hh⟩
  subst hrs
  -- drop the JSON `Vec` (q, 128, L)
  ihave V128 := memBytes_addr (b := s.toNat - 16) (by omega) $$ V128
  icases splitB (a := s.toNat - 16) (b := s.toNat - 12) (bytes32 q) (bytes32 128 ++ bytes32 L) (by simp; omega)
    $$ V128 with ⟨V128, V132⟩
  icases split64' (a := s.toNat - 12) (b := s.toNat - 8) 128 L (by omega) $$ V132 with ⟨V132, V136⟩
  mstep; mstep; mstep
  mcall (f68_spec cfg lim (d + 1) types[0]! rfl inst mi A n g ta hm (by omega) Cg maxP hl
      [(q.toNat, 128), (p.toNat, 1)] F (s - 128 + 112) q 128 L (by decide) (by omega))
    using [V128 V132 V136 Hinv Hb Hr]
  · iunfold pre747
    ihave V128 := memBytes_addr (b := (s - 128 + 112).toNat) (by omega) $$ V128
    ihave V132 := memBytes_addr (b := (s - 128 + 112).toNat + 4) (by omega) $$ V132
    ihave V136 := memBytes_addr (b := (s - 128 + 112).toNat + 8) (by omega) $$ V136
    ihave Hq := joinB (a := q.toNat) (b := q.toNat + bs.length) bs rest rfl $$ [Hb Hr]
    · iframe Hb Hr
    iframe V128 V132 V136 Hinv
    isplitr
    · ipureintro; rfl
    isplitr
    · ipureintro; simp
    iunfold block
    iexists bs ++ rest
    iframe Hq
    ipureintro; simp; omega
  iunfold post747 at HQ
  icases HQ with ⟨%hrs, V128, V132, V136, Hinv⟩
  subst hrs
  -- drop the prefix's `Vec` (p, 1, 1)
  mstep; mstep; mstep
  have hlive : [(q.toNat, 128), (p.toNat, 1)].erase (q.toNat, 128) = [(p.toNat, 1)] := by
    simp
  rw [hlive]
  mcall (f68_spec cfg lim (d + 1) types[0]! rfl inst mi A n g ta hm (by omega) Cg maxP hl
      [(p.toNat, 1)] (F + 1) (s - 128 + 40) p 1 1 (by decide) (by omega))
    using [V0 V4 V8 Hinv Hp]
  · iunfold pre747
    ihave V0 := memBytes_addr (b := (s - 128 + 40).toNat) (by omega) $$ V0
    ihave V4 := memBytes_addr (b := (s - 128 + 40).toNat + 4) (by omega) $$ V4
    ihave V8 := memBytes_addr (b := (s - 128 + 40).toNat + 8) (by omega) $$ V8
    iframe V0 V4 V8 Hinv
    isplitr
    · ipureintro; rfl
    isplitr
    · ipureintro; simp
    iunfold block
    iexists WNear.accountsPrefix
    iframe Hp
    ipureintro; rw [StateReadModel.accountsPrefix_length]; rfl
  iunfold post747 at HQ
  icases HQ with ⟨%hrs, -⟩
  subst hrs
  -- the epilogue
  mstep; mstep; mstep; mstep [Hg]
  rw [show s - 128 + 128 = s by simp]
  mcredits R
  iapply W $$ Hc Hg Hh

end SegC

/-! ## On an absent `STATE` -/

section None

variable {GF : BundledGFunctors} [WasmGS NearState GF]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- `FtTotalSupply.segBNone` for the shared prefix `bodyB306` followed by anything: `state_read`
(219) leaves `None`, and `unwrap_or_default` (155) traps through `Contract::default`, the host
after `storage_read` panicked. -/
theorem segBNone306 (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (e inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 18 < lim.maxCallDepth)
    (Cg R : Nat) (gt : GlobalType) (s : UInt32) (hs : 736 ≤ s.toNat) (hal : s.toNat % 8 = 0)
    (idx : UInt32) (maxP len : Nat) (h : NearState) (st : Near.TrieOverlay.State) (hr : ReadNone h st)
    (rest : List Instr) (Φ : Post NearState GF) :
    codeM306 e inst mi A n maxP ∗ ifaceCode e inst mi A n (some maxP) ∗ codeP e inst mi A ∗
      credits Cg (costBNone cfg h + R) ∗ g ↦[wg] ⟨gt, .i32 (s - 128)⟩ ∗ ifaceR n ta A ∗
      stk n (s.toNat - 720) 592 ∗ stk n (s.toNat - 72) 40 ∗ vt n 1057464 idx ta (A 578) ∗
      heapInv n maxP len [] 1 ∗ n ↦[wms][ 1049788 ] StateRead.stateKey ∗ staticsP n ta A ∗ mhostPt h ∗
      (∀ h1, ⌜StorageReadPost h StateRead.stateKey 0 st h1⌝ -∗ panicked Cg h1 notInit -∗ Φ.trap)
      ⊢ mwpi cfg lim d ⟨#[.i32 (s - 128), .i32 1, .i32 0], inst, mi⟩ [] (bodyB306 ++ rest) Φ := by
  iintro ⟨#Hk, #HIC, #HP, Hc, Hg, HI, Lo, F72, Hvt, Hinv, Hkey, HSP, Hh, W⟩
  ihave #Hk' := Hk
  iunfold codeM306 at Hk'
  icases Hk' with ⟨#HSC, #F219, #F155, -, -, -, -, -, -, -, -, -, #Hi⟩
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
  have e0 : (s - 128).toNat = s.toNat - 128 := by rw [tsub _ _ (by simp; omega)]; simp
  have e1 : (s - 128 - 16).toNat = s.toNat - 144 := by rw [tsub _ _ (by simp [e0]; omega), e0]; simp; omega
  have e2 : (s - 128 - 16 - 16).toNat = s.toNat - 160 := by
    rw [tsub _ _ (by simp [e1]; omega), e1]; simp; omega
  have a72 : (s - 128 + 56).toNat = s.toNat - 72 := by simp [UInt32.toNat_add, e0]; omega
  iapply mwpi_seq
  simp only [bodyB306]
  -- state_read(sp0 + 72): None
  icases stk_bytes' $$ F72 with ⟨%ob, %hob, F72⟩
  mstep; mstep; mstep
  have S219 := StateRead.f219_spec_none (GF := GF) cfg lim (d + 1) types[0]! rfl inst mi e A n g ta (some maxP) hm
    (by omega) Cg gt (s - 128) (s - 128 + 56) (by omega) (by omega) (by omega) idx maxP len [] ob hob h hv st hacc
    hlim hb hz hlink hproof
  simp only [StorageReadWrap.costS] at S219
  mcall S219 using [Hg HI Lo Hvt Hinv F72 Hkey Hh]
  · iunfold pre219
    ihave Lo := stkA (b := (s - 128).toNat - 592) (by omega) $$ Lo
    ihave F72 := memBytes_addr (b := (s - 128 + 56).toNat) (by omega) $$ F72
    iframe Hg HI Lo Hvt Hinv F72 Hkey Hh
    ipureintro; rfl
  iunfold post219None at HQ
  icases HQ with ⟨%hrs, Hg, HI, Lo, -, -, Ho, -, ⟨%h1, %hq1, Hh⟩⟩
  subst hrs
  obtain ⟨hcfg, hlogs, hext, -⟩ := storageReadPost_fields hq1
  -- the zero niche at sp0 + 72 + 24
  iunfold noneAt at Ho
  icases splitB (a := (s - 128 + 56).toNat) (b := (s - 128 + 56).toNat + 28) (ob.take 24 ++ [0, 0, 0, 0])
    (ob.drop 28) (by simp [hob]) $$ Ho with ⟨Ho, -⟩
  icases splitB (a := (s - 128 + 56).toNat) (b := (s - 128 + 56).toNat + 24) (ob.take 24) [0, 0, 0, 0]
    (by simp [hob]) $$ Ho with ⟨-, H24⟩
  ihave H24 := (show (n ↦[wms][ (s - 128 + 56).toNat + 24 ] [0, 0, 0, 0] : IProp GF) ⊢
    n ↦[i32][ (s - 128 + 56).toNat + 24 ] 0 by rw [StateRead.bytes32_zero']) $$ H24
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
    (code := f155) [.i32 (s - 128 + 16), .i32 (s - 128 + 56)])
  isplitr
  · iapply (UnwrapOrDefault.f155_spec_none cfg lim (d + 1) types[14]! inst mi e A n g ta (some maxP) hm
      (by omega) Cg ⟨gt, .i32 (s - 128)⟩ (s - 128) rfl (by omega) (by omega) (s - 128 + 16) (s - 128 + 56)
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
    ihave C0 := memBytes_addr (b := (s - 128 - 16).toNat + 8) (by omega) $$ C0
    ihave C4 := memBytes_addr (b := (s - 128 - 16).toNat + 12) (by omega) $$ C4
    ihave W0 := memBytes_addr (b := (s - 128 - 16 - 16).toNat) (by omega) $$ W0
    ihave W4 := memBytes_addr (b := (s - 128 - 16 - 16).toNat + 4) (by omega) $$ W4
    ihave W8 := memBytes_addr (b := (s - 128 - 16 - 16).toNat + 8) (by omega) $$ W8
    ihave W12 := memBytes_addr (b := (s - 128 - 16 - 16).toNat + 12) (by omega) $$ W12
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

/-! ## The body -/

theorem f306_body : f306.body = bodyA306 ++ ((bodyB306 ++ bodyM306) ++ bodyC306 1051200) := rfl

theorem entryLocals_f306 : entryLocals f306 [] = #[.i32 0, .i32 0, .i32 0] := rfl

theorem boundsJ_pos (S : WNear.State) : 0 < (boundsJ S).length := by
  simp [boundsJ, SerdeStruct.boundsJson]

/-- The cost of `storage_balance_bounds` (306), activation excluded: segment A's 477
`regular_op_cost`s, the middle segment's `costM306`, segment C's 1010 and `value_return`'s gas. -/
noncomputable def cost306 (cfg : WasmConfig) (h : NearState) (S : WNear.State) : Nat :=
  477 * cfg.regularOpCost + costM306 cfg h S + 1010 * cfg.regularOpCost + valueReturnUse h (boundsJ S).length

/-- Its cost on an absent `STATE`: segment A's and `costBNone`. -/
def cost306None (cfg : WasmConfig) (h : NearState) : Nat :=
  477 * cfg.regularOpCost + costBNone cfg h

section Main

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The code `storage_balance_bounds` runs (persistent). -/
def code306 (e inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n maxP : Nat) : IProp GF :=
  iprop(codeA inst mi A ∗ codeM306 e inst mi A n maxP ∗ codeC e inst mi A n (some maxP))

instance (e inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n maxP : Nat) :
    Persistent (code306 (GF := GF) e inst mi A n maxP) := by
  unfold code306; infer_instance

/-- The statics `storage_balance_bounds` owns: `ft_total_supply`'s and the struct serializer's
data (`SerdeStruct.boundsData`). -/
noncomputable def statics306 (n ta : Nat) (A : Nat → Nat) (old k3 idx ptr0 : UInt32) (maxP len : Nat) :
    IProp GF :=
  iprop(statics n ta A old k3 idx ptr0 maxP len ∗ SerdeStruct.boundsData n)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **The body of `storage_balance_bounds`** (306), from its entry frame: with the statics, 736 bytes
of stack below the stack pointer `s` and the host `h` reading the model state `S`, it falls
through with the stack pointer restored and the host `h1.selectReturnValue (boundsJ S)`, `h1` the
host after `storage_read`. -/
theorem body306 (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (e inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 30 < lim.maxCallDepth)
    (Cg R : Nat) (gt : GlobalType) (s : UInt32) (hs : 736 ≤ s.toNat)
    (hal : s.toNat % 8 = 0) (old k3 idx ptr0 : UInt32) (maxP len : Nat) (hroom : HeapRoom6 len maxP)
    (h : NearState) (S : WNear.State) (st : Near.TrieOverlay.State) (hr : U128View.ReadOkV h S st (boundsJ S))
    (Φ : Post NearState GF) :
    code306 e inst mi A n maxP ∗ credits Cg (cost306 cfg h S + R) ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
      stk n (s.toNat - 736) 736 ∗ statics306 n ta A old k3 idx ptr0 maxP len ∗ mhostPt h ∗
      (∀ h1, ⌜StorageReadPost h StateRead.stateKey 0 st h1⌝ -∗ credits Cg R -∗ g ↦[wg] ⟨gt, .i32 s⟩ -∗
        mhostPt (h1.selectReturnValue (boundsJ S)) -∗ Φ.normal [] ⟨#[.i32 (s - 128), .i32 0, .i32 0], inst, mi⟩)
      ⊢ mwpi cfg lim d ⟨#[.i32 0, .i32 0, .i32 0], inst, mi⟩ [] f306.body Φ := by
  iintro ⟨#Hk, Hc, Hg, Stk, HS, Hh, W⟩
  iunfold code306 at Hk
  icases Hk with ⟨#KA, #KM, #KC⟩
  iunfold statics306 at HS
  icases HS with ⟨HS, HB⟩
  iunfold statics at HS
  icases HS with ⟨HH, Hkey, T116, T106, HBI, HV, Hvt, Hinv, HsK, HT⟩
  iunfold ToVec.tvData at HT
  icases HT with ⟨HT, Hq, He, Hlut⟩
  obtain ⟨hv, hacc, hlim, hb, hz, hlink, hproof, hreg, hret⟩ := hr
  have hlt := s.toNat_lt
  have hJ := boundsJ_length S
  have hJ0 := boundsJ_pos S
  have hL : (UInt32.ofNat (boundsJ S).length).toNat = (boundsJ S).length := by
    simp only [UInt32.toNat_ofNat']; omega
  icases stkSp 16 720 rfl $$ Stk with ⟨-, Stk⟩
  icases stkSp 512 208 rfl $$ Stk with ⟨Lo512, Stk⟩
  icases stkSp 80 128 rfl $$ Stk with ⟨L2, Stk⟩
  icases stkSp 8 120 rfl $$ Stk with ⟨-, Stk⟩
  icases stkSp 8 112 rfl $$ Stk with ⟨F8, Stk⟩
  icases stkSp 40 72 rfl $$ Stk with ⟨F16, Stk⟩
  icases stkSp 40 32 rfl $$ Stk with ⟨F56, Stk⟩
  icases stkSp 16 16 rfl $$ Stk with ⟨F96, Stk⟩
  icases stkSp 12 4 rfl $$ Stk with ⟨F112, -⟩
  rw [f306_body]
  iapply segA306 cfg lim d inst mi A n g ta hm (by omega) Cg
    (costM306 cfg h S + (1010 * cfg.regularOpCost + valueReturnUse h (boundsJ S).length + R))
    gt s hs hal old k3 ((bodyB306 ++ bodyM306) ++ bodyC306 1051200) Φ
  ihave L2 := stkA (b := s.toNat - 208) (by omega) $$ L2
  iframe KA Hg L2 HH Hkey T116 T106 HBI HV
  isplitl [Hc]
  · iapply credits_mono (by unfold cost306; omega) $$ Hc
  iintro Hc Hg L2 HI
  ihave L2 := stkA (b := s.toNat - 736 + 16 + 512) (by omega) $$ L2
  ihave Lo := stkJ (a := s.toNat - 736 + 16) (b := s.toNat - 736 + 16 + 512) (k1 := 512) (k2 := 80) (k := 592)
    rfl rfl $$ [Lo512 L2]
  · iframe Lo512 L2
  ihave Lo := stkA (b := s.toNat - 720) (by omega) $$ Lo
  iapply segM306 cfg lim d e inst mi A n g ta hm hd Cg
    (1010 * cfg.regularOpCost + valueReturnUse h (boundsJ S).length + R) gt s hs hal idx ptr0 maxP len hroom
    h S hv st hacc hlim hb hz hlink hproof hreg (bodyC306 1051200) Φ
  ihave F16 := stkA (b := s.toNat - 112) (by omega) $$ F16
  ihave F56 := stkA (b := s.toNat - 72) (by omega) $$ F56
  ihave F96 := stkA (b := s.toNat - 32) (by omega) $$ F96
  ihave F112 := stkA (b := s.toNat - 16) (by omega) $$ F112
  iframe KM Hc Hg HI Lo F16 F56 F96 F112 Hvt Hinv HsK HT Hlut Hq He HB Hh
  iintro %q %p %rst %hl %F %h1 %⟨hq1, hrst⟩ Hc Hg HI Lo R0 R4 R8 R12 V P0 P4 P8 Hqj Hp Hinv Hh
  obtain ⟨hcfg, hvru⟩ := storageReadPost_config hq1
  icases stkSp 512 80 rfl $$ Lo with ⟨-, L2⟩
  ihave L2 := stkA (b := s.toNat - 208) (by omega) $$ L2
  ihave F8 := stkA (b := s.toNat - 120) (by omega) $$ F8
  iapply segC306 cfg lim d e inst mi A n g ta (some maxP) hm (by omega) Cg R gt s hs hal q
    (UInt32.ofNat (boundsJ S).length) p (boundsJ S) rst hL.symm (by omega) hrst maxP hl F h1
    (by rw [hcfg, hL]; exact hret) 1051200 0 0 Φ
  iframe KC Hg HI L2 F8 R0 R4 R8 R12 V P0 P4 P8 Hqj Hp Hinv Hh
  isplitl [Hc]
  · rw [hvru, hL]; iexact Hc
  iintro Hc Hg Hh
  iapply W $$ %h1 %hq1 Hc Hg Hh

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **The body of `storage_balance_bounds` on an uninitialized contract** (306): it traps in
`unwrap_or_default`, the host after `storage_read` panicked with "The contract is not
initialized", at `cost306None`. -/
theorem body306None (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (e inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 18 < lim.maxCallDepth)
    (Cg R : Nat) (gt : GlobalType) (s : UInt32) (hs : 736 ≤ s.toNat) (hal : s.toNat % 8 = 0)
    (old k3 idx ptr0 : UInt32) (maxP len : Nat) (h : NearState) (st : Near.TrieOverlay.State)
    (hr : ReadNone h st) (Φ : Post NearState GF) :
    code306 e inst mi A n maxP ∗ codeP e inst mi A ∗ credits Cg (cost306None cfg h + R) ∗
      g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 736) 736 ∗ statics306 n ta A old k3 idx ptr0 maxP len ∗
      staticsP n ta A ∗ mhostPt h ∗
      (∀ h1, ⌜StorageReadPost h StateRead.stateKey 0 st h1⌝ -∗ panicked Cg h1 notInit -∗ Φ.trap)
      ⊢ mwpi cfg lim d ⟨#[.i32 0, .i32 0, .i32 0], inst, mi⟩ [] f306.body Φ := by
  iintro ⟨#Hk, #HP, Hc, Hg, Stk, HS, HSP, Hh, W⟩
  iunfold code306 at Hk
  icases Hk with ⟨#KA, #KM, #KC⟩
  ihave #HIC : ifaceCode e inst mi A n (some maxP) $$ []
  · iunfold codeC at KC
    icases KC with ⟨#HIC, -⟩
    iexact HIC
  iunfold statics306 at HS
  icases HS with ⟨HS, -⟩
  iunfold statics at HS
  icases HS with ⟨HH, Hkey, T116, T106, HBI, HV, Hvt, Hinv, HsK, -⟩
  have hlt := s.toNat_lt
  icases stkSp 16 720 rfl $$ Stk with ⟨-, Stk⟩
  icases stkSp 512 208 rfl $$ Stk with ⟨Lo512, Stk⟩
  icases stkSp 80 128 rfl $$ Stk with ⟨L2, Stk⟩
  icases stkSp 56 72 rfl $$ Stk with ⟨-, Stk⟩
  icases stkSp 40 32 rfl $$ Stk with ⟨F56, -⟩
  rw [f306_body]
  iapply segA306 cfg lim d inst mi A n g ta hm (by omega) Cg (costBNone cfg h + R) gt s hs hal old k3
    ((bodyB306 ++ bodyM306) ++ bodyC306 1051200) Φ
  ihave L2 := stkA (b := s.toNat - 208) (by omega) $$ L2
  iframe KA Hg L2 HH Hkey T116 T106 HBI HV
  isplitl [Hc]
  · iapply credits_mono (by unfold cost306None; omega) $$ Hc
  iintro Hc Hg L2 HI
  ihave L2 := stkA (b := s.toNat - 736 + 16 + 512) (by omega) $$ L2
  ihave Lo := stkJ (a := s.toNat - 736 + 16) (b := s.toNat - 736 + 16 + 512) (k1 := 512) (k2 := 80) (k := 592)
    rfl rfl $$ [Lo512 L2]
  · iframe Lo512 L2
  ihave Lo := stkA (b := s.toNat - 720) (by omega) $$ Lo
  rw [List.append_assoc]
  iapply segBNone306 cfg lim d e inst mi A n g ta hm hd Cg R gt s hs hal idx maxP len h st hr
    (bodyM306 ++ bodyC306 1051200) Φ
  ihave F56 := stkA (b := s.toNat - 72) (by omega) $$ F56
  iframe KM HIC HP Hc Hg HI Lo F56 Hvt Hinv HsK HSP Hh W

end Main

end WNear.Binary.StorageBalanceBoundsBody
