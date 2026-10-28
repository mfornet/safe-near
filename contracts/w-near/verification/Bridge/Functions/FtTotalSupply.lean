import Bridge.Functions.StateReadLen
import Bridge.Functions.ToVec
import Bridge.Functions.ResultExpect
import Bridge.Functions.UnwrapOrDefault
import Bridge.Functions.FtTotalSupplyGetter
import Bridge.Functions.SetupPanicHook
import Bridge.Functions.SetBlockchainInterface

/-!
# `ft_total_supply` (function 296), assembled (milestone M3)

```wat
;; 296 ft_total_supply(): sp -= 144 (the frame at sp0 = sp - 144)
setup_panic_hook()                               ;; 522
set_blockchain_interface(1, 1050188)             ;; 520
state_read(sp0 + 72)                             ;; 219: Some(contract) at sp0 + 72
unwrap_or_default(sp0 + 32, sp0 + 72)            ;; 155: the contract at sp0 + 32
ft_total_supply(sp0 + 16, sp0 + 32)              ;; 414: the u128 at sp0 + 16
[sp0 + 120] := [sp0 + 24]; [sp0 + 112] := [sp0 + 16]   ;; U128(total) at sp0 + 112
to_vec(sp0 + 72, sp0 + 112)                      ;; 96: Ok(vec) at sp0 + 72
expect(sp0 + 128, sp0 + 72, loc)                 ;; 158: the vec at sp0 + 128
deref(sp0 + 8, sp0 + 128)                        ;; 779: the slice at sp0 + 8
value_return([sp0 + 8], [sp0 + 12])              ;; 545
drop(sp0 + 128); drop(sp0 + 56)                  ;; 68: the JSON bytes, the prefix
sp += 144
```

`f296_spec`: from a fresh instance's statics (the panic hook and the blockchain interface not
set up, the vtable words and table entries the interface uses), 736 bytes of stack below `sp`,
the heap (`heapInv … [] 1`) with room for three grows, `to_string`'s data and a host whose
storage at `STATE` is the model's `header s`: the method ends with the host
`h1.selectReturnValue (jsonOf (s.totalSupply % 2^128))`, `h1` the host after `storage_read`
(`StorageReadPost`: `h` up to gas, the accounting's caches and register 0).

## What is assumed

* `ToVecAfterFree cfg lim x96`: `serde_json::to_vec::<U128>` (96) as `ToVec.f96_spec` states it,
  but from the heap `state_read` leaves, whose free list holds two cells (`heapInv … 2`), at an
  extra cost `x96`. The postcondition's heap is `heapInv … F'` for some `F'`. Discharged with
  `x96 = 0` by `ToVecTwo.toVecAfterFree_zero` (`f96_spec` at `F = 2`, through
  `AllocTwo.f310_spec_two`); `Methods/FtTotalSupplyRefines.lean` uses it.
* The storage premises of `storage_read` (`f548_spec_host`), as hypotheses: the accounting
  state, the trie link and canonical trie (`hlink`, `hb`), no witness hashing to zero (`hz`),
  room in the recorded proof for the lookup (`ProofBudget`, SAF-67), the link through the overlay's view, the key and register limits.
* `withinLimit h.config.maxReturnLen` of the JSON's length.

The proof is split into three segments (`segA`, `segB`, `segC`) so that each proof term stays
small enough for the kernel.
-/

namespace WNear.Binary.FtTotalSupply

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
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
open WNear.Binary.StateRead (stateCode pre219)
open WNear.Binary.ToVec (tvCode tvData cost96 len_json)
open WNear.Binary.ToString (tsData)
open WNear.Binary.FmtDigits (decDigits)
open WNear.Binary.FmtU128 (val)
open WNear.Binary.FmtString (kOf)
open WNear.Binary.FmtGrow (newCap)
open WNear.Binary.U128From (u128Bytes)
open WNear.Binary.DropVec (dropCode pre747 post747 f68_spec)
open WNear.Binary.RegisterLen (frame4)

/-! ## The body, in three segments -/

/-- The prologue, `setup_panic_hook` and `set_blockchain_interface`. -/
def bodyA : List Instr :=
  [.global_get 0, .i32_const 144, .i32_binop .sub, .local_tee 0, .global_set 0, .call 522,
    .i32_const 1, .i32_const 1050188, .call 520]

/-- `state_read`, `unwrap_or_default`, the getter, the copy of the `u128`, `to_vec`. -/
def bodyB : List Instr :=
  [.local_get 0, .i32_const 72, .i32_binop .add, .call 219,
    .local_get 0, .i32_const 32, .i32_binop .add, .local_get 0, .i32_const 72, .i32_binop .add, .call 155,
    .local_get 0, .i32_const 16, .i32_binop .add, .local_get 0, .i32_const 32, .i32_binop .add, .call 414,
    .local_get 0, .local_get 0, .i32_const 24, .i32_binop .add, .load .i64 none { align := 3, offset := 0 },
    .store .i64 none { align := 3, offset := 120 },
    .local_get 0, .local_get 0, .load .i64 none { align := 3, offset := 16 },
    .store .i64 none { align := 3, offset := 112 },
    .local_get 0, .i32_const 72, .i32_binop .add, .local_get 0, .i32_const 112, .i32_binop .add, .call 96]

/-- `expect`, `deref`, `value_return`, the two drops and the epilogue. -/
def bodyC : List Instr :=
  [.local_get 0, .i32_const 128, .i32_binop .add, .local_get 0, .i32_const 72, .i32_binop .add,
    .i32_const 1050984, .call 158,
    .local_get 0, .i32_const 8, .i32_binop .add, .local_get 0, .i32_const 128, .i32_binop .add, .call 779,
    .local_get 0, .load .i32 none { align := 2, offset := 8 }, .local_get 0,
    .load .i32 none { align := 2, offset := 12 }, .call 545,
    .local_get 0, .i32_const 128, .i32_binop .add, .call 68,
    .local_get 0, .i32_const 56, .i32_binop .add, .call 68,
    .local_get 0, .i32_const 144, .i32_binop .add, .global_set 0]

theorem f296_body : f296.body = bodyA ++ (bodyB ++ bodyC) := rfl

theorem entryLocals_f296 : entryLocals f296 [] = #[.i32 0] := rfl

/-! ## Arithmetic -/

theorem tsub (x y : UInt32) (h : y.toNat ≤ x.toNat) : (x - y).toNat = x.toNat - y.toNat :=
  UInt32.toNat_sub_of_le x y (UInt32.le_iff_toNat_le.mpr h)

/-- The JSON string of a `u128`: `"` ++ its decimal digits ++ `"`. -/
def jsonOf (N : Nat) : List UInt8 := [34] ++ decDigits N ++ [34]

theorem decodeLE_cons (b : UInt8) (bs : List UInt8) :
    Memory.decodeLE (b :: bs) = b.toNat + 256 * Memory.decodeLE bs := by
  simp only [Memory.decodeLE, List.foldr_cons]
  omega

theorem decodeLE_leBytes (w N : Nat) : Memory.decodeLE (NearSdk.Borsh.leBytes w N) = N % 256 ^ w := by
  induction w generalizing N with
  | zero => simp [NearSdk.Borsh.leBytes, Memory.decodeLE, Nat.mod_one]
  | succ w ih =>
    rw [NearSdk.Borsh.leBytes, decodeLE_cons, ih]
    have e : (UInt8.ofNat (N % 256)).toNat = N % 256 := by simp [UInt8.toNat_ofNat']
    rw [e, Nat.pow_succ, Nat.mul_comm (256 ^ w) 256, Nat.mod_mul]

theorem leBytes_add (a b N : Nat) :
    NearSdk.Borsh.leBytes (a + b) N = NearSdk.Borsh.leBytes a N ++ NearSdk.Borsh.leBytes b (N / 256 ^ a) := by
  induction a generalizing N with
  | zero => simp [NearSdk.Borsh.leBytes]
  | succ a ih =>
    rw [Nat.add_right_comm, NearSdk.Borsh.leBytes, NearSdk.Borsh.leBytes, ih, Nat.div_div_eq_div_mul,
      Nat.pow_succ, Nat.mul_comm (256 ^ a) 256]
    rfl

/-- The two words of the Borsh `u128` of `N` are `N mod 2^128`. -/
theorem val_u128 (N : Nat) :
    val (UInt64.ofNat (Memory.decodeLE ((WNear.Borsh.u128 N).take 8)))
      (UInt64.ofNat (Memory.decodeLE ((WNear.Borsh.u128 N).drop 8))) = N % 2 ^ 128 := by
  have e : WNear.Borsh.u128 N = NearSdk.Borsh.leBytes 8 N ++ NearSdk.Borsh.leBytes 8 (N / 256 ^ 8) :=
    leBytes_add 8 8 N
  rw [e, List.take_left' (by simp), List.drop_left' (by simp), decodeLE_leBytes, decodeLE_leBytes]
  simp only [val, UInt64.toNat_ofNat']
  have h1 : N % 256 ^ 8 % 2 ^ 64 = N % 2 ^ 64 := by norm_num
  have h2 : N / 256 ^ 8 % 256 ^ 8 % 2 ^ 64 = N / 2 ^ 64 % 2 ^ 64 := by norm_num
  rw [h1, h2]
  have := Nat.mod_mul (x := N) (a := 2 ^ 64) (b := 2 ^ 64)
  rw [show (2 : Nat) ^ 128 = 2 ^ 64 * 2 ^ 64 by norm_num, this]

/-- The pages a grow asks for, for at most 128 bytes: one. -/
theorem cellPages_small (size : UInt32) (h : size.toNat ≤ 128) : (cellPages (wordsOf size) 1).toNat = 1 := by
  have hw : (wordsOf size).toNat = (size.toNat + 3) / 4 := by
    simp only [wordsOf, UInt32.toNat_ofNat']; omega
  rw [cellPages_toNat _ _ (by omega) (by decide), cellBytes_toNat _ _ (by omega) (by decide), hw]
  simp only [UInt32.reduceToNat]
  omega

theorem grownLen_small (len : Nat) (size : UInt32) (h : size.toNat ≤ 128) :
    grownLen len size = len + 65536 := by
  simp only [grownLen, cellPages_small size h]

/-- Room for four grows of one page under the limit `maxP` (and `2^32`). -/
def HeapRoom (len maxP : Nat) : Prop :=
  len % 65536 = 0 ∧ 0 < len ∧ len + 4 * 65536 ≤ maxP * 65536 ∧ len + 5 * 65536 ≤ 2 ^ 32

theorem roomFor_of (len maxP L : Nat) (size : UInt32) (h : size.toNat ≤ 128) (hr : HeapRoom len maxP)
    (h1 : len ≤ L) (h2 : L ≤ len + 3 * 65536) (h3 : L % 65536 = 0) : roomFor L maxP size := by
  obtain ⟨r1, r2, r3, r4⟩ := hr
  refine ⟨h3, by omega, ?_, ?_⟩ <;> (rw [cellPages_small size h]; omega)

theorem lenStep_bounds (len L : Nat) (hr : len % 65536 = 0) (h : LenStep len 29 1 L) :
    len ≤ L ∧ L ≤ len + 2 * 65536 ∧ L % 65536 = 0 := by
  obtain ⟨l1, h1, h2⟩ := h
  rw [grownLen_small _ _ (by decide)] at h1
  rw [grownLen_small _ _ (by decide)] at h2
  omega

theorem kOf_le (N : Nat) : (kOf N).toNat ≤ 39 := by
  unfold kOf
  have : (UInt32.ofNat (39 - (decDigits N).length)).toNat ≤ 39 := by simp; omega
  rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; simpa using this)]
  simp

theorem newCap_le (N : Nat) : (newCap 0 (kOf N)).toNat ≤ 128 := by
  have := kOf_le N
  unfold newCap
  split <;> simp_all <;> omega

/-! ## Resources -/

section Res

variable {GF : BundledGFunctors} [WasmGS NearState GF]

theorem stk4_word (n a : Nat) : stk (GF := GF) n a 4 ⊢ ∃ w : UInt32, n ↦[i32][ a ] w := by
  iintro H
  icases stk_bytes' $$ H with ⟨%bs, %hbs, H⟩
  iexists UInt32.ofNat (Memory.decodeLE bs)
  rw [ResultExpect.bytes32_decode bs hbs]
  iexact H

/-- The live blocks start at least 8 bytes in (after a cell header). -/
theorem heapInv_live8 (n maxP len : Nat) (live : List (Nat × Nat)) (F : Nat) :
    heapInv (GF := GF) n maxP len live F ⊢
      ⌜∀ p s, (p, s) ∈ live → 8 ≤ p⌝ ∗ heapInv n maxP len live F := by
  iintro H
  iunfold heapInv at H
  icases H with ⟨%M, %⟨hw, hl⟩, Hh, Hl, Hm, Hc⟩
  isplitr
  · ipureintro
    intro p s hps
    obtain ⟨-, c, -, -, hp, -⟩ := hw.lives.live_cell p s hps
    omega
  iunfold heapInv
  iexists M
  iframe Hh Hl Hm Hc
  ipureintro; exact ⟨hw, hl⟩

/-- The vtable words and table entries of the four methods the interface is used for
(`register_len`, `value_return`, `storage_read`, `read_register`), from the data segment and
the table. -/
noncomputable def vtab (n ta : Nat) (A : Nat → Nat) : IProp GF :=
  iprop(n ↦[wms][ 1050188 + 16 ] dataWord (1050188 + 16) ∗ ta ↦[wt][ 39 ] Ref.func (A 241) ∗
    n ↦[wms][ 1050188 + 92 ] dataWord (1050188 + 92) ∗ ta ↦[wt][ 58 ] Ref.func (A 260) ∗
    n ↦[wms][ 1050188 + 188 ] dataWord (1050188 + 188) ∗ ta ↦[wt][ 82 ] Ref.func (A 284) ∗
    n ↦[wms][ 1050188 + 12 ] dataWord (1050188 + 12) ∗ ta ↦[wt][ 38 ] Ref.func (A 240))

/-- The code of the prologue's calls (persistent). -/
def codeA (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) : IProp GF :=
  iprop(A 522 ↪[wf] FuncInst.wasm types[21]! inst f522 ∗ A 503 ↪[wf] FuncInst.wasm types[13]! inst f503 ∗
    A 508 ↪[wf] FuncInst.wasm types[31]! inst f508 ∗ A 509 ↪[wf] FuncInst.wasm types[45]! inst f509 ∗
    A 822 ↪[wf] FuncInst.wasm types[14]! inst f822 ∗
    A 520 ↪[wf] FuncInst.wasm types[14]! inst f520 ∗ A 463 ↪[wf] FuncInst.wasm types[31]! inst f463 ∗
    A 565 ↪[wf] FuncInst.wasm types[1]! inst f565 ∗ A 468 ↪[wf] FuncInst.wasm types[13]! inst f468 ∗
    A 467 ↪[wf] FuncInst.wasm types[13]! inst f467 ∗ A 564 ↪[wf] FuncInst.wasm types[0]! inst f564 ∗
    A 441 ↪[wf] FuncInst.wasm types[31]! inst f441 ∗ A 492 ↪[wf] FuncInst.wasm types[32]! inst f492 ∗
    A 672 ↪[wf] FuncInst.wasm types[13]! inst f672 ∗ A 464 ↪[wf] FuncInst.wasm types[0]! inst f464 ∗
    A 442 ↪[wf] FuncInst.wasm types[0]! inst f442 ∗ A 433 ↪[wf] FuncInst.wasm types[0]! inst f433 ∗
    inst ↪[inst] mi)

instance (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) : Persistent (codeA (GF := GF) inst mi A) := by
  unfold codeA; infer_instance

end Res

/-! ## Segment A: the prologue, `setup_panic_hook`, `set_blockchain_interface` -/

section SegA

variable {GF : BundledGFunctors} [WasmGS NearState GF]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- The prologue (`sp0 = s - 144`), `setup_panic_hook` (522) and `set_blockchain_interface(1,
1050188)` (520), in the 80 bytes below `sp0`: the interface installed (`ifaceR`). 475
`regular_op_cost`s. -/
theorem segA (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat)
    (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 7 < lim.maxCallDepth) (Cg R : Nat) (gt : GlobalType)
    (s : UInt32) (hs : 736 ≤ s.toNat) (hal : s.toNat % 8 = 0) (old k3 : UInt32) (rest : List Instr)
    (Φ : Post NearState GF) :
    codeA inst mi A ∗ credits Cg (475 * cfg.regularOpCost + R) ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
      stk n (s.toNat - 224) 80 ∗ hookCells n 0 old 0 ∗ n ↦[i32][ 1055020 ] 116 ∗
      ta ↦[wt][ 116 ] Ref.func (A 565) ∗ ta ↦[wt][ 106 ] Ref.func (A 564) ∗
      blockchainInterfaceCells n 0 0 0 k3 ∗ vtab n ta A ∗
      (credits Cg R -∗ g ↦[wg] ⟨gt, .i32 (s - 144)⟩ -∗ stk n (s.toNat - 224) 80 -∗ ifaceR n ta A -∗
        mwpi cfg lim d ⟨#[.i32 (s - 144)], inst, mi⟩ [] rest Φ)
      ⊢ mwpi cfg lim d ⟨#[.i32 0], inst, mi⟩ [] (bodyA ++ rest) Φ := by
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
  have e0 : (s - 144).toNat = s.toNat - 144 := by rw [tsub _ _ (by simp; omega)]; simp
  have e1 : (s - 144 - 16).toNat = s.toNat - 160 := by rw [tsub _ _ (by simp [e0]; omega), e0]; simp; omega
  have e2 : (s - 144 - 16 - 16).toNat = s.toNat - 176 := by rw [tsub _ _ (by simp [e1]; omega), e1]; simp; omega
  have e3 : (s - 144 - 32).toNat = s.toNat - 176 := by rw [tsub _ _ (by simp [e0]; omega), e0]; simp; omega
  have e4 : (s - 144 - 32 - 48).toNat = s.toNat - 224 := by rw [tsub _ _ (by simp [e3]; omega), e3]; simp; omega
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
  simp only [bodyA]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  -- setup_panic_hook
  mcall (SetupPanicHook.f522_spec cfg lim (d + 1) types[21]! rfl inst mi n g (A 503) (A 508) (A 509) (A 822)
      hn hg (hm.funcs 503 (by decide)) (hm.funcs 508 (by decide)) (hm.funcs 509 (by decide))
      (hm.funcs 822 (by decide)) types[13]! types[31]! types[45]! types[14]! rfl rfl rfl rfl rfl rfl rfl rfl
      (by omega) Cg ⟨gt, .i32 (s - 144)⟩ (s - 144) u72 u76 u56 u60 old rfl (by omega))
    using [Hg U72 U76 U56 U60 HH]
  · iunfold SetupPanicHook.pre
    ihave U72 := memBytes_addr (b := (s - 144 - 16).toNat + 8) (by omega) $$ U72
    ihave U76 := memBytes_addr (b := (s - 144 - 16).toNat + 12) (by omega) $$ U76
    ihave U56 := memBytes_addr (b := (s - 144 - 16 - 16).toNat + 8) (by omega) $$ U56
    ihave U60 := memBytes_addr (b := (s - 144 - 16 - 16).toNat + 12) (by omega) $$ U60
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
      rfl rfl rfl rfl rfl rfl rfl rfl (by omega) Cg ⟨gt, .i32 (s - 144)⟩ (s - 144) rfl (by omega) (by omega)
      1 1050188 k3 1 0 u64 u68 1 0 w0 w4 w8 w16 w20 w24 w28)
    using [Hg Hkey T116 T106 HB U56 U60 U64 U68 U72 U76 W0 W4 W8 W16 W20 W24 W28]
  · iunfold SetBlockchainInterface.pre, frames
    ihave U56 := memBytes_addr (b := (s - 144 - 32).toNat + 8) (by omega) $$ U56
    ihave U60 := memBytes_addr (b := (s - 144 - 32).toNat + 12) (by omega) $$ U60
    ihave U64 := memBytes_addr (b := (s - 144 - 32).toNat + 16) (by omega) $$ U64
    ihave U68 := memBytes_addr (b := (s - 144 - 32).toNat + 20) (by omega) $$ U68
    ihave U72 := memBytes_addr (b := (s - 144 - 32).toNat + 24) (by omega) $$ U72
    ihave U76 := memBytes_addr (b := (s - 144 - 32).toNat + 28) (by omega) $$ U76
    ihave W0 := memBytes_addr (b := (s - 144 - 32 - 48).toNat) (by omega) $$ W0
    ihave W4 := memBytes_addr (b := (s - 144 - 32 - 48).toNat + 4) (by omega) $$ W4
    ihave W8 := memBytes_addr (b := (s - 144 - 32 - 48).toNat + 8) (by omega) $$ W8
    ihave W16 := memBytes_addr (b := (s - 144 - 32 - 48).toNat + 16) (by omega) $$ W16
    ihave W20 := memBytes_addr (b := (s - 144 - 32 - 48).toNat + 20) (by omega) $$ W20
    ihave W24 := memBytes_addr (b := (s - 144 - 32 - 48).toNat + 24) (by omega) $$ W24
    ihave W28 := memBytes_addr (b := (s - 144 - 32 - 48).toNat + 28) (by omega) $$ W28
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
  ihave W0 := stkW (b := s.toNat - 224) _ (by omega) $$ W0
  ihave W4 := stkW (b := s.toNat - 224 + 4) _ (by omega) $$ W4
  ihave W8 := stkW (b := s.toNat - 224 + 4 + 4) _ (by omega) $$ W8
  ihave W16 := stkW (b := s.toNat - 224 + 4 + 4 + 4 + 4) _ (by omega) $$ W16
  ihave W20 := stkW (b := s.toNat - 224 + 4 + 4 + 4 + 4 + 4) _ (by omega) $$ W20
  ihave W24 := stkW (b := s.toNat - 224 + 4 + 4 + 4 + 4 + 4 + 4) _ (by omega) $$ W24
  ihave W28 := stkW (b := s.toNat - 224 + 4 + 4 + 4 + 4 + 4 + 4 + 4) _ (by omega) $$ W28
  ihave U56 := stkW (b := s.toNat - 224 + 56) _ (by omega) $$ U56
  ihave U60 := stkW (b := s.toNat - 224 + 60) _ (by omega) $$ U60
  ihave U64 := stkW (b := s.toNat - 224 + 64) _ (by omega) $$ U64
  ihave U68 := stkW (b := s.toNat - 224 + 68) _ (by omega) $$ U68
  ihave U72 := stkW (b := s.toNat - 224 + 72) _ (by omega) $$ U72
  ihave U76 := stkW (b := s.toNat - 224 + 76) _ (by omega) $$ U76
  ihave L := stkJ (a := s.toNat - 224 + 72) (b := s.toNat - 224 + 76) (k1 := 4) (k2 := 4) (k := 8) (by omega) rfl $$ [U72 U76]
  · iframe U72 U76
  ihave L := stkJ (a := s.toNat - 224 + 68) (b := s.toNat - 224 + 72) (k1 := 4) (k2 := 8) (k := 12) (by omega) rfl $$ [U68 L]
  · iframe U68 L
  ihave L := stkJ (a := s.toNat - 224 + 64) (b := s.toNat - 224 + 68) (k1 := 4) (k2 := 12) (k := 16) (by omega) rfl $$ [U64 L]
  · iframe U64 L
  ihave L := stkJ (a := s.toNat - 224 + 60) (b := s.toNat - 224 + 64) (k1 := 4) (k2 := 16) (k := 20) (by omega) rfl $$ [U60 L]
  · iframe U60 L
  ihave L := stkJ (a := s.toNat - 224 + 56) (b := s.toNat - 224 + 60) (k1 := 4) (k2 := 20) (k := 24) (by omega) rfl $$ [U56 L]
  · iframe U56 L
  ihave L := stkJ (a := s.toNat - 224 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4) (b := s.toNat - 224 + 56) (k1 := 24) (k2 := 24) (k := 48) (by omega) rfl $$ [M32 L]
  · iframe M32 L
  ihave L := stkA (b := s.toNat - 224 + 32) (by omega) $$ L
  ihave L := stkJ (a := s.toNat - 224 + 4 + 4 + 4 + 4 + 4 + 4 + 4) (b := s.toNat - 224 + 32) (k1 := 4) (k2 := 48) (k := 52) (by omega) rfl $$ [W28 L]
  · iframe W28 L
  ihave L := stkA (b := s.toNat - 224 + 28) (by omega) $$ L
  ihave L := stkJ (a := s.toNat - 224 + 4 + 4 + 4 + 4 + 4 + 4) (b := s.toNat - 224 + 28) (k1 := 4) (k2 := 52) (k := 56) (by omega) rfl $$ [W24 L]
  · iframe W24 L
  ihave L := stkA (b := s.toNat - 224 + 24) (by omega) $$ L
  ihave L := stkJ (a := s.toNat - 224 + 4 + 4 + 4 + 4 + 4) (b := s.toNat - 224 + 24) (k1 := 4) (k2 := 56) (k := 60) (by omega) rfl $$ [W20 L]
  · iframe W20 L
  ihave L := stkA (b := s.toNat - 224 + 20) (by omega) $$ L
  ihave L := stkJ (a := s.toNat - 224 + 4 + 4 + 4 + 4) (b := s.toNat - 224 + 20) (k1 := 4) (k2 := 60) (k := 64) (by omega) rfl $$ [W16 L]
  · iframe W16 L
  ihave L := stkA (b := s.toNat - 224 + 16) (by omega) $$ L
  ihave L := stkJ (a := s.toNat - 224 + 4 + 4 + 4) (b := s.toNat - 224 + 16) (k1 := 4) (k2 := 64) (k := 68) (by omega) rfl $$ [X12 L]
  · iframe X12 L
  ihave L := stkA (b := s.toNat - 224 + 12) (by omega) $$ L
  ihave L := stkJ (a := s.toNat - 224 + 4 + 4) (b := s.toNat - 224 + 12) (k1 := 4) (k2 := 68) (k := 72) (by omega) rfl $$ [W8 L]
  · iframe W8 L
  ihave L := stkA (b := s.toNat - 224 + 8) (by omega) $$ L
  ihave L := stkJ (a := s.toNat - 224 + 4) (b := s.toNat - 224 + 8) (k1 := 4) (k2 := 72) (k := 76) (by omega) rfl $$ [W4 L]
  · iframe W4 L
  ihave L := stkA (b := s.toNat - 224 + 4) (by omega) $$ L
  ihave L := stkJ (a := s.toNat - 224) (b := s.toNat - 224 + 4) (k1 := 4) (k2 := 76) (k := 80) (by omega) rfl $$ [W0 L]
  · iframe W0 L
  mcredits R
  iapply W $$ Hc Hg L HI

end SegA

/-! ## Segment C: `expect`, `deref`, `value_return`, the drops, the epilogue -/

section SegC

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The code of segment C (persistent). -/
def codeC (e inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n : Nat) (mx : Option Nat) : IProp GF :=
  iprop(ifaceCode e inst mi A n mx ∗ dropCode inst mi A ∗ A 456 ↪[wf] FuncInst.wasm types[14]! inst f456 ∗
    A 158 ↪[wf] FuncInst.wasm types[31]! inst f158 ∗ A 779 ↪[wf] FuncInst.wasm types[14]! inst f779 ∗
    A 545 ↪[wf] FuncInst.wasm types[14]! inst f545 ∗ A 68 ↪[wf] FuncInst.wasm types[0]! inst f68)

instance (e inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n : Nat) (mx : Option Nat) :
    Persistent (codeC (GF := GF) e inst mi A n mx) := by
  unfold codeC; infer_instance

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- Segment C, from `to_vec`'s `Ok(vec)` at `sp0 + 72` (`vec = (q, 128, L)`, the bytes `bs` at `q`):
`expect` (158), `deref` (779), `value_return(q, L)` (545), the drops of the JSON `Vec` and of the
prefix's (68, twice), the epilogue. `1010` `regular_op_cost`s and `value_return`'s gas. -/
theorem segC (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (e inst : Nat) (mi : ModuleInst) (A : Nat → Nat)
    (n g ta : Nat) (mx : Option Nat) (hm : IfaceMod mi A n g ta) (hd : d + 8 < lim.maxCallDepth)
    (Cg R : Nat) (gt : GlobalType) (s : UInt32) (hs : 736 ≤ s.toNat) (hal : s.toNat % 8 = 0)
    (q L p : UInt32) (bs rest : List UInt8) (hbs : bs.length = L.toNat) (hpos : 0 < L.toNat)
    (hrest : bs.length + rest.length = 128) (maxP hl F : Nat) (h1 : NearState)
    (hlim : withinLimit h1.config.maxReturnLen L.toNat = true) (Φ : Post NearState GF) :
    codeC e inst mi A n mx ∗ credits Cg (1010 * cfg.regularOpCost + valueReturnUse h1 L.toNat + R) ∗
      g ↦[wg] ⟨gt, .i32 (s - 144)⟩ ∗ ifaceR n ta A ∗ stk n (s.toNat - 224) 80 ∗ stk n (s.toNat - 136) 8 ∗
      n ↦[i32][ s.toNat - 72 ] 0 ∗ n ↦[i32][ s.toNat - 68 ] q ∗ n ↦[i32][ s.toNat - 64 ] 128 ∗
      n ↦[i32][ s.toNat - 60 ] L ∗ stk n (s.toNat - 16) 12 ∗
      n ↦[i32][ s.toNat - 88 ] p ∗ n ↦[i32][ s.toNat - 84 ] 1 ∗ n ↦[i32][ s.toNat - 80 ] 1 ∗
      n ↦[wms][ q.toNat ] (bs ++ rest) ∗ n ↦[wms][ p.toNat ] WNear.accountsPrefix ∗
      heapInv n maxP hl [(q.toNat, 128), (p.toNat, 1)] F ∗ mhostPt h1 ∗
      (credits Cg R -∗ g ↦[wg] ⟨gt, .i32 s⟩ -∗ mhostPt (h1.selectReturnValue bs) -∗
        Φ.normal [] ⟨#[.i32 (s - 144)], inst, mi⟩)
      ⊢ mwpi cfg lim d ⟨#[.i32 (s - 144)], inst, mi⟩ [] bodyC Φ := by
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
  have e0 : (s - 144).toNat = s.toNat - 144 := by rw [tsub _ _ (by simp; omega)]; simp
  have e1 : (s - 144 - 16).toNat = s.toNat - 160 := by rw [tsub _ _ (by simp [e0]; omega), e0]; simp; omega
  have e2 : (s - 144 - 16 - 16).toNat = s.toNat - 176 := by rw [tsub _ _ (by simp [e1]; omega), e1]; simp; omega
  have a128 : (s - 144 + 128).toNat = s.toNat - 16 := by simp [UInt32.toNat_add, e0]; omega
  have a72 : (s - 144 + 72).toNat = s.toNat - 72 := by simp [UInt32.toNat_add, e0]; omega
  have a8 : (s - 144 + 8).toNat = s.toNat - 136 := by simp [UInt32.toNat_add, e0]; omega
  have a56 : (s - 144 + 56).toNat = s.toNat - 88 := by simp [UInt32.toNat_add, e0]; omega
  have hLb : L.toNat ≤ 128 := by omega
  have hq := q.toNat_lt
  simp only [bodyC]
  -- expect(sp0 + 128, sp0 + 72, loc)
  ihave PL := join64' (a := s.toNat - 68) (b := s.toNat - 64) q 128 (by omega) $$ [R4 R8]
  · iframe R4 R8
  ihave PL := joinB (a := s.toNat - 68) (b := s.toNat - 60) (bytes32 q ++ bytes32 128) (bytes32 L)
    (by simp; omega) $$ [PL R12]
  · iframe PL R12
  icases stk_bytes' $$ F128 with ⟨%ob, %hob, F128⟩
  mstep; mstep; mstep; mstep; mstep; mstep; mstep
  mcall (ResultExpect.f158_spec cfg lim (d + 1) types[31]! rfl inst mi n g hn hg Cg ⟨gt, .i32 (s - 144)⟩
      (s - 144) (s - 144 + 128) (s - 144 + 72) 1050984 rfl (by omega) (by omega) (bytes32 0)
      (bytes32 q ++ bytes32 128 ++ bytes32 L) ob (by simp) (by simp) hob (by simp [decodeLE_bytes32]))
    using [Hg R0 PL F128]
  · iunfold ResultExpect.pre
    ihave R0 := memBytes_addr (b := (s - 144 + 72).toNat) (by omega) $$ R0
    ihave PL := memBytes_addr (b := (s - 144 + 72).toNat + 4) (by omega) $$ PL
    ihave F128 := memBytes_addr (b := (s - 144 + 128).toNat) (by omega) $$ F128
    iframe Hg R0 PL F128
    ipureintro; rfl
  iunfold ResultExpect.post at HQ
  icases HQ with ⟨%hrs, Hg, R0, PL, V128⟩
  subst hrs
  -- deref(sp0 + 8, sp0 + 128)
  icases stk_bytes' $$ F8 with ⟨%o8, %ho8, F8⟩
  mstep; mstep; mstep; mstep; mstep; mstep
  mcall (VecDeref.f779_spec cfg lim (d + 1) types[14]! rfl inst mi n hn Cg (s - 144 + 8) (s - 144 + 128) o8
      (bytes32 q ++ bytes32 128 ++ bytes32 L) ho8 (by simp)) using [F8 V128]
  · iunfold VecDeref.pre
    ihave F8 := memBytes_addr (b := (s - 144 + 8).toNat) (by omega) $$ F8
    iframe F8 V128
    ipureintro; rfl
  iunfold VecDeref.post at HQ
  icases HQ with ⟨%hrs, O8, V128⟩
  subst hrs
  have hvb : (bytes32 q ++ (bytes32 128 ++ bytes32 L)).take 4 ++ (bytes32 q ++ (bytes32 128 ++ bytes32 L)).drop 8 =
      bytes32 q ++ bytes32 L := by
    simp [List.take_append, List.drop_append, bytes32_length]
  rw [hvb]
  ihave O8 := memBytes_addr (b := s.toNat - 136) (by omega) $$ O8
  icases split64' (a := s.toNat - 136) (b := s.toNat - 132) q L (by omega) $$ O8 with ⟨O8, O12⟩
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
    ⟨gt, .i32 (s - 144)⟩ (s - 144) rfl (by omega) (by omega) h1 q L bs hbs hlim hpos x72 x76 x48 x52 x56 x60
    $$ []
  · iframe F456 HIC
  mcall S545 using [Hg HI X72 X76 X48 X52 X56 X60 Hb Hh]
  · iunfold ValueReturn.pre, frame4
    ihave X72 := memBytes_addr (b := (s - 144 - 16).toNat + 8) (by omega) $$ X72
    ihave X76 := memBytes_addr (b := (s - 144 - 16).toNat + 12) (by omega) $$ X76
    ihave X48 := memBytes_addr (b := (s - 144 - 16 - 16).toNat) (by omega) $$ X48
    ihave X52 := memBytes_addr (b := (s - 144 - 16 - 16).toNat + 4) (by omega) $$ X52
    ihave X56 := memBytes_addr (b := (s - 144 - 16 - 16).toNat + 8) (by omega) $$ X56
    ihave X60 := memBytes_addr (b := (s - 144 - 16 - 16).toNat + 12) (by omega) $$ X60
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
      [(q.toNat, 128), (p.toNat, 1)] F (s - 144 + 128) q 128 L (by decide) (by omega))
    using [V128 V132 V136 Hinv Hb Hr]
  · iunfold pre747
    ihave V128 := memBytes_addr (b := (s - 144 + 128).toNat) (by omega) $$ V128
    ihave V132 := memBytes_addr (b := (s - 144 + 128).toNat + 4) (by omega) $$ V132
    ihave V136 := memBytes_addr (b := (s - 144 + 128).toNat + 8) (by omega) $$ V136
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
      [(p.toNat, 1)] (F + 1) (s - 144 + 56) p 1 1 (by decide) (by omega))
    using [V0 V4 V8 Hinv Hp]
  · iunfold pre747
    ihave V0 := memBytes_addr (b := (s - 144 + 56).toNat) (by omega) $$ V0
    ihave V4 := memBytes_addr (b := (s - 144 + 56).toNat + 4) (by omega) $$ V4
    ihave V8 := memBytes_addr (b := (s - 144 + 56).toNat + 8) (by omega) $$ V8
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
  rw [show s - 144 + 144 = s by simp]
  mcredits R
  iapply W $$ Hc Hg Hh

end SegC

/-! ## Segment B: `state_read`, `unwrap_or_default`, the getter, the copy, `to_vec` -/

/-- The two words of the Borsh `u128` total supply of `S`. -/
def loOf (S : WNear.State) : UInt64 := UInt64.ofNat (Memory.decodeLE ((WNear.Borsh.u128 S.totalSupply).take 8))
def hiOf (S : WNear.State) : UInt64 := UInt64.ofNat (Memory.decodeLE ((WNear.Borsh.u128 S.totalSupply).drop 8))

theorem val_loOf (S : WNear.State) : val (loOf S) (hiOf S) = S.totalSupply % 2 ^ 128 := val_u128 _

/-- The cost of `state_read` on the model state `S` (`f219_spec_model`), activation excluded. -/
def cost219 (cfg : WasmConfig) (h : NearState) (S : WNear.State) : Nat :=
  105 * cfg.regularOpCost +
    (40 * cfg.regularOpCost + (249 * cfg.regularOpCost + storageReadUse h StateRead.stateKey 5) +
      StorageReadWrap.costS cfg h (some (WNear.header S))) +
    BorshContract.cost161 cfg 1 + 726 * cfg.regularOpCost + 334 * cfg.regularOpCost

/-- `serde_json::to_vec::<U128>` (96)
as `ToVec.f96_spec` states it, but from a heap whose free list may hold two cells
(`heapInv … 2`, what `state_read` leaves after freeing the value's buffer), at an extra cost
`x96`; the heap after it is `heapInv … F'` for some `F'`. Proved for `x96 = 0`:
`ToVecTwo.toVecAfterFree_zero`. -/
def ToVecAfterFree (cfg : WasmConfig) (lim : ExecLimits) (x96 : Nat) : Prop :=
  ∀ {GF : BundledGFunctors} [WasmGS NearState GF] (d : Nat) (type : FuncType), type.results = [] →
    ∀ (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat), IfaceMod mi A n g ta →
    d + 27 < lim.maxCallDepth → ∀ (Cg : Nat) (gt : GlobalType) (s out v ptr0 aidx : UInt32) (ob : List UInt8)
    (maxP hl : Nat) (live : List (Nat × Nat)) (lo hi : UInt64), 416 ≤ s.toNat → ob.length = 16 →
    out.toNat + 16 ≤ 2 ^ 32 → v.toNat + 16 ≤ 2 ^ 32 → roomFor hl maxP 128 →
    (∀ hl1, hl1 = hl ∨ hl1 = grownLen hl 128 → roomFor hl1 maxP (newCap 0 (kOf (val lo hi)))) →
    (tvCode n maxP inst mi A ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f96 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 v]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 416) 416 ∗
          n ↦[wms][ out.toNat ] ob ∗ n ↦[wms][ v.toNat ] u128Bytes lo hi ∗ tvData n ta ptr0 (A 759) (A 353) ∗
          vt n 1057464 aidx ta (A 578) ∗ heapInv n maxP hl live 2))
        (fun _ => cost96 cfg lo hi + x96)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 416) 416 ∗
          n ↦[wms][ v.toNat ] u128Bytes lo hi ∗ tvData n ta ptr0 (A 759) (A 353) ∗ vt n 1057464 aidx ta (A 578) ∗
          ∃ q : UInt32, ∃ rest : List UInt8, ⌜rest.length = 128 - ((kOf (val lo hi)).toNat + 2)⌝ ∗
            n ↦[i32][ out.toNat ] 0 ∗ n ↦[i32][ out.toNat + 4 ] q ∗ n ↦[i32][ out.toNat + 8 ] 128 ∗
            n ↦[i32][ out.toNat + 12 ] (0 + kOf (val lo hi) + 2) ∗
            n ↦[wms][ q.toNat ] (([34] ++ decDigits (val lo hi) ++ [34]) ++ rest) ∗
            ∃ hl' F', heapInv n maxP hl' ((q.toNat, 128) :: live) F')))

section SegB

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The code of segment B (persistent). -/
def codeB (e inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n maxP : Nat) : IProp GF :=
  iprop(stateCode e inst mi A n maxP (some maxP) ∗ tvCode n maxP inst mi A ∗
    A 219 ↪[wf] FuncInst.wasm types[0]! inst f219 ∗ A 155 ↪[wf] FuncInst.wasm types[14]! inst f155 ∗
    A 951 ↪[wf] FuncInst.wasm types[15]! inst f951 ∗ A 414 ↪[wf] FuncInst.wasm types[14]! inst f414 ∗
    A 566 ↪[wf] FuncInst.wasm types[4]! inst f566 ∗ A 96 ↪[wf] FuncInst.wasm types[14]! inst f96 ∗
    inst ↪[inst] mi)

instance (e inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n maxP : Nat) :
    Persistent (codeB (GF := GF) e inst mi A n maxP) := by
  unfold codeB; infer_instance

theorem contractBytes_split (S : WNear.State) (p : UInt32) (pad : List UInt8) :
    contractBytes S p ++ pad =
      WNear.Borsh.u128 S.totalSupply ++ (WNear.Borsh.u64 S.accountStorageUsage ++
        (bytes32 p ++ (bytes32 1 ++ (bytes32 1 ++ pad)))) := by
  simp [contractBytes]

theorem u128_length (N : Nat) : (WNear.Borsh.u128 N).length = 16 := by simp [NearSdk.Borsh.u128]
theorem u64_length (N : Nat) : (WNear.Borsh.u64 N).length = 8 := by simp [NearSdk.Borsh.u64]

theorem contractBytes_length (S : WNear.State) (p : UInt32) : (contractBytes S p).length = 36 := by
  simp [contractBytes, u128_length, u64_length]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
open Near.TrieAccounting Near.TrieConstruction Near.TrieOverlay in
/-- Segment B: `state_read` (219) on the model state `S`, `unwrap_or_default` (155), the getter
(414), the copy of the `u128` to `sp0 + 112`, `to_vec` (96, assumed on the heap `state_read`
leaves). -/
theorem segB (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (e inst : Nat) (mi : ModuleInst) (A : Nat → Nat)
    (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 28 < lim.maxCallDepth) (x96 : Nat)
    (H96 : ToVecAfterFree cfg lim x96) (Cg R : Nat) (gt : GlobalType) (s : UInt32) (hs : 736 ≤ s.toNat)
    (hal : s.toNat % 8 = 0) (idx ptr0 : UInt32) (maxP len : Nat) (hroom : HeapRoom len maxP)
    (h : NearState) (S : WNear.State)
    (hv : h.storage WNear.stateKey = some (WNear.header S))
    (st : Near.TrieOverlay.State) (hacc : h.storageAccounting = some st)
    (hlim : withinLimit h.config.maxStorageKeyLen 5 = true)
    (hb : build st.entries = .ok st.base) (hz : zeroHash ∉ st.base.witness.map Prod.fst)
    (hlink : h.storage WNear.stateKey = viewVal st (contractKey h.context.currentAccountId WNear.stateKey))
    (hproof : ProofBudget h st (lookupProofBound (contractKey h.context.currentAccountId WNear.stateKey))) (hreg : withinLimit h.config.maxRegisterLen 29 = true)
    (rest : List Instr) (Φ : Post NearState GF) :
    codeB e inst mi A n maxP ∗
      credits Cg (864 * cfg.regularOpCost + cost219 cfg h S + (cost96 cfg (loOf S) (hiOf S) + x96) + R) ∗
      g ↦[wg] ⟨gt, .i32 (s - 144)⟩ ∗ ifaceR n ta A ∗ stk n (s.toNat - 736) 592 ∗
      stk n (s.toNat - 128) 16 ∗ stk n (s.toNat - 112) 40 ∗ stk n (s.toNat - 72) 40 ∗ stk n (s.toNat - 32) 16 ∗
      vt n 1057464 idx ta (A 578) ∗ heapInv n maxP len [] 1 ∗ n ↦[wms][ 1049788 ] StateRead.stateKey ∗
      tvData n ta ptr0 (A 759) (A 353) ∗ mhostPt h ∗
      (∀ (q p : UInt32) (rst : List UInt8) (hl F : Nat) (h1 : NearState),
        ⌜StorageReadPost h StateRead.stateKey 0 st h1 ∧
          rst.length = 128 - ((kOf (val (loOf S) (hiOf S))).toNat + 2)⌝ -∗
        credits Cg R -∗ g ↦[wg] ⟨gt, .i32 (s - 144)⟩ -∗ ifaceR n ta A -∗ stk n (s.toNat - 224) 80 -∗
        n ↦[i32][ s.toNat - 72 ] 0 -∗ n ↦[i32][ s.toNat - 68 ] q -∗ n ↦[i32][ s.toNat - 64 ] 128 -∗
        n ↦[i32][ s.toNat - 60 ] (0 + kOf (val (loOf S) (hiOf S)) + 2) -∗
        n ↦[i32][ s.toNat - 88 ] p -∗ n ↦[i32][ s.toNat - 84 ] 1 -∗ n ↦[i32][ s.toNat - 80 ] 1 -∗
        n ↦[wms][ q.toNat ] (jsonOf (val (loOf S) (hiOf S)) ++ rst) -∗
        n ↦[wms][ p.toNat ] WNear.accountsPrefix -∗
        heapInv n maxP hl [(q.toNat, 128), (p.toNat, 1)] F -∗ mhostPt h1 -∗
        mwpi cfg lim d ⟨#[.i32 (s - 144)], inst, mi⟩ [] rest Φ)
      ⊢ mwpi cfg lim d ⟨#[.i32 (s - 144)], inst, mi⟩ [] (bodyB ++ rest) Φ := by
  iintro ⟨#Hk, Hc, Hg, HI, Lo, F16, F32, F72, F112, Hvt, Hinv, Hkey, HT, Hh, W⟩
  ihave #Hk' := Hk
  iunfold codeB at Hk'
  icases Hk' with ⟨#HSC, #HTV, #F219, #F155, #F951, #F414, #F566, #F96, #Hi⟩
  unfold cost219
  have hn := hm.mem
  have hg := hm.glob
  have ha219 := hm.funcs 219 (by decide)
  have ha155 := hm.funcs 155 (by decide)
  have ha414 := hm.funcs 414 (by decide)
  have ha96 := hm.funcs 96 (by decide)
  have t0 : types[0]!.params.length = 1 := rfl
  have t14 : types[14]!.params.length = 2 := rfl
  have hlt := s.toNat_lt
  obtain ⟨r1, r2, r3, r4⟩ := hroom
  have e0 : (s - 144).toNat = s.toNat - 144 := by rw [tsub _ _ (by simp; omega)]; simp
  have e1 : (s - 144 - 16).toNat = s.toNat - 160 := by rw [tsub _ _ (by simp [e0]; omega), e0]; simp; omega
  have a72 : (s - 144 + 72).toNat = s.toNat - 72 := by simp [UInt32.toNat_add, e0]; omega
  have a32 : (s - 144 + 32).toNat = s.toNat - 112 := by simp [UInt32.toNat_add, e0]; omega
  have a16 : (s - 144 + 16).toNat = s.toNat - 128 := by simp [UInt32.toNat_add, e0]; omega
  have a24 : (s - 144 + 24).toNat = s.toNat - 120 := by simp [UInt32.toNat_add, e0]; omega
  have a112 : (s - 144 + 112).toNat = s.toNat - 32 := by simp [UInt32.toNat_add, e0]; omega
  iapply mwpi_seq
  simp only [bodyB]
  -- state_read(sp0 + 72)
  icases stk_bytes' $$ F72 with ⟨%ob, %hob, F72⟩
  mstep; mstep; mstep
  mcall (f219_spec_model_len cfg lim (d + 1) types[0]! rfl inst mi e A n g ta (some maxP) hm (by omega) Cg gt
      (s - 144) (s - 144 + 72) (by omega) (by omega) (by omega) idx maxP len [] ob hob h S hv
      (roomFor_of len maxP len 29 (by decide) ⟨r1, r2, r3, r4⟩ (by omega) (by omega) r1)
      (by
        intro l hl
        rw [grownLen_small _ _ (by decide)] at hl
        exact roomFor_of len maxP l 1 (by decide) ⟨r1, r2, r3, r4⟩ (by omega) (by omega) (by omega))
      st hacc hlim hb hz hlink hproof hreg)
    using [Hg HI Lo Hvt Hinv F72 Hkey Hh]
  · iunfold pre219
    ihave Lo := stkA (b := (s - 144).toNat - 592) (by omega) $$ Lo
    ihave F72 := memBytes_addr (b := (s - 144 + 72).toNat) (by omega) $$ F72
    iframe Hg HI Lo Hvt Hinv F72 Hkey Hh
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
  -- unwrap_or_default(sp0 + 32, sp0 + 72)
  icases stk_bytes' $$ F32 with ⟨%ob32, %hob32, F32⟩
  have hsb : (contractBytes S p ++ pad).length = 40 := by rw [List.length_append, contractBytes_length, hpad]
  have hniche : ((contractBytes S p ++ pad).drop 24).take 4 = bytes32 p := by
    rw [contractBytes_split]; simp [List.drop_append, List.take_append, u128_length, u64_length]
  mstep; mstep; mstep; mstep; mstep; mstep
  mcall (UnwrapOrDefault.f155_spec cfg lim (d + 1) types[14]! rfl inst mi n (A 951) hn (hm.funcs 951 (by decide))
      types[15]! rfl rfl (by omega) Cg (s - 144 + 32) (s - 144 + 72) (by omega) (by omega) ob32
      (contractBytes S p ++ pad) hob32 hsb (by rw [hniche, decodeLE_bytes32]; omega))
    using [F32 Hopt]
  · iunfold UnwrapOrDefault.pre
    ihave F32 := memBytes_addr (b := (s - 144 + 32).toNat) (by omega) $$ F32
    iframe F32 Hopt
    ipureintro; rfl
  iunfold UnwrapOrDefault.post at HQ
  icases HQ with ⟨%hrs, C32, Hopt⟩
  subst hrs
  -- the getter: ft_total_supply(sp0 + 16, sp0 + 32)
  rw [contractBytes_split]
  ihave C32 := memBytes_addr (b := s.toNat - 112) (by omega) $$ C32
  icases splitB (a := s.toNat - 112) (b := s.toNat - 96) (WNear.Borsh.u128 S.totalSupply) _
    (by rw [u128_length]; omega) $$ C32 with ⟨T32, C48⟩
  icases stkSp 576 16 rfl $$ Lo with ⟨Lo, FB⟩
  icases stk_bytes' $$ FB with ⟨%fb, %hfb, FB⟩
  icases stk_bytes' $$ F16 with ⟨%ob16, %hob16, F16⟩
  mstep; mstep; mstep; mstep; mstep; mstep
  mcall (FtTotalSupplyGetter.f414_spec cfg lim (d + 1) types[14]! rfl inst mi n g (A 566) hn hg
      (hm.funcs 566 (by decide)) types[4]! rfl rfl (by omega) Cg ⟨gt, .i32 (s - 144)⟩ (s - 144) (s - 144 + 16)
      (s - 144 + 32) rfl (by omega) (by omega) fb ob16 (WNear.Borsh.u128 S.totalSupply) hfb hob16 (u128_length _))
    using [Hg FB F16 T32]
  · iunfold FtTotalSupplyGetter.pre
    ihave FB := memBytes_addr (b := (s - 144 - 16).toNat) (by omega) $$ FB
    ihave F16 := memBytes_addr (b := (s - 144 + 16).toNat) (by omega) $$ F16
    ihave T32 := memBytes_addr (b := (s - 144 + 32).toNat) (by omega) $$ T32
    iframe Hg FB F16 T32
    ipureintro; rfl
  iunfold FtTotalSupplyGetter.post at HQ
  icases HQ with ⟨%hrs, Hg, FB, T16, -⟩
  subst hrs
  -- the copy: [sp0 + 120] := [sp0 + 24]; [sp0 + 112] := [sp0 + 16]
  ihave T16 := memBytes_addr (b := s.toNat - 128) (by omega) $$ T16
  icases U128From.memBytes_split n (s.toNat - 128) 8 (WNear.Borsh.u128 S.totalSupply) (by rw [u128_length]; omega)
    $$ T16 with ⟨T16a, T16b⟩
  have hne1 : (WNear.Borsh.u128 S.totalSupply).take 8 ≠ [] := by
    intro h0; have := congrArg List.length h0; simp [u128_length] at this
  have hne2 : (WNear.Borsh.u128 S.totalSupply).drop 8 ≠ [] := by
    intro h0; have := congrArg List.length h0; simp [u128_length] at this
  icases stkSp 8 8 rfl $$ F112 with ⟨Z0, Z8⟩
  icases stk_bytes' $$ Z0 with ⟨%z0, %hz0, Z0⟩
  icases stk_bytes' $$ Z8 with ⟨%z8, %hz8, Z8⟩
  mstep; mstep; mstep; mstep; mstep [T16b] with (simp [u128_length]); mstep [Z8]
  mstep; mstep; mstep [T16a] with (simp [u128_length]); mstep [Z0]
  -- to_vec(sp0 + 72, sp0 + 112)
  ihave V := joinB (a := s.toNat - 32) (b := s.toNat - 32 + 8)
    (storeBytes (Value.i64 (UInt64.ofNat (Memory.decodeLE (List.take 8 (WNear.Borsh.u128 S.totalSupply))))) 8)
    (storeBytes (Value.i64 (UInt64.ofNat (Memory.decodeLE (List.drop 8 (WNear.Borsh.u128 S.totalSupply))))) 8)
    (by simp) $$ [Z0 Z8]
  · iframe Z0 Z8
  ihave Hopt := memBytes_addr (b := s.toNat - 72) (by omega) $$ Hopt
  icases splitB (a := s.toNat - 72) (b := s.toNat - 56) (WNear.Borsh.u128 S.totalSupply) _
    (by rw [u128_length]; omega) $$ Hopt with ⟨O72, -⟩
  ihave FB := stkB (b := (s - 144).toNat - 592 + 576) _ (by omega) (u128_length _) $$ FB
  ihave Lo := stkJ (a := (s - 144).toNat - 592) (b := (s - 144).toNat - 592 + 576) (k1 := 576) (k2 := 16)
    (k := 592) rfl rfl $$ [Lo FB]
  · iframe Lo FB
  icases stkSp 176 416 rfl $$ Lo with ⟨-, Lo⟩
  have hr1 : roomFor len' maxP 128 := roomFor_of len maxP len' 128 (by decide) ⟨r1, r2, r3, r4⟩ hl1 (by omega) hl3
  have hr2 : ∀ l, l = len' ∨ l = grownLen len' 128 →
      roomFor l maxP (newCap 0 (kOf (val (loOf S) (hiOf S)))) := by
    intro l hl
    rw [grownLen_small _ _ (by decide)] at hl
    exact roomFor_of len maxP l _ (newCap_le _) ⟨r1, r2, r3, r4⟩ (by omega) (by omega) (by omega)
  ihave #S96 := H96 (GF := GF) (d + 1) types[14]! rfl inst mi A n g ta hm (by omega) Cg gt (s - 144) (s - 144 + 72)
    (s - 144 + 112) ptr0 idx (WNear.Borsh.u128 S.totalSupply) maxP len' [(p.toNat, 1)] (loOf S) (hiOf S)
    (by omega) (u128_length _) (by omega) (by omega) hr1 hr2 $$ HTV
  mstep; mstep; mstep; mstep; mstep; mstep
  mcall S96 using [Hg Lo O72 V HT Hvt Hinv]
  · ihave Lo := stkA (b := (s - 144).toNat - 416) (by omega) $$ Lo
    ihave O72 := memBytes_addr (b := (s - 144 + 72).toNat) (by omega) $$ O72
    ihave V := memBytes_addr (b := (s - 144 + 112).toNat) (by omega) $$ V
    iframe Hg Lo O72 HT Hvt Hinv
    have hu : u128Bytes (loOf S) (hiOf S) =
        storeBytes (Value.i64 (UInt64.ofNat (Memory.decodeLE (List.take 8 (WNear.Borsh.u128 S.totalSupply))))) 8 ++
        storeBytes (Value.i64 (UInt64.ofNat (Memory.decodeLE (List.drop 8 (WNear.Borsh.u128 S.totalSupply))))) 8 :=
      rfl
    rw [← hu]
    iexact V
  icases HQ with ⟨%hrs, Hg, Lo, -, -, -, %q, %rst, %hrst, R0, R4, R8, R12, Hq, %hl', %F', Hinv⟩
  subst hrs
  -- hand over to segment C
  ihave Lo := stkA (b := s.toNat - 560) (by omega) $$ Lo
  icases stkSp 336 80 rfl $$ Lo with ⟨-, Lo⟩
  ihave Lo := stkA (b := s.toNat - 224) (by omega) $$ Lo
  ihave R0 := memBytes_addr (b := s.toNat - 72) (by omega) $$ R0
  ihave R4 := memBytes_addr (b := s.toNat - 68) (by omega) $$ R4
  ihave R8 := memBytes_addr (b := s.toNat - 64) (by omega) $$ R8
  ihave R12 := memBytes_addr (b := s.toNat - 60) (by omega) $$ R12
  icases splitB (a := s.toNat - 96) (b := s.toNat - 88) (WNear.Borsh.u64 S.accountStorageUsage) _
    (by rw [u64_length]; omega) $$ C48 with ⟨-, C56⟩
  icases splitB (a := s.toNat - 88) (b := s.toNat - 84) (bytes32 p) _ (by simp; omega) $$ C56 with ⟨V0, C60⟩
  icases splitB (a := s.toNat - 84) (b := s.toNat - 80) (bytes32 1) _ (by simp; omega) $$ C60 with ⟨V4, C64⟩
  icases splitB (a := s.toNat - 80) (b := s.toNat - 76) (bytes32 1) _ (by simp; omega) $$ C64 with ⟨V8, -⟩
  mcredits R
  iapply W $$ %q %p %rst %hl' %F' %h1 [] Hc Hg HI Lo R0 R4 R8 R12 V0 V4 V8 [Hq] Hp Hinv Hh
  · ipureintro; exact ⟨hq1, hrst⟩
  · ihave Hq := AllocNewCell.memBytes_eq (bs' := jsonOf (val (loOf S) (hiOf S)) ++ rst) (by simp [jsonOf]) $$ Hq
    iexact Hq

end SegB

/-! ## The method's body and `f296_spec` -/

/-- The JSON bytes of the model's total supply (as a `u128`). -/
def supplyJson (S : WNear.State) : List UInt8 := jsonOf (S.totalSupply % 2 ^ 128)

theorem supplyJson_eq (S : WNear.State) : supplyJson S = jsonOf (val (loOf S) (hiOf S)) := by
  rw [supplyJson, val_loOf]

/-- The cost of `ft_total_supply` (296), activation excluded: 2349 `regular_op_cost`s, `state_read`'s
storage and deserialisation (`cost219`), `to_vec` (`cost96` and the assumed `x96`), and
`value_return`'s gas. -/
noncomputable def cost296 (cfg : WasmConfig) (h : NearState) (S : WNear.State) (x96 : Nat) : Nat :=
  2349 * cfg.regularOpCost + cost219 cfg h S + (cost96 cfg (loOf S) (hiOf S) + x96) +
    valueReturnUse h (supplyJson S).length

open Near.TrieAccounting Near.TrieConstruction Near.TrieOverlay in
/-- What `ft_total_supply` needs of the host `h` (the storage premises of `storage_read`,
`f548_spec_host`, kept as hypotheses): `STATE` holds the model's `header S`; the accounting
state `st`, its trie canonical and linked to the storage through the overlay's view (`viewVal`), no
witness hashing to zero, room in the recorded proof for the lookup (`ProofBudget`, SAF-67); the key, register and return limits. -/
structure ReadOk (h : NearState) (S : WNear.State) (st : Near.TrieOverlay.State) : Prop where
  value : h.storage WNear.stateKey = some (WNear.header S)
  acc : h.storageAccounting = some st
  keyLen : withinLimit h.config.maxStorageKeyLen 5 = true
  trie : build st.entries = .ok st.base
  zero : zeroHash ∉ st.base.witness.map Prod.fst
  link : h.storage WNear.stateKey = viewVal st (contractKey h.context.currentAccountId WNear.stateKey)
  proof : ProofBudget h st (lookupProofBound (contractKey h.context.currentAccountId WNear.stateKey))
  regLen : withinLimit h.config.maxRegisterLen 29 = true
  retLen : withinLimit h.config.maxReturnLen (supplyJson S).length = true

/-- `storage_read` keeps the config, so the fees `value_return` pays. -/
theorem storageReadPost_config {h h1 : NearState} {key : List UInt8} {r : UInt64} {st : Near.TrieOverlay.State}
    (H : StorageReadPost h key r st h1) :
    h1.config = h.config ∧ ∀ k, valueReturnUse h1 k = valueReturnUse h k := by
  obtain ⟨s2, -, -, he⟩ := H
  have hc : (storageReadRegs { h with storageAccounting := some s2 } r (h.storage key)).config = h.config := by
    unfold storageReadRegs; split
    · split <;> rfl
    · rfl
  have hv : ∀ k, valueReturnUse (storageReadRegs { h with storageAccounting := some s2 } r (h.storage key)) k =
      valueReturnUse h k := by
    intro k; unfold storageReadRegs; split
    · split <;> rfl
    · rfl
  refine ⟨(erase_field he NearState.config fun _ => rfl).trans hc, fun k => ?_⟩
  rw [← hv k]
  exact erase_field he (fun x => valueReturnUse x k) fun _ => rfl

section Main

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The code `ft_total_supply` runs (persistent). -/
def code296 (e inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n maxP : Nat) : IProp GF :=
  iprop(codeA inst mi A ∗ codeB e inst mi A n maxP ∗ codeC e inst mi A n (some maxP))

instance (e inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n maxP : Nat) :
    Persistent (code296 (GF := GF) e inst mi A n maxP) := by
  unfold code296; infer_instance

/-- The statics a fresh instance holds that `ft_total_supply` owns: the panic hook's cells (default
hook, lock free), the `LocalKey` of the blockchain interface and its table entries, the interface's
cells (not initialised), the vtable words and table entries of the interface's methods
(`vtab`), the allocator's policy vtable (`vt`), the heap, the key `"STATE"` and `to_string`'s data. -/
noncomputable def statics (n ta : Nat) (A : Nat → Nat) (old k3 idx ptr0 : UInt32) (maxP len : Nat) : IProp GF :=
  iprop(hookCells n 0 old 0 ∗ n ↦[i32][ 1055020 ] 116 ∗ ta ↦[wt][ 116 ] Ref.func (A 565) ∗
    ta ↦[wt][ 106 ] Ref.func (A 564) ∗ blockchainInterfaceCells n 0 0 0 k3 ∗ vtab n ta A ∗
    vt n 1057464 idx ta (A 578) ∗ heapInv n maxP len [] 1 ∗ n ↦[wms][ 1049788 ] StateRead.stateKey ∗
    tvData n ta ptr0 (A 759) (A 353))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **The body of `ft_total_supply`** (296), from its entry frame: with the statics, 736 bytes of
stack below the stack pointer `s` and the host `h` reading the model state `S`, it falls through
with the stack pointer restored and the host `h1.selectReturnValue (supplyJson S)`, `h1` the host
after `storage_read`. -/
theorem body296 (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (e inst : Nat) (mi : ModuleInst) (A : Nat → Nat)
    (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 28 < lim.maxCallDepth) (x96 : Nat)
    (H96 : ToVecAfterFree cfg lim x96) (Cg R : Nat) (gt : GlobalType) (s : UInt32) (hs : 736 ≤ s.toNat)
    (hal : s.toNat % 8 = 0) (old k3 idx ptr0 : UInt32) (maxP len : Nat) (hroom : HeapRoom len maxP)
    (h : NearState) (S : WNear.State) (st : Near.TrieOverlay.State) (hr : ReadOk h S st)
    (Φ : Post NearState GF) :
    code296 e inst mi A n maxP ∗ credits Cg (cost296 cfg h S x96 + R) ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
      stk n (s.toNat - 736) 736 ∗ statics n ta A old k3 idx ptr0 maxP len ∗ mhostPt h ∗
      (∀ h1, ⌜StorageReadPost h StateRead.stateKey 0 st h1⌝ -∗ credits Cg R -∗ g ↦[wg] ⟨gt, .i32 s⟩ -∗
        mhostPt (h1.selectReturnValue (supplyJson S)) -∗ Φ.normal [] ⟨#[.i32 (s - 144)], inst, mi⟩)
      ⊢ mwpi cfg lim d ⟨#[.i32 0], inst, mi⟩ [] f296.body Φ := by
  iintro ⟨#Hk, Hc, Hg, Stk, HS, Hh, W⟩
  iunfold code296 at Hk
  icases Hk with ⟨#KA, #KB, #KC⟩
  iunfold statics at HS
  icases HS with ⟨HH, Hkey, T116, T106, HB, HV, Hvt, Hinv, HsK, HT⟩
  obtain ⟨hv, hacc, hlim, hb, hz, hlink, hproof, hreg, hret⟩ := hr
  have hlt := s.toNat_lt
  icases stkSp 512 224 rfl $$ Stk with ⟨Lo512, Stk⟩
  icases stkSp 80 144 rfl $$ Stk with ⟨L2, Stk⟩
  icases stkSp 8 136 rfl $$ Stk with ⟨-, Stk⟩
  icases stkSp 8 128 rfl $$ Stk with ⟨F8, Stk⟩
  icases stkSp 16 112 rfl $$ Stk with ⟨F16, Stk⟩
  icases stkSp 40 72 rfl $$ Stk with ⟨F32, Stk⟩
  icases stkSp 40 32 rfl $$ Stk with ⟨F72, Stk⟩
  icases stkSp 16 16 rfl $$ Stk with ⟨F112, Stk⟩
  icases stkSp 12 4 rfl $$ Stk with ⟨F128, -⟩
  have hL : ((0 : UInt32) + kOf (val (loOf S) (hiOf S)) + 2).toNat = (jsonOf (val (loOf S) (hiOf S))).length := by
    rw [len_json]; simp [jsonOf]
  have hk39 := FmtString.decDigits_le (loOf S) (hiOf S)
  have hk := FmtString.kOf_toNat (loOf S) (hiOf S)
  have hjl : (jsonOf (val (loOf S) (hiOf S))).length = (decDigits (val (loOf S) (hiOf S))).length + 2 := by
    simp [jsonOf]
  have hsj : (supplyJson S).length = (jsonOf (val (loOf S) (hiOf S))).length := by rw [supplyJson_eq]
  rw [f296_body]
  iapply segA cfg lim d inst mi A n g ta hm (by omega) Cg
    (864 * cfg.regularOpCost + cost219 cfg h S + (cost96 cfg (loOf S) (hiOf S) + x96) +
      (1010 * cfg.regularOpCost + valueReturnUse h ((0 : UInt32) + kOf (val (loOf S) (hiOf S)) + 2).toNat + R))
    gt s hs hal old k3 (bodyB ++ bodyC) Φ
  ihave L2 := stkA (b := s.toNat - 224) (by omega) $$ L2
  iframe KA Hg L2 HH Hkey T116 T106 HB HV
  isplitl [Hc]
  · iapply credits_mono (by unfold cost296; rw [hL, ← hsj]; omega) $$ Hc
  iintro Hc Hg L2 HI
  ihave Lo := stkJ (a := s.toNat - 736) (b := s.toNat - 736 + 512) (k1 := 512) (k2 := 80) (k := 592) rfl rfl
    $$ [Lo512 L2]
  · ihave L2 := stkA (b := s.toNat - 736 + 512) (by omega) $$ L2
    iframe Lo512 L2
  iapply segB cfg lim d e inst mi A n g ta hm hd x96 H96 Cg
    (1010 * cfg.regularOpCost + valueReturnUse h ((0 : UInt32) + kOf (val (loOf S) (hiOf S)) + 2).toNat + R)
    gt s hs hal idx ptr0 maxP len hroom h S hv st hacc hlim hb hz hlink hproof hreg bodyC Φ
  ihave F16 := stkA (b := s.toNat - 128) (by omega) $$ F16
  ihave F32 := stkA (b := s.toNat - 112) (by omega) $$ F32
  ihave F72 := stkA (b := s.toNat - 72) (by omega) $$ F72
  ihave F112 := stkA (b := s.toNat - 32) (by omega) $$ F112
  iframe KB Hc Hg HI Lo F16 F32 F72 F112 Hvt Hinv HsK HT Hh
  iintro %q %p %rst %hl %F %h1 %⟨hq1, hrst⟩ Hc Hg HI L80 R0 R4 R8 R12 V0 V4 V8 Hq Hp Hinv Hh
  obtain ⟨hcfg, hvru⟩ := storageReadPost_config hq1
  ihave F8 := stkA (b := s.toNat - 136) (by omega) $$ F8
  ihave F128 := stkA (b := s.toNat - 16) (by omega) $$ F128
  iapply segC cfg lim d e inst mi A n g ta (some maxP) hm (by omega) Cg R gt s hs hal q
    ((0 : UInt32) + kOf (val (loOf S) (hiOf S)) + 2) p (jsonOf (val (loOf S) (hiOf S))) rst hL.symm
    (by rw [hL, hjl]; omega) (by rw [hjl, hrst]; omega) maxP hl F h1
    (by rw [hcfg, hL, ← hsj]; exact hret) Φ
  iframe KC Hg HI L80 F8 R0 R4 R8 R12 F128 V0 V4 V8 Hq Hp Hinv Hh
  isplitl [Hc]
  · rw [hvru]; iexact Hc
  iintro Hc Hg Hh
  rw [← supplyJson_eq]
  iapply W $$ %h1 %hq1 Hc Hg Hh

/-- The precondition of `ft_total_supply`: no arguments, the stack pointer `s` in global `g`, the
736 bytes of stack below it, the statics and the host. -/
noncomputable def pre296 (n g ta : Nat) (A : Nat → Nat) (gt : GlobalType) (s old k3 idx ptr0 : UInt32)
    (maxP len : Nat) (h : NearState) (args : List Value) : IProp GF :=
  iprop(⌜args = []⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 736) 736 ∗
    statics n ta A old k3 idx ptr0 maxP len ∗ mhostPt h)

/-- The postcondition: no results, the stack pointer restored, the host after `storage_read` with
the JSON of the total supply as its return data. -/
def post296 (g : Nat) (gt : GlobalType) (s : UInt32) (h : NearState) (S : WNear.State)
    (st : Near.TrieOverlay.State) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
    ∃ h1, ⌜StorageReadPost h StateRead.stateKey 0 st h1⌝ ∗ mhostPt (h1.selectReturnValue (supplyJson S)))

/-- **`ft_total_supply`** (function 296 of `contract.wasm`): from the statics of a fresh instance,
736 bytes of stack and a host whose storage holds the model state `S` (`ReadOk`), with `to_vec`
assumed on the heap `state_read` leaves (`ToVecAfterFree`): the JSON of the total supply as the
return data, at `cost296`. -/
theorem f296_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType) (htype : type.results = [])
    (e inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta)
    (hd : d + 28 < lim.maxCallDepth) (x96 : Nat) (H96 : ToVecAfterFree cfg lim x96) (Cg : Nat)
    (gt : GlobalType) (s : UInt32) (hs : 736 ≤ s.toNat) (hal : s.toNat % 8 = 0) (old k3 idx ptr0 : UInt32)
    (maxP len : Nat) (hroom : HeapRoom len maxP) (h : NearState) (S : WNear.State)
    (st : Near.TrieOverlay.State) (hr : ReadOk h S st) :
    code296 e inst mi A n maxP
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f296 Cg
        (pre296 n g ta A gt s old k3 idx ptr0 maxP len h) (fun _ => cost296 cfg h S x96)
        (post296 g gt s h S st) := by
  iintro #Hk
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold pre296 at HP
  icases HP with ⟨%hargs, Hg, Stk, HS, Hh⟩
  subst hargs
  rw [entryLocals_f296]
  iapply body296 cfg lim d e inst mi A n g ta hm hd x96 H96 Cg R gt s hs hal old k3 idx ptr0 maxP len hroom h S st hr
  iframe Hk Hc Hg Stk HS Hh
  iintro %h1 %hq Hc Hg Hh
  simp only [Post.mfunc, htype, List.length_nil]
  isplitr
  · ipureintro; simp
  iexists R
  iframe Hc
  iintro Hc
  iframe Hc
  iunfold post296
  iframe Hg
  isplitr
  · ipureintro; rfl
  iexists h1
  iframe Hh
  ipureintro; exact hq

end Main

end WNear.Binary.FtTotalSupply
