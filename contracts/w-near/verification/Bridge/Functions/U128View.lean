import Bridge.Functions.FtTotalSupplyNone
import Bridge.Functions.Getter

/-!
# The body of a view method returning a `u128`, for any getter

`ft_total_supply` (296) and `storage_minimum_balance` (231) have the same body but for the
getter they call and the location their `expect` panics with:

```wat
;; sp -= 144 (the frame at sp0 = sp - 144)
setup_panic_hook(); set_blockchain_interface(1, 1050188)        ;; bodyA
state_read(sp0 + 72); unwrap_or_default(sp0 + 32, sp0 + 72)    ;; bodyB0
getter(sp0 + 16, sp0 + 32)                                     ;; bodyB1 gi: 414 or 230
[sp0 + 112 .. 128] := [sp0 + 16 .. 32]; to_vec(sp0 + 72, sp0 + 112)
expect(sp0 + 128, sp0 + 72, loc); deref; value_return; drops    ;; bodyCG loc
sp += 144
```

This file proves that body for any getter given its `MFunSpec` in the shape
`Getter.getterPre`/`getterPost` (a frame of `F` bytes, the 16 bytes `vb` it writes), reusing
`FtTotalSupply`'s segments A (`segA`) and, generalised over `loc`, C (`segCG`):

* `segBG`: `state_read`, `unwrap_or_default`, the getter, the copy, `to_vec`.
* `bodyView`: the whole body: the host ends with `h1.selectReturnValue (viewJson vb)`.
* `segBNoneG`, `bodyViewNone`: on an absent `STATE`, the body traps in `unwrap_or_default`,
  before the getter (the prefix `bodyA ++ bodyB0` every view method shares).

`FtTotalSupply`'s own proofs are left as they are.
-/

namespace WNear.Binary.U128View

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv WNear.Binary.FtTotalSupply
open WNear.Binary.Interface (IfaceMod iface ifaceCode dataWord)
open WNear.Binary.ReadRegister (ifaceR iface_of_ifaceR)
open WNear.Binary.VecFromElem (stk roomFor grownLen)
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.BorshFT (join64' split64' joinB splitB stkJ stkW stkB stkSp stkA)
open WNear.Binary.BorshInt (stk_bytes')
open WNear.Binary.StateReadLen (LenStep postModelL f219_spec_model_len)
open WNear.Binary.StateReadModel (contractBytes)
open WNear.Binary.StateRead (stateCode pre219 post219None noneAt)
open WNear.Binary.ToVec (tvCode tvData cost96 len_json)
open WNear.Binary.FmtDigits (decDigits)
open WNear.Binary.FmtU128 (val)
open WNear.Binary.FmtString (kOf)
open WNear.Binary.FmtGrow (newCap)
open WNear.Binary.U128From (u128Bytes)
open WNear.Binary.DropVec (dropCode pre747 post747 f68_spec)
open WNear.Binary.RegisterLen (frame4)
open WNear.Binary.PanicStr (panicCode panicSlot panicked notInit)
open WNear.Binary.Getter (getterPre getterPost)

/-! ## The body -/

/-- `state_read` and `unwrap_or_default`, the prefix every view method starts segment B with. -/
def bodyB0 : List Instr :=
  [.local_get 0, .i32_const 72, .i32_binop .add, .call 219,
    .local_get 0, .i32_const 32, .i32_binop .add, .local_get 0, .i32_const 72, .i32_binop .add, .call 155]

/-- The getter `gi`, the copy of the `u128`, `to_vec`. -/
def bodyB1 (gi : Nat) : List Instr :=
  [.local_get 0, .i32_const 16, .i32_binop .add, .local_get 0, .i32_const 32, .i32_binop .add, .call gi,
    .local_get 0, .local_get 0, .i32_const 24, .i32_binop .add, .load .i64 none { align := 3, offset := 0 },
    .store .i64 none { align := 3, offset := 120 },
    .local_get 0, .local_get 0, .load .i64 none { align := 3, offset := 16 },
    .store .i64 none { align := 3, offset := 112 },
    .local_get 0, .i32_const 72, .i32_binop .add, .local_get 0, .i32_const 112, .i32_binop .add, .call 96]

/-- Segment C with the location `expect` panics with. -/
def bodyCG (loc : UInt32) : List Instr :=
  [.local_get 0, .i32_const 128, .i32_binop .add, .local_get 0, .i32_const 72, .i32_binop .add,
    .i32_const loc, .call 158,
    .local_get 0, .i32_const 8, .i32_binop .add, .local_get 0, .i32_const 128, .i32_binop .add, .call 779,
    .local_get 0, .load .i32 none { align := 2, offset := 8 }, .local_get 0,
    .load .i32 none { align := 2, offset := 12 }, .call 545,
    .local_get 0, .i32_const 128, .i32_binop .add, .call 68,
    .local_get 0, .i32_const 56, .i32_binop .add, .call 68,
    .local_get 0, .i32_const 144, .i32_binop .add, .global_set 0]

theorem bodyB_eq : bodyB = bodyB0 ++ bodyB1 414 := rfl
theorem bodyC_eq : bodyC = bodyCG 1050984 := rfl

/-- The two words of the getter's 16 bytes `vb`, as the copy loads them. -/
def loV (vb : List UInt8) : UInt64 := UInt64.ofNat (Memory.decodeLE (vb.take 8))
def hiV (vb : List UInt8) : UInt64 := UInt64.ofNat (Memory.decodeLE (vb.drop 8))

/-- The JSON the method returns for the getter's bytes `vb`. -/
def viewJson (vb : List UInt8) : List UInt8 := jsonOf (val (loV vb) (hiV vb))

/-! ## Segment C, at any panic location -/

section SegC

variable {GF : BundledGFunctors} [WasmGS NearState GF]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- `FtTotalSupply.segC` for `bodyCG loc`. -/
theorem segCG (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (e inst : Nat) (mi : ModuleInst) (A : Nat → Nat)
    (n g ta : Nat) (mx : Option Nat) (hm : IfaceMod mi A n g ta) (hd : d + 8 < lim.maxCallDepth)
    (Cg R : Nat) (gt : GlobalType) (s : UInt32) (hs : 736 ≤ s.toNat) (hal : s.toNat % 8 = 0)
    (q L p : UInt32) (bs rest : List UInt8) (hbs : bs.length = L.toNat) (hpos : 0 < L.toNat)
    (hrest : bs.length + rest.length = 128) (maxP hl F : Nat) (h1 : NearState)
    (hlim : withinLimit h1.config.maxReturnLen L.toNat = true) (loc : UInt32) (Φ : Post NearState GF) :
    codeC e inst mi A n mx ∗ credits Cg (1010 * cfg.regularOpCost + valueReturnUse h1 L.toNat + R) ∗
      g ↦[wg] ⟨gt, .i32 (s - 144)⟩ ∗ ifaceR n ta A ∗ stk n (s.toNat - 224) 80 ∗ stk n (s.toNat - 136) 8 ∗
      n ↦[i32][ s.toNat - 72 ] 0 ∗ n ↦[i32][ s.toNat - 68 ] q ∗ n ↦[i32][ s.toNat - 64 ] 128 ∗
      n ↦[i32][ s.toNat - 60 ] L ∗ stk n (s.toNat - 16) 12 ∗
      n ↦[i32][ s.toNat - 88 ] p ∗ n ↦[i32][ s.toNat - 84 ] 1 ∗ n ↦[i32][ s.toNat - 80 ] 1 ∗
      n ↦[wms][ q.toNat ] (bs ++ rest) ∗ n ↦[wms][ p.toNat ] WNear.accountsPrefix ∗
      heapInv n maxP hl [(q.toNat, 128), (p.toNat, 1)] F ∗ mhostPt h1 ∗
      (credits Cg R -∗ g ↦[wg] ⟨gt, .i32 s⟩ -∗ mhostPt (h1.selectReturnValue bs) -∗
        Φ.normal [] ⟨#[.i32 (s - 144)], inst, mi⟩)
      ⊢ mwpi cfg lim d ⟨#[.i32 (s - 144)], inst, mi⟩ [] (bodyCG loc) Φ := by
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
  simp only [bodyCG]
  -- expect(sp0 + 128, sp0 + 72, loc)
  ihave PL := join64' (a := s.toNat - 68) (b := s.toNat - 64) q 128 (by omega) $$ [R4 R8]
  · iframe R4 R8
  ihave PL := joinB (a := s.toNat - 68) (b := s.toNat - 60) (bytes32 q ++ bytes32 128) (bytes32 L)
    (by simp; omega) $$ [PL R12]
  · iframe PL R12
  icases stk_bytes' $$ F128 with ⟨%ob, %hob, F128⟩
  mstep; mstep; mstep; mstep; mstep; mstep; mstep
  mcall (ResultExpect.f158_spec cfg lim (d + 1) types[31]! rfl inst mi n g hn hg Cg ⟨gt, .i32 (s - 144)⟩
      (s - 144) (s - 144 + 128) (s - 144 + 72) loc rfl (by omega) (by omega) (bytes32 0)
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

/-! ## Segment B, for any getter -/

section SegB

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The code of segment B but the getter's (persistent). -/
def codeBG (e inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n maxP : Nat) : IProp GF :=
  iprop(stateCode e inst mi A n maxP (some maxP) ∗ tvCode n maxP inst mi A ∗
    A 219 ↪[wf] FuncInst.wasm types[0]! inst f219 ∗ A 155 ↪[wf] FuncInst.wasm types[14]! inst f155 ∗
    A 951 ↪[wf] FuncInst.wasm types[15]! inst f951 ∗ A 96 ↪[wf] FuncInst.wasm types[14]! inst f96 ∗
    inst ↪[inst] mi)

instance (e inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n maxP : Nat) :
    Persistent (codeBG (GF := GF) e inst mi A n maxP) := by
  unfold codeBG; infer_instance

/-- What the body needs of a getter `fg` (function `gi`, code `KG`): its `MFunSpec` called at
`sp0 + 16` on the contract at `sp0 + 32` (any `p`, `pad`), with a frame of `F` bytes, at the
cost `Kg`, writing `vb`; its locals those of 414 and 230 (an `i32`, an `i64`: activation 11). -/
structure GetterOk (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g : Nat) (gi : Nat) (fg : Func) (KG : IProp GF) (F Kg : Nat)
    (Cg : Nat) (gt : GlobalType) (s : UInt32) (S : WNear.State) (vb : List UInt8) : Prop where
  idx : gi < 955
  frame : F ≤ 592
  vb_length : vb.length = 16
  locals : actSize (fg.locals.map ValType.default) = 12
  spec : ∀ (ob : List UInt8) (p : UInt32) (pad : List UInt8), ob.length = 16 → pad.length = 4 →
    (KG ⊢ MFunSpec (GF := GF) cfg lim (d + 1) types[14]! inst mi fg Cg
      (getterPre n g gt (s - 144) (s - 144 + 16) (s - 144 + 32) F ob (contractBytes S p ++ pad))
      (fun _ => Kg)
      (getterPost n g gt (s - 144) (s - 144 + 16) (s - 144 + 32) F vb (contractBytes S p ++ pad)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
open Near.TrieAccounting Near.TrieConstruction Near.TrieOverlay in
/-- Segment B for the getter `gi` (`GetterOk`): `state_read` (219) on the model state `S`,
`unwrap_or_default` (155), the getter, the copy of its `u128` to `sp0 + 112`, `to_vec` (96,
assumed on the heap `state_read` leaves). -/
theorem segBG (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (e inst : Nat) (mi : ModuleInst) (A : Nat → Nat)
    (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 28 < lim.maxCallDepth) (x96 : Nat)
    (H96 : ToVecAfterFree cfg lim x96) (Cg R : Nat) (gt : GlobalType) (s : UInt32) (hs : 736 ≤ s.toNat)
    (hal : s.toNat % 8 = 0) (idx ptr0 : UInt32) (maxP len : Nat) (hroom : HeapRoom len maxP)
    (h : NearState) (S : WNear.State)
    (gi : Nat) (fg : Func) (KG : IProp GF) [Persistent KG] (F Kg : Nat) (vb : List UInt8)
    (HG : GetterOk cfg lim d inst mi A n g gi fg KG F Kg Cg gt s S vb)
    (hv : h.storage WNear.stateKey = some (WNear.header S))
    (st : Near.TrieOverlay.State) (hacc : h.storageAccounting = some st)
    (hlim : withinLimit h.config.maxStorageKeyLen 5 = true)
    (hb : build st.entries = .ok st.base) (hz : zeroHash ∉ st.base.witness.map Prod.fst)
    (hlink : h.storage WNear.stateKey = viewVal st (contractKey h.context.currentAccountId WNear.stateKey))
    (hproof : ProofBudget h st (lookupProofBound (contractKey h.context.currentAccountId WNear.stateKey)))
    (hreg : withinLimit h.config.maxRegisterLen 29 = true)
    (rest : List Instr) (Φ : Post NearState GF) :
    codeBG e inst mi A n maxP ∗ A gi ↪[wf] FuncInst.wasm types[14]! inst fg ∗ KG ∗
      credits Cg (818 * cfg.regularOpCost + Kg + cost219 cfg h S +
        (cost96 cfg (loV vb) (hiV vb) + x96) + R) ∗
      g ↦[wg] ⟨gt, .i32 (s - 144)⟩ ∗ ifaceR n ta A ∗ stk n (s.toNat - 736) 592 ∗
      stk n (s.toNat - 128) 16 ∗ stk n (s.toNat - 112) 40 ∗ stk n (s.toNat - 72) 40 ∗ stk n (s.toNat - 32) 16 ∗
      vt n 1057464 idx ta (A 578) ∗ heapInv n maxP len [] 1 ∗ n ↦[wms][ 1049788 ] StateRead.stateKey ∗
      tvData n ta ptr0 (A 759) (A 353) ∗ mhostPt h ∗
      (∀ (q p : UInt32) (rst : List UInt8) (hl F : Nat) (h1 : NearState),
        ⌜StorageReadPost h StateRead.stateKey 0 st h1 ∧
          rst.length = 128 - ((kOf (val (loV vb) (hiV vb))).toNat + 2)⌝ -∗
        credits Cg R -∗ g ↦[wg] ⟨gt, .i32 (s - 144)⟩ -∗ ifaceR n ta A -∗ stk n (s.toNat - 224) 80 -∗
        n ↦[i32][ s.toNat - 72 ] 0 -∗ n ↦[i32][ s.toNat - 68 ] q -∗ n ↦[i32][ s.toNat - 64 ] 128 -∗
        n ↦[i32][ s.toNat - 60 ] (0 + kOf (val (loV vb) (hiV vb)) + 2) -∗
        n ↦[i32][ s.toNat - 88 ] p -∗ n ↦[i32][ s.toNat - 84 ] 1 -∗ n ↦[i32][ s.toNat - 80 ] 1 -∗
        n ↦[wms][ q.toNat ] (viewJson vb ++ rst) -∗
        n ↦[wms][ p.toNat ] WNear.accountsPrefix -∗
        heapInv n maxP hl [(q.toNat, 128), (p.toNat, 1)] F -∗ mhostPt h1 -∗
        mwpi cfg lim d ⟨#[.i32 (s - 144)], inst, mi⟩ [] rest Φ)
      ⊢ mwpi cfg lim d ⟨#[.i32 (s - 144)], inst, mi⟩ [] ((bodyB0 ++ bodyB1 gi) ++ rest) Φ := by
  iintro ⟨#Hk, #FG, #HKG, Hc, Hg, HI, Lo, F16, F32, F72, F112, Hvt, Hinv, Hkey, HT, Hh, W⟩
  ihave #Hk' := Hk
  iunfold codeBG at Hk'
  icases Hk' with ⟨#HSC, #HTV, #F219, #F155, #F951, #F96, #Hi⟩
  unfold cost219
  obtain ⟨hgi, hF, hvb, hloc, HGs⟩ := HG
  have hn := hm.mem
  have hg := hm.glob
  have ha219 := hm.funcs 219 (by decide)
  have ha155 := hm.funcs 155 (by decide)
  have hagi := hm.funcs gi hgi
  have ha96 := hm.funcs 96 (by decide)
  have t0 : types[0]!.params.length = 1 := rfl
  have t14 : types[14]!.params.length = 2 := rfl
  have hlt := s.toNat_lt
  obtain ⟨r1, r2, r3, r4⟩ := hroom
  have e0 : (s - 144).toNat = s.toNat - 144 := by rw [tsub _ _ (by simp; omega)]; simp
  have a72 : (s - 144 + 72).toNat = s.toNat - 72 := by simp [UInt32.toNat_add, e0]; omega
  have a32 : (s - 144 + 32).toNat = s.toNat - 112 := by simp [UInt32.toNat_add, e0]; omega
  have a16 : (s - 144 + 16).toNat = s.toNat - 128 := by simp [UInt32.toNat_add, e0]; omega
  have a24 : (s - 144 + 24).toNat = s.toNat - 120 := by simp [UInt32.toNat_add, e0]; omega
  have a112 : (s - 144 + 112).toNat = s.toNat - 32 := by simp [UInt32.toNat_add, e0]; omega
  iapply mwpi_seq
  simp only [bodyB0, bodyB1, List.cons_append, List.nil_append]
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
  -- the getter: gi(sp0 + 16, sp0 + 32)
  icases stkSp (592 - F) F (by omega) $$ Lo with ⟨Lo, FB⟩
  icases stk_bytes' $$ F16 with ⟨%ob16, %hob16, F16⟩
  ihave #SG := HGs ob16 p pad hob16 hpad $$ HKG
  mstep; mstep; mstep; mstep; mstep; mstep
  mcall SG using [Hg FB F16 C32]
    with (mstep_norm_full; simp only [hloc, Nat.reduceAdd, Nat.reduceDiv] at *; omega)
  · iunfold getterPre
    ihave FB := stkA (b := (s - 144).toNat - F) (by omega) $$ FB
    ihave F16 := memBytes_addr (b := (s - 144 + 16).toNat) (by omega) $$ F16
    iframe Hg FB F16 C32
    ipureintro; rfl
  iunfold getterPost at HQ
  icases HQ with ⟨%hrs, Hg, FB, T16, C32⟩
  subst hrs
  simp only [hloc, Nat.reduceAdd, Nat.reduceDiv]
  -- the copy: [sp0 + 120] := [sp0 + 24]; [sp0 + 112] := [sp0 + 16]
  ihave T16 := memBytes_addr (b := s.toNat - 128) (by omega) $$ T16
  icases U128From.memBytes_split n (s.toNat - 128) 8 vb (by omega) $$ T16 with ⟨T16a, T16b⟩
  have hne1 : vb.take 8 ≠ [] := by
    intro h0; have := congrArg List.length h0; simp [hvb] at this
  have hne2 : vb.drop 8 ≠ [] := by
    intro h0; have := congrArg List.length h0; simp [hvb] at this
  icases stkSp 8 8 rfl $$ F112 with ⟨Z0, Z8⟩
  icases stk_bytes' $$ Z0 with ⟨%z0, %hz0, Z0⟩
  icases stk_bytes' $$ Z8 with ⟨%z8, %hz8, Z8⟩
  mstep; mstep; mstep; mstep; mstep [T16b] with (simp [hvb]); mstep [Z8]
  mstep; mstep; mstep [T16a] with (simp [hvb]); mstep [Z0]
  -- to_vec(sp0 + 72, sp0 + 112)
  ihave V := joinB (a := s.toNat - 32) (b := s.toNat - 32 + 8)
    (storeBytes (Value.i64 (UInt64.ofNat (Memory.decodeLE (List.take 8 vb)))) 8)
    (storeBytes (Value.i64 (UInt64.ofNat (Memory.decodeLE (List.drop 8 vb)))) 8)
    (by simp) $$ [Z0 Z8]
  · iframe Z0 Z8
  ihave Hopt := memBytes_addr (b := s.toNat - 72) (by omega) $$ Hopt
  rw [contractBytes_split]
  icases splitB (a := s.toNat - 72) (b := s.toNat - 56) (WNear.Borsh.u128 S.totalSupply) _
    (by rw [u128_length]; omega) $$ Hopt with ⟨O72, -⟩
  ihave FB := stkA (b := (s - 144).toNat - 592 + (592 - F)) (by omega) $$ FB
  ihave Lo := stkJ (a := (s - 144).toNat - 592) (b := (s - 144).toNat - 592 + (592 - F)) (k1 := 592 - F)
    (k2 := F) (k := 592) rfl (by omega) $$ [Lo FB]
  · iframe Lo FB
  icases stkSp 176 416 rfl $$ Lo with ⟨-, Lo⟩
  have hr1 : roomFor len' maxP 128 := roomFor_of len maxP len' 128 (by decide) ⟨r1, r2, r3, r4⟩ hl1 (by omega) hl3
  have hr2 : ∀ l, l = len' ∨ l = grownLen len' 128 →
      roomFor l maxP (newCap 0 (kOf (val (loV vb) (hiV vb)))) := by
    intro l hl
    rw [grownLen_small _ _ (by decide)] at hl
    exact roomFor_of len maxP l _ (newCap_le _) ⟨r1, r2, r3, r4⟩ (by omega) (by omega) (by omega)
  ihave #S96 := H96 (GF := GF) (d + 1) types[14]! rfl inst mi A n g ta hm (by omega) Cg gt (s - 144) (s - 144 + 72)
    (s - 144 + 112) ptr0 idx (WNear.Borsh.u128 S.totalSupply) maxP len' [(p.toNat, 1)] (loV vb) (hiV vb)
    (by omega) (u128_length _) (by omega) (by omega) hr1 hr2 $$ HTV
  mstep; mstep; mstep; mstep; mstep; mstep
  mcall S96 using [Hg Lo O72 V HT Hvt Hinv]
  · ihave Lo := stkA (b := (s - 144).toNat - 416) (by omega) $$ Lo
    ihave O72 := memBytes_addr (b := (s - 144 + 72).toNat) (by omega) $$ O72
    ihave V := memBytes_addr (b := (s - 144 + 112).toNat) (by omega) $$ V
    iframe Hg Lo O72 HT Hvt Hinv
    have hu : u128Bytes (loV vb) (hiV vb) =
        storeBytes (Value.i64 (UInt64.ofNat (Memory.decodeLE (List.take 8 vb)))) 8 ++
        storeBytes (Value.i64 (UInt64.ofNat (Memory.decodeLE (List.drop 8 vb)))) 8 :=
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
  ihave C32 := memBytes_addr (b := s.toNat - 112) (by omega) $$ C32
  icases splitB (a := s.toNat - 112) (b := s.toNat - 96) (WNear.Borsh.u128 S.totalSupply) _
    (by rw [u128_length]; omega) $$ C32 with ⟨-, C48⟩
  icases splitB (a := s.toNat - 96) (b := s.toNat - 88) (WNear.Borsh.u64 S.accountStorageUsage) _
    (by rw [u64_length]; omega) $$ C48 with ⟨-, C56⟩
  icases splitB (a := s.toNat - 88) (b := s.toNat - 84) (bytes32 p) _ (by simp; omega) $$ C56 with ⟨V0, C60⟩
  icases splitB (a := s.toNat - 84) (b := s.toNat - 80) (bytes32 1) _ (by simp; omega) $$ C60 with ⟨V4, C64⟩
  icases splitB (a := s.toNat - 80) (b := s.toNat - 76) (bytes32 1) _ (by simp; omega) $$ C64 with ⟨V8, -⟩
  mcredits R
  iapply W $$ %q %p %rst %hl' %F' %h1 [] Hc Hg HI Lo R0 R4 R8 R12 V0 V4 V8 [Hq] Hp Hinv Hh
  · ipureintro; exact ⟨hq1, hrst⟩
  · ihave Hq := AllocNewCell.memBytes_eq (bs' := viewJson vb ++ rst) (by simp [viewJson, jsonOf]) $$ Hq
    iexact Hq

end SegB

/-! ## The body -/

open Near.TrieAccounting Near.TrieConstruction Near.TrieOverlay in
/-- `FtTotalSupply.ReadOk` with the returned JSON `j` in place of `supplyJson S`. -/
structure ReadOkV (h : NearState) (S : WNear.State) (st : Near.TrieOverlay.State) (j : List UInt8) :
    Prop where
  value : h.storage WNear.stateKey = some (WNear.header S)
  acc : h.storageAccounting = some st
  keyLen : withinLimit h.config.maxStorageKeyLen 5 = true
  trie : build st.entries = .ok st.base
  zero : zeroHash ∉ st.base.witness.map Prod.fst
  link : h.storage WNear.stateKey = viewVal st (contractKey h.context.currentAccountId WNear.stateKey)
  proof : ProofBudget h st (lookupProofBound (contractKey h.context.currentAccountId WNear.stateKey))
  regLen : withinLimit h.config.maxRegisterLen 29 = true
  retLen : withinLimit h.config.maxReturnLen j.length = true

/-- The cost of the body, activation excluded: 2303 `regular_op_cost`s (segment A's 475,
segment B's 818 with the getter's call and activation, segment C's 1010), the getter's `Kg`,
`state_read`'s `cost219`, `to_vec`'s `cost96` and `x96`, `value_return`'s gas. -/
noncomputable def costView (cfg : WasmConfig) (h : NearState) (S : WNear.State) (x96 Kg : Nat)
    (vb : List UInt8) : Nat :=
  2303 * cfg.regularOpCost + Kg + cost219 cfg h S + (cost96 cfg (loV vb) (hiV vb) + x96) +
    valueReturnUse h (viewJson vb).length

section Main

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The code a view method with getter `gi` runs (persistent): segment A's, B's but the
getter's, C's, the getter and its code `KG`. -/
def codeView (e inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n maxP gi : Nat) (fg : Func)
    (KG : IProp GF) : IProp GF :=
  iprop(codeA inst mi A ∗ codeBG e inst mi A n maxP ∗ codeC e inst mi A n (some maxP) ∗
    A gi ↪[wf] FuncInst.wasm types[14]! inst fg ∗ KG)

instance (e inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n maxP gi : Nat) (fg : Func) (KG : IProp GF)
    [Persistent KG] : Persistent (codeView e inst mi A n maxP gi fg KG) := by
  unfold codeView; infer_instance

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **The body of a view method returning a `u128`** (`fb`: segment A, segment B with the getter
`gi`, segment C with `loc`), from its entry frame: with the statics, 736 bytes of stack below the
stack pointer `s` and the host `h` reading the model state `S`, it falls through with the stack
pointer restored and the host `h1.selectReturnValue (viewJson vb)`, `h1` the host after
`storage_read`, `vb` the getter's bytes. -/
theorem bodyView (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (e inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 28 < lim.maxCallDepth) (x96 : Nat)
    (H96 : ToVecAfterFree cfg lim x96) (Cg R : Nat) (gt : GlobalType) (s : UInt32) (hs : 736 ≤ s.toNat)
    (hal : s.toNat % 8 = 0) (old k3 idx ptr0 : UInt32) (maxP len : Nat) (hroom : HeapRoom len maxP)
    (h : NearState) (S : WNear.State) (st : Near.TrieOverlay.State)
    (gi : Nat) (fg : Func) (KG : IProp GF) [Persistent KG] (F Kg : Nat) (vb : List UInt8)
    (HG : GetterOk cfg lim d inst mi A n g gi fg KG F Kg Cg gt s S vb)
    (hr : ReadOkV h S st (viewJson vb)) (loc : UInt32) (fb : List Instr)
    (hfb : fb = bodyA ++ ((bodyB0 ++ bodyB1 gi) ++ bodyCG loc)) (Φ : Post NearState GF) :
    codeView e inst mi A n maxP gi fg KG ∗ credits Cg (costView cfg h S x96 Kg vb + R) ∗
      g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 736) 736 ∗ statics n ta A old k3 idx ptr0 maxP len ∗
      mhostPt h ∗
      (∀ h1, ⌜StorageReadPost h StateRead.stateKey 0 st h1⌝ -∗ credits Cg R -∗ g ↦[wg] ⟨gt, .i32 s⟩ -∗
        mhostPt (h1.selectReturnValue (viewJson vb)) -∗ Φ.normal [] ⟨#[.i32 (s - 144)], inst, mi⟩)
      ⊢ mwpi cfg lim d ⟨#[.i32 0], inst, mi⟩ [] fb Φ := by
  iintro ⟨#Hk, Hc, Hg, Stk, HS, Hh, W⟩
  iunfold codeView at Hk
  icases Hk with ⟨#KA, #KB, #KC, #FG, #HKG⟩
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
  have hL : ((0 : UInt32) + kOf (val (loV vb) (hiV vb)) + 2).toNat = (viewJson vb).length := by
    rw [viewJson, len_json]; simp [jsonOf]
  have hk39 := FmtString.decDigits_le (loV vb) (hiV vb)
  have hk := FmtString.kOf_toNat (loV vb) (hiV vb)
  have hjl : (viewJson vb).length = (decDigits (val (loV vb) (hiV vb))).length + 2 := by
    simp [viewJson, jsonOf]
  subst hfb
  iapply segA cfg lim d inst mi A n g ta hm (by omega) Cg
    (818 * cfg.regularOpCost + Kg + cost219 cfg h S + (cost96 cfg (loV vb) (hiV vb) + x96) +
      (1010 * cfg.regularOpCost + valueReturnUse h ((0 : UInt32) + kOf (val (loV vb) (hiV vb)) + 2).toNat + R))
    gt s hs hal old k3 ((bodyB0 ++ bodyB1 gi) ++ bodyCG loc) Φ
  ihave L2 := stkA (b := s.toNat - 224) (by omega) $$ L2
  iframe KA Hg L2 HH Hkey T116 T106 HB HV
  isplitl [Hc]
  · iapply credits_mono (by unfold costView; rw [hL]; omega) $$ Hc
  iintro Hc Hg L2 HI
  ihave Lo := stkJ (a := s.toNat - 736) (b := s.toNat - 736 + 512) (k1 := 512) (k2 := 80) (k := 592) rfl rfl
    $$ [Lo512 L2]
  · ihave L2 := stkA (b := s.toNat - 736 + 512) (by omega) $$ L2
    iframe Lo512 L2
  iapply segBG cfg lim d e inst mi A n g ta hm hd x96 H96 Cg
    (1010 * cfg.regularOpCost + valueReturnUse h ((0 : UInt32) + kOf (val (loV vb) (hiV vb)) + 2).toNat + R)
    gt s hs hal idx ptr0 maxP len hroom h S gi fg KG F Kg vb HG hv st hacc hlim hb hz hlink hproof hreg
    (bodyCG loc) Φ
  ihave F16 := stkA (b := s.toNat - 128) (by omega) $$ F16
  ihave F32 := stkA (b := s.toNat - 112) (by omega) $$ F32
  ihave F72 := stkA (b := s.toNat - 72) (by omega) $$ F72
  ihave F112 := stkA (b := s.toNat - 32) (by omega) $$ F112
  iframe KB FG HKG Hg HI Lo F16 F32 F72 F112 Hvt Hinv HsK HT Hh
  isplitl [Hc]
  · iapply credits_mono (by omega) $$ Hc
  iintro %q %p %rst %hl %F %h1 %⟨hq1, hrst⟩ Hc Hg HI L80 R0 R4 R8 R12 V0 V4 V8 Hq Hp Hinv Hh
  obtain ⟨hcfg, hvru⟩ := storageReadPost_config hq1
  ihave F8 := stkA (b := s.toNat - 136) (by omega) $$ F8
  ihave F128 := stkA (b := s.toNat - 16) (by omega) $$ F128
  iapply segCG cfg lim d e inst mi A n g ta (some maxP) hm (by omega) Cg R gt s hs hal q
    ((0 : UInt32) + kOf (val (loV vb) (hiV vb)) + 2) p (viewJson vb) rst hL.symm
    (by rw [hL, hjl]; omega) (by rw [hjl, hrst]; omega) maxP hl F h1
    (by rw [hcfg, hL]; exact hret) loc Φ
  iframe KC Hg HI L80 F8 R0 R4 R8 R12 F128 V0 V4 V8 Hq Hp Hinv Hh
  isplitl [Hc]
  · rw [hvru]; iexact Hc
  iintro Hc Hg Hh
  iapply W $$ %h1 %hq1 Hc Hg Hh

end Main

/-! ## On an absent `STATE` -/

section None

variable {GF : BundledGFunctors} [WasmGS NearState GF]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- `FtTotalSupply.segBNone` for the shared prefix `bodyB0` followed by anything: `state_read`
(219) leaves `None`, and `unwrap_or_default` (155) traps through `Contract::default`, the host
after `storage_read` panicked. -/
theorem segBNoneG (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (e inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 18 < lim.maxCallDepth)
    (Cg R : Nat) (gt : GlobalType) (s : UInt32) (hs : 736 ≤ s.toNat) (hal : s.toNat % 8 = 0)
    (idx : UInt32) (maxP len : Nat) (h : NearState) (st : Near.TrieOverlay.State) (hr : ReadNone h st)
    (rest : List Instr) (Φ : Post NearState GF) :
    codeBG e inst mi A n maxP ∗ ifaceCode e inst mi A n (some maxP) ∗ codeP e inst mi A ∗
      credits Cg (costBNone cfg h + R) ∗ g ↦[wg] ⟨gt, .i32 (s - 144)⟩ ∗ ifaceR n ta A ∗
      stk n (s.toNat - 736) 592 ∗ stk n (s.toNat - 72) 40 ∗ vt n 1057464 idx ta (A 578) ∗
      heapInv n maxP len [] 1 ∗ n ↦[wms][ 1049788 ] StateRead.stateKey ∗ staticsP n ta A ∗ mhostPt h ∗
      (∀ h1, ⌜StorageReadPost h StateRead.stateKey 0 st h1⌝ -∗ panicked Cg h1 notInit -∗ Φ.trap)
      ⊢ mwpi cfg lim d ⟨#[.i32 (s - 144)], inst, mi⟩ [] (bodyB0 ++ rest) Φ := by
  iintro ⟨#Hk, #HIC, #HP, Hc, Hg, HI, Lo, F72, Hvt, Hinv, Hkey, HSP, Hh, W⟩
  ihave #Hk' := Hk
  iunfold codeBG at Hk'
  icases Hk' with ⟨#HSC, -, #F219, #F155, -, -, #Hi⟩
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
  simp only [bodyB0]
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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **The body of a view method on an uninitialized contract** (`fb`: segment A, then the
prefix `bodyB0`, then anything): it traps in `unwrap_or_default`, the host after `storage_read`
panicked with "The contract is not initialized", at `FtTotalSupply.cost296None`. -/
theorem bodyViewNone (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (e inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 18 < lim.maxCallDepth)
    (Cg R : Nat) (gt : GlobalType) (s : UInt32) (hs : 736 ≤ s.toNat) (hal : s.toNat % 8 = 0)
    (old k3 idx ptr0 : UInt32) (maxP len : Nat) (h : NearState) (st : Near.TrieOverlay.State)
    (hr : ReadNone h st) (rest : List Instr) (fb : List Instr) (hfb : fb = bodyA ++ (bodyB0 ++ rest))
    (Φ : Post NearState GF) :
    codeA inst mi A ∗ codeBG e inst mi A n maxP ∗ ifaceCode e inst mi A n (some maxP) ∗ codeP e inst mi A ∗
      credits Cg (cost296None cfg h + R) ∗
      g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 736) 736 ∗ statics n ta A old k3 idx ptr0 maxP len ∗
      staticsP n ta A ∗ mhostPt h ∗
      (∀ h1, ⌜StorageReadPost h StateRead.stateKey 0 st h1⌝ -∗ panicked Cg h1 notInit -∗ Φ.trap)
      ⊢ mwpi cfg lim d ⟨#[.i32 0], inst, mi⟩ [] fb Φ := by
  iintro ⟨#KA, #KB, #HIC, #HP, Hc, Hg, Stk, HS, HSP, Hh, W⟩
  iunfold statics at HS
  icases HS with ⟨HH, Hkey, T116, T106, HB, HV, Hvt, Hinv, HsK, -⟩
  have hlt := s.toNat_lt
  icases stkSp 512 224 rfl $$ Stk with ⟨Lo512, Stk⟩
  icases stkSp 80 144 rfl $$ Stk with ⟨L2, Stk⟩
  icases stkSp 72 72 rfl $$ Stk with ⟨-, Stk⟩
  icases stkSp 40 32 rfl $$ Stk with ⟨F72, -⟩
  subst hfb
  iapply segA cfg lim d inst mi A n g ta hm (by omega) Cg (costBNone cfg h + R) gt s hs hal old k3
    (bodyB0 ++ rest) Φ
  ihave L2 := stkA (b := s.toNat - 224) (by omega) $$ L2
  iframe KA Hg L2 HH Hkey T116 T106 HB HV
  isplitl [Hc]
  · iapply credits_mono (by unfold cost296None costBNone; omega) $$ Hc
  iintro Hc Hg L2 HI
  ihave Lo := stkJ (a := s.toNat - 736) (b := s.toNat - 736 + 512) (k1 := 512) (k2 := 80) (k := 592) rfl rfl
    $$ [Lo512 L2]
  · ihave L2 := stkA (b := s.toNat - 736 + 512) (by omega) $$ L2
    iframe Lo512 L2
  iapply segBNoneG cfg lim d e inst mi A n g ta hm hd Cg R gt s hs hal idx maxP len h st hr rest Φ
  ihave F72 := stkA (b := s.toNat - 72) (by omega) $$ F72
  iframe KB HIC HP Hc Hg HI Lo F72 Hvt Hinv HsK HSP Hh W

end None

end WNear.Binary.U128View
