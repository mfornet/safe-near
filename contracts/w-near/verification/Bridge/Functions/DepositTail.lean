import Bridge.Functions.DepositLog
import Bridge.Functions.LogStr
import Bridge.Functions.DropVec
import Bridge.Functions.SerdeAccountId
import Binary.Code

/-!
# The end of `near_deposit` (232): the log and the drops (M8)

After `internal_deposit` (406), 232 builds the log's `Arguments`, formats it, logs it and drops
the two `String`s:

```
354(sp + 16, sp + 40, 5)               the `u128` argument (&amount, table entry 5)
745(sp + 8, sp + 56, 6)                the `String` argument (&account_id, table entry 6)
args at sp + 128; Arguments at sp + 72 { pieces: 1050632, 2, fmt: None, args: sp + 128, 2 }
846(sp + 112, sp + 72)                 format!
779(sp, sp + 112); 546(*sp, *(sp + 4)) log_str
68(sp + 112); 68(sp + 56)              the drops
sp += 144; return
```

* `f354_spec`, `f745_spec`: `fmt::ArgumentV1::new` (two stores).
* `logM_of`, `logM_to`: the arrays of the log's `Arguments` as `DepositLog.logM`.
-/

namespace WNear.Binary.DepositTail

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_word stk_addr roomFor)
open WNear.Binary.BorshFT (splitB joinB stkJ stkSp stkA join64' split64' stkW stkB)
open WNear.Binary.DepositLog
open WNear.Binary.FmtDigits (decDigits lut)
open WNear.Binary.FmtU128 (val)
open WNear.Binary.U128From (u128Bytes)
open WNear.Binary.FmtStrPad (strW)
open WNear.Binary.FmtWriteN (argsN)

section Spec

variable {GF : BundledGFunctors} [WasmGS NearState GF]

set_option maxRecDepth 100000 in
/-- **`ArgumentV1::new(out, v, f)`** (354): `(v, f)` at `out`. -/
theorem f354_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (n : Nat)
    (hn : mi.memAddrs[0]? = some n) (Cg : Nat) (out v f : UInt32) (o0 o4 : List UInt8)
    (h0 : o0.length = 4) (h4 : o4.length = 4) :
    ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f354 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 v, .i32 f]⌝ ∗ n ↦[wms][ out.toNat ] o0 ∗
          n ↦[wms][ out.toNat + 4 ] o4))
        (fun _ => 8 * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ n ↦[i32][ out.toNat ] v ∗ n ↦[i32][ out.toNat + 4 ] f)) := by
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, O0, O4⟩
  subst hargs
  simp only [f354]
  repeat mstep
  mstep [O4]
  repeat mstep
  mstep [O0]
  mcredits R
  iframe Hc O0 O4

set_option maxRecDepth 100000 in
/-- **`ArgumentV1::new(out, v, f)`** (745): `(v, f)` at `out`. -/
theorem f745_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (n : Nat)
    (hn : mi.memAddrs[0]? = some n) (Cg : Nat) (out v f : UInt32) (o0 o4 : List UInt8)
    (h0 : o0.length = 4) (h4 : o4.length = 4) :
    ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f745 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 v, .i32 f]⌝ ∗ n ↦[wms][ out.toNat ] o0 ∗
          n ↦[wms][ out.toNat + 4 ] o4))
        (fun _ => 8 * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ n ↦[i32][ out.toNat ] v ∗ n ↦[i32][ out.toNat + 4 ] f)) := by
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, O0, O4⟩
  subst hargs
  simp only [f745]
  repeat mstep
  mstep [O4]
  repeat mstep
  mstep [O0]
  mcredits R
  iframe Hc O0 O4

/-- The static part of the log's arrays: the pieces array at 1050632 and the formatters' table
entries 5 and 6. -/
def logStat (n ta : Nat) (A : Nat → Nat) : IProp GF :=
  iprop(n ↦[i32][ 1050632 ] 1050612 ∗ n ↦[i32][ 1050636 ] 8 ∗ n ↦[i32][ 1050640 ] 1050620 ∗
    n ↦[i32][ 1050644 ] 9 ∗ ta ↦[wt][ 5 ] Ref.func (A 901) ∗ ta ↦[wt][ 6 ] Ref.func (A 179))

theorem logM_of (n ta : Nat) (A : Nat → Nat) (argp u sv : UInt32) :
    logStat (GF := GF) n ta A ∗ n ↦[i32][ argp.toNat ] u ∗ n ↦[i32][ argp.toNat + 4 ] 5 ∗
      n ↦[i32][ argp.toNat + 8 ] sv ∗ n ↦[i32][ argp.toNat + 12 ] 6 ⊢ logM n ta A argp u sv := by
  iintro ⟨HS, A0, A4, A8, A12⟩
  iunfold logStat at HS
  icases HS with ⟨P0, P4, P8, P12, T5, T6⟩
  iunfold logM
  simp only [pptr, plen, vp, fi, bF, ↓reduceIte, Nat.reduceEqDiff, Nat.mul_zero, Nat.add_zero, Nat.mul_one]
  rw [show (1050632 : UInt32).toNat = 1050632 from rfl, show (5 : UInt32).toNat = 5 from rfl,
    show (6 : UInt32).toNat = 6 from rfl, show argp.toNat + 8 + 4 = argp.toNat + 12 by omega]
  iframe P0 P4 P8 P12 T5 T6 A0 A4 A8 A12

theorem logM_to (n ta : Nat) (A : Nat → Nat) (argp u sv : UInt32) :
    logM (GF := GF) n ta A argp u sv ⊢ logStat n ta A ∗ n ↦[i32][ argp.toNat ] u ∗ n ↦[i32][ argp.toNat + 4 ] 5 ∗
      n ↦[i32][ argp.toNat + 8 ] sv ∗ n ↦[i32][ argp.toNat + 12 ] 6 := by
  iintro H
  iunfold logM at H
  simp only [pptr, plen, vp, fi, bF, ↓reduceIte, Nat.reduceEqDiff, Nat.mul_zero, Nat.add_zero, Nat.mul_one]
  rw [show (1050632 : UInt32).toNat = 1050632 from rfl, show (5 : UInt32).toNat = 5 from rfl,
    show (6 : UInt32).toNat = 6 from rfl, show argp.toNat + 8 + 4 = argp.toNat + 12 by omega]
  icases H with ⟨⟨P0, P4⟩, ⟨P8, P12⟩, ⟨A0, A4, T5⟩, ⟨A8, A12, T6⟩⟩
  iunfold logStat
  iframe P0 P4 P8 P12 T5 T6 A0 A4 A8 A12

/-- 232's instructions after `internal_deposit` (406). -/
def tail232 : List Instr :=
  [.local_get 1, .i32_const 16, .i32_binop .add, .local_get 1, .i32_const 40, .i32_binop .add, .i32_const 5,
    .call 354,
    .local_get 1, .load .i64 none { align := 3, offset := 16 }, .local_set 2,
    .local_get 1, .i32_const 8, .i32_binop .add, .local_get 1, .i32_const 56, .i32_binop .add, .i32_const 6,
    .call 745,
    .local_get 1, .i32_const 92, .i32_binop .add, .i32_const 2, .store .i32 none { align := 2, offset := 0 },
    .local_get 1, .local_get 2, .store .i64 none { align := 3, offset := 128 },
    .local_get 1, .i64_const 2, .store .i64 none { align := 2, offset := 76 },
    .local_get 1, .i32_const 1050632, .store .i32 none { align := 2, offset := 72 },
    .local_get 1, .local_get 1, .load .i64 none { align := 3, offset := 8 },
    .store .i64 none { align := 3, offset := 136 },
    .local_get 1, .local_get 1, .i32_const 128, .i32_binop .add, .store .i32 none { align := 2, offset := 88 },
    .local_get 1, .i32_const 112, .i32_binop .add, .local_get 1, .i32_const 72, .i32_binop .add, .call 846,
    .local_get 1, .local_get 1, .i32_const 112, .i32_binop .add, .call 779,
    .local_get 1, .load .i32 none { align := 2, offset := 0 }, .local_get 1,
    .load .i32 none { align := 2, offset := 4 }, .call 546,
    .local_get 1, .i32_const 112, .i32_binop .add, .call 68,
    .local_get 1, .i32_const 56, .i32_binop .add, .call 68,
    .local_get 1, .i32_const 144, .i32_binop .add, .global_set 0, .return]

/-- The code of the tail (persistent). -/
def tailCode (e n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (mx : Option Nat) : IProp GF :=
  iprop(code846 n maxP inst mi A ∗ DropVec.dropCode inst mi A ∗
    A 452 ↪[wf] FuncInst.wasm types[14]! inst f452 ∗ Interface.ifaceCode e inst mi A n mx ∗ LogStr.lCode e inst A ∗
    A 354 ↪[wf] FuncInst.wasm types[31]! inst f354 ∗ A 745 ↪[wf] FuncInst.wasm types[31]! inst f745 ∗
    A 846 ↪[wf] FuncInst.wasm types[14]! inst f846 ∗ A 779 ↪[wf] FuncInst.wasm types[14]! inst f779 ∗
    A 546 ↪[wf] FuncInst.wasm types[14]! inst f546 ∗ A 68 ↪[wf] FuncInst.wasm types[0]! inst f68)

instance (e n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (mx : Option Nat) :
    Persistent (tailCode (GF := GF) e n maxP inst mi A mx) := by
  unfold tailCode; infer_instance

/-- The log's text. -/
abbrev logText (lo hi : UInt64) (ab : List UInt8) : List UInt8 := logW (decDigits (val lo hi)) ab 4

/-- The statics the tail reads: the arrays, the sink's vtable slot, the digit table, the pieces. -/
def tailStat (n ta : Nat) (A : Nat → Nat) : IProp GF :=
  iprop(logStat n ta A ∗ n ↦[i32][ (1066728 : UInt32).toNat + 12 ] 189 ∗
    ta ↦[wt][ (189 : UInt32).toNat ] Ref.func (A 840) ∗ n ↦[wms][ 1070974 ] lut ∗
    n ↦[wms][ 1050612 ] pDeposit ∗ n ↦[wms][ 1050620 ] pNear)

/-- The cost of the tail, activations of the callees included. -/
noncomputable def costTail (cfg : WasmConfig) (F : Nat) (lo hi : UInt64) (ab : List UInt8) (h : NearState) : Nat :=
  100 * cfg.regularOpCost +
    (activationGas cfg.regularOpCost (entryLocals f354 [.i32 0, .i32 0, .i32 0]) + 8 * cfg.regularOpCost) +
    (activationGas cfg.regularOpCost (entryLocals f745 [.i32 0, .i32 0, .i32 0]) + 8 * cfg.regularOpCost) +
    (activationGas cfg.regularOpCost (entryLocals f846 [.i32 0, .i32 0]) +
      FmtFormat.cost846 cfg F (2 : UInt32).toNat 17 (cost872 cfg F lo hi (UInt32.ofNat ab.length))) +
    (activationGas cfg.regularOpCost (entryLocals f779 [.i32 0, .i32 0]) + 12 * cfg.regularOpCost) +
    (activationGas cfg.regularOpCost (entryLocals f546 [.i32 0, .i32 0]) +
      (267 * cfg.regularOpCost + logUtf8Use h (logW (decDigits (val lo hi)) ab 4).length)) +
    2 * (activationGas cfg.regularOpCost (entryLocals f68 [.i32 0]) + 315 * cfg.regularOpCost)

theorem sb64 (bs : List UInt8) (h : bs.length = 8) :
    storeBytes (.i64 (UInt64.ofNat (Memory.decodeLE bs))) 8 = bs := by
  have := FtTotalSupplyGetter.storeBytes_load_i64 bs h
  simpa [loadValue] using this

theorem sb64_2 : storeBytes (.i64 2) 8 = bytes32 2 ++ bytes32 0 := by decide

theorem memBytes_eq {n a : Nat} {bs bs' : List UInt8} (h : bs = bs') :
    n ↦[wms][ a ] bs ⊢ (n ↦[wms][ a ] bs' : IProp GF) := by
  subst h; exact .rfl

theorem fIt_le {F : Nat} (hF : 1 ≤ F) {j : Nat} (hj : j ≤ 2) : StrSinkMulti.fIt F j ≤ F + j := by
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 by omega) with rfl | rfl | rfl <;>
    simp [StrSinkMulti.fIt] <;> omega

/-- The bounds the tail leaves on the heap. -/
theorem tail_bounds {hl F hl' F' c0 B : Nat} {ptr cap : UInt32} (hF : 1 ≤ F)
    (h : StrSinkMulti.ssinkOk (hl + 65536) F c0 B ptr cap hl' F') :
    F' + 2 ≤ F + 4 ∧ hl' ≤ hl + 3 * 65536 ∧ hl' % 65536 = 0 ∧ 0 < hl' := by
  obtain ⟨⟨j, hj, hFj, hlj, -⟩, -, h0, h1, -, -⟩ := h
  have := fIt_le hF hj
  have : j * 65536 ≤ 2 * 65536 := Nat.mul_le_mul_right _ hj
  refine ⟨by omega, by omega, h0, h1⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 64000000 in
/-- **The end of `near_deposit`** (232's instructions after `internal_deposit`): the log's
`Arguments` built, `format!` (846), `log_str` of its text (546), the two `String`s dropped (68),
`sp += 144`, `return`. -/
theorem tail232_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (e inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (mx : Option Nat) (hm : IfaceMod mi A n g ta) (hd : d + 26 < lim.maxCallDepth)
    (Cg R : Nat) (gt : GlobalType) (sp self : UInt32) (l2 l3 l5 l6 : UInt64) (l4 : UInt32)
    (hs : 272 ≤ sp.toNat) (hs2 : sp.toNat + 144 ≤ 2 ^ 32 - 16) (hal : sp.toNat % 8 = 0)
    (maxP hl : Nat) (live : List (Nat × Nat)) (F : Nat) (aidx : UInt32)
    (hL1 : hl + 4 * 65536 ≤ 2 ^ 32) (hL2 : hl + 3 * 65536 ≤ maxP * 65536)
    (hr : roomFor hl maxP (FmtFormat.capOf 17)) (hF : VecWithCap.okG F)
    (lo hi : UInt64) (ap : UInt32) (ab : List UInt8) (hab : ab.length ≤ 64) (hab0 : 0 < ab.length)
    (hap : ap.toNat + ab.length ≤ 2 ^ 32) (hlive : (ap.toNat, ab.length) ∈ live)
    (h : NearState) (hok : LogStr.LogOk h (logW (decDigits (val lo hi)) ab 4) (logW (decDigits (val lo hi)) ab 4).length)
    (Φ : Post NearState GF) :
    tailCode e n maxP inst mi A mx ∗ credits Cg (costTail cfg F lo hi ab h + R) ∗
      g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 272) 272 ∗ stk n sp.toNat 24 ∗
      n ↦[wms][ (sp + 40).toNat ] u128Bytes lo hi ∗
      strW n (sp + 56) ap (UInt32.ofNat ab.length) (UInt32.ofNat ab.length) ∗ n ↦[wms][ ap.toNat ] ab ∗
      stk n (sp.toNat + 72) 24 ∗ stk n (sp.toNat + 112) 12 ∗ stk n (sp.toNat + 128) 16 ∗
      tailStat n ta A ∗ vt n 1057464 aidx ta (A 578) ∗ heapInv n maxP hl live F ∗
      Interface.iface n ta A ∗ LogStr.lslot n ta A ∗ mhostPt h ∗
      (∀ (l2' : UInt64) (hl' F' : Nat), ⌜F' ≤ F + 4 ∧ hl' ≤ hl + 3 * 65536 ∧ hl' % 65536 = 0 ∧ 0 < hl'⌝ -∗
        credits Cg R -∗ g ↦[wg] ⟨gt, .i32 (sp + 144)⟩ -∗ stk n (sp.toNat - 272) 272 -∗ stk n sp.toNat 24 -∗
        n ↦[wms][ (sp + 40).toNat ] u128Bytes lo hi -∗ strW n (sp + 56) ap (UInt32.ofNat ab.length)
          (UInt32.ofNat ab.length) -∗
        stk n (sp.toNat + 72) 24 -∗ stk n (sp.toNat + 112) 12 -∗ stk n (sp.toNat + 128) 16 -∗
        tailStat n ta A -∗ vt n 1057464 aidx ta (A 578) -∗
        heapInv n maxP hl' (live.erase (ap.toNat, ab.length)) F' -∗
        Interface.iface n ta A -∗ LogStr.lslot n ta A -∗ mhostPt (LogStr.logged h (logW (decDigits (val lo hi)) ab 4)) -∗
        Φ.ret [] ⟨#[.i32 self, .i32 sp, .i64 l2', .i64 l3, .i32 l4, .i64 l5, .i64 l6], inst, mi⟩)
      ⊢ mwpi cfg lim d ⟨#[.i32 self, .i32 sp, .i64 l2, .i64 l3, .i32 l4, .i64 l5, .i64 l6], inst, mi⟩ []
          tail232 Φ := by
  iintro ⟨#Hk, Hc, Hg, Hlo, Hs24, Hu, HW, Hab, Har, Hout, Harg, HSt, Hvt, Hinv, HI, HL, Hh, Wk⟩
  ihave #Hk' := Hk
  iunfold tailCode at Hk'
  icases Hk' with ⟨#H846c, #Hdrop, #F452, #Hic, #HLc, #F354, #F745, #F846, #F779, #F546, #F68⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold Interface.ifaceCode at Hic
    icases Hic with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩
    iexact Hi
  have hn := hm.mem
  have hg := hm.glob
  have ha354 := hm.funcs 354 (by decide)
  have ha745 := hm.funcs 745 (by decide)
  have ha846 := hm.funcs 846 (by decide)
  have ha779 := hm.funcs 779 (by decide)
  have ha546 := hm.funcs 546 (by decide)
  have ha68 := hm.funcs 68 (by decide)
  have t31 : types[31]!.params.length = 3 := by rfl
  have t14 : types[14]!.params.length = 2 := by rfl
  have t0 : types[0]!.params.length = 1 := by rfl
  have hlt := sp.toNat_lt
  have e8 : (sp + 8).toNat = sp.toNat + 8 := by rw [UInt32.toNat_add]; simp; omega
  have e16 : (sp + 16).toNat = sp.toNat + 16 := by rw [UInt32.toNat_add]; simp; omega
  have e40 : (sp + 40).toNat = sp.toNat + 40 := by rw [UInt32.toNat_add]; simp; omega
  have e56 : (sp + 56).toNat = sp.toNat + 56 := by rw [UInt32.toNat_add]; simp; omega
  have e72 : (sp + 72).toNat = sp.toNat + 72 := by rw [UInt32.toNat_add]; simp; omega
  have e92 : (sp + 92).toNat = sp.toNat + 92 := by rw [UInt32.toNat_add]; simp; omega
  have e112 : (sp + 112).toNat = sp.toNat + 112 := by rw [UInt32.toNat_add]; simp; omega
  have e128 : (sp + 128).toNat = sp.toNat + 128 := by rw [UInt32.toNat_add]; simp; omega
  have hal' : (UInt32.ofNat ab.length).toNat = ab.length := by simp; omega
  have hTL : (logW (decDigits (val lo hi)) ab 4).length ≤ 120 := by
    have := logW_length (decDigits (val lo hi)) ab 4
    have := FmtString.decDigits_le lo hi
    omega
  iunfold costTail at Hc
  -- the frame's words
  icases stkSp 8 16 rfl $$ Hs24 with ⟨S0, Hs16⟩
  icases stkSp 8 8 rfl $$ Hs16 with ⟨S8, S16⟩
  icases stkSp 4 4 rfl $$ S16 with ⟨S16a, S16b⟩
  icases stkSp 4 4 rfl $$ S8 with ⟨S8a, S8b⟩
  iunfold stk at S16a S16b S8a S8b
  icases S16a with ⟨%a0, %ha0, S16a⟩
  icases S16b with ⟨%a4, %ha4, S16b⟩
  icases S8a with ⟨%b0, %hb0, S8a⟩
  icases S8b with ⟨%b4, %hb4, S8b⟩
  ihave S16a := memBytes_addr (show sp.toNat + 8 + 8 = (sp + 16).toNat by omega) $$ S16a
  ihave S16b := memBytes_addr (show sp.toNat + 8 + 8 + 4 = (sp + 16).toNat + 4 by omega) $$ S16b
  ihave S8a := memBytes_addr (show sp.toNat + 8 = (sp + 8).toNat by omega) $$ S8a
  ihave S8b := memBytes_addr (show sp.toNat + 8 + 4 = (sp + 8).toNat + 4 by omega) $$ S8b
  simp only [tail232]
  -- 354: the `u128` argument at sp + 16
  repeat mstep
  mcall (f354_spec (GF := GF) cfg lim (d + 1) types[31]! rfl inst mi n hn Cg (sp + 16) (sp + 40) 5 a0 a4 ha0 ha4)
    using [S16a S16b]
  · iframe S16a S16b
  icases HQ with ⟨%hrs, S16a, S16b⟩
  subst hrs
  ihave S16a := memBytes_addr (show (sp + 16).toNat = sp.toNat + 16 by omega) $$ S16a
  ihave S16b := memBytes_addr (show (sp + 16).toNat + 4 = sp.toNat + 16 + 4 by omega) $$ S16b
  ihave S16 := join64' (a := sp.toNat + 16) (b := sp.toNat + 16 + 4) (sp + 40) 5 rfl $$ [S16a S16b]
  · iframe S16a S16b
  repeat mstep
  mstep [S16]
  repeat mstep
  -- 745: the `String` argument at sp + 8
  mcall (f745_spec (GF := GF) cfg lim (d + 1) types[31]! rfl inst mi n hn Cg (sp + 8) (sp + 56) 6 b0 b4 hb0 hb4)
    using [S8a S8b]
  · iframe S8a S8b
  icases HQ with ⟨%hrs, S8a, S8b⟩
  subst hrs
  ihave S8a := memBytes_addr (show (sp + 8).toNat = sp.toNat + 8 by omega) $$ S8a
  ihave S8b := memBytes_addr (show (sp + 8).toNat + 4 = sp.toNat + 8 + 4 by omega) $$ S8b
  ihave S8 := join64' (a := sp.toNat + 8) (b := sp.toNat + 8 + 4) (sp + 56) 6 rfl $$ [S8a S8b]
  · iframe S8a S8b
  -- the `Arguments` at sp + 72 and the arguments at sp + 128
  icases stkSp 4 20 rfl $$ Har with ⟨R72, Har⟩
  icases stkSp 8 12 rfl $$ Har with ⟨R76, Har⟩
  icases stkSp 4 8 rfl $$ Har with ⟨R84, Har⟩
  icases stkSp 4 4 rfl $$ Har with ⟨R88, R92⟩
  icases stkSp 8 8 rfl $$ Harg with ⟨R128, R136⟩
  iunfold stk at R72 R76 R84 R88 R92 R128 R136
  icases R72 with ⟨%c72, %hc72, R72⟩
  icases R76 with ⟨%c76, %hc76, R76⟩
  icases R84 with ⟨%junk, %hjunk, R84⟩
  icases R88 with ⟨%c88, %hc88, R88⟩
  icases R92 with ⟨%c92, %hc92, R92⟩
  icases R128 with ⟨%c128, %hc128, R128⟩
  icases R136 with ⟨%c136, %hc136, R136⟩
  ihave R92 := memBytes_addr (show sp.toNat + 72 + 4 + 8 + 4 + 4 = (sp + 92).toNat by omega) $$ R92
  ihave R76 := memBytes_addr (show sp.toNat + 72 + 4 = sp.toNat + 76 by omega) $$ R76
  ihave R88 := memBytes_addr (show sp.toNat + 72 + 4 + 8 + 4 = sp.toNat + 88 by omega) $$ R88
  ihave R136 := memBytes_addr (show sp.toNat + 128 + 8 = sp.toNat + 136 by omega) $$ R136
  repeat mstep
  mstep [R92]
  repeat mstep
  mstep [R128]
  repeat mstep
  mstep [R76]
  repeat mstep
  mstep [R72]
  repeat mstep
  mstep [S8]
  mstep [R136]
  repeat mstep
  mstep [R88]
  repeat mstep
  -- the `Arguments` and the arrays as 846 reads them
  ihave R128 := memBytes_eq (sb64 _ (by simp)) $$ R128
  ihave R136 := memBytes_eq (sb64 _ (by simp)) $$ R136
  ihave R76 := memBytes_eq sb64_2 $$ R76
  icases split64' (a := sp.toNat + 128) (b := sp.toNat + 128 + 4) _ _ rfl $$ R128 with ⟨A0, A4⟩
  icases split64' (a := sp.toNat + 136) (b := sp.toNat + 136 + 4) _ _ rfl $$ R136 with ⟨A8, A12⟩
  icases split64' (a := sp.toNat + 76) (b := sp.toNat + 76 + 4) _ _ rfl $$ R76 with ⟨R76, R80⟩
  ihave A0 := memBytes_addr (show sp.toNat + 128 = (sp + 128).toNat by omega) $$ A0
  ihave A4 := memBytes_addr (show sp.toNat + 128 + 4 = (sp + 128).toNat + 4 by omega) $$ A4
  ihave A8 := memBytes_addr (show sp.toNat + 136 = (sp + 128).toNat + 8 by omega) $$ A8
  ihave A12 := memBytes_addr (show sp.toNat + 136 + 4 = (sp + 128).toNat + 12 by omega) $$ A12
  ihave R72 := memBytes_addr (show sp.toNat + 72 = (sp + 72).toNat by omega) $$ R72
  ihave R76 := memBytes_addr (show sp.toNat + 76 = (sp + 72).toNat + 4 by omega) $$ R76
  ihave R80 := memBytes_addr (show sp.toNat + 76 + 4 = (sp + 72).toNat + 8 by omega) $$ R80
  ihave R84 := memBytes_addr (show sp.toNat + 72 + 4 + 8 = (sp + 72).toNat + 12 by omega) $$ R84
  ihave R88 := memBytes_addr (show sp.toNat + 88 = (sp + 72).toNat + 16 by omega) $$ R88
  ihave R92 := memBytes_addr (show (sp + 92).toNat = (sp + 72).toNat + 20 by omega) $$ R92
  iunfold tailStat at HSt
  icases HSt with ⟨HLS, H189, Ht189, Hlut, Hp0, Hp1⟩
  ihave HM := logM_of n ta A (sp + 128) (sp + 40) (sp + 56) $$ [HLS A0 A4 A8 A12]
  · iframe HLS A0 A4 A8 A12
  icases stkSp 224 48 rfl $$ Hlo with ⟨Hlo, H48⟩
  ihave H48 := stkA (show sp.toNat - 272 + 224 = sp.toNat - 48 by omega) $$ H48
  ihave Hout := stkA (show sp.toNat + 112 = (sp + 112).toNat by omega) $$ Hout
  have hab32 : (UInt32.ofNat ab.length).toNat = ab.length := hal'
  have S846 := f846_log (GF := GF) cfg lim (d + 1) types[14]! rfl inst mi A n g ta hm (by omega) Cg gt maxP hl live
    F aidx hL1 hL2 hr hF sp (sp + 112) (sp + 72) (sp + 128) (sp + 40) (sp + 56) ap (UInt32.ofNat ab.length)
    (UInt32.ofNat ab.length) junk hjunk lo hi ab (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) hab32.symm (by omega) (by omega)
  mcall S846 using [Hg H48 R72 R76 R80 R88 R92 R84 HM Hout Hvt Hinv Hlo H189 Ht189 Hu Hlut HW Hab Hp0 Hp1]
  · iframe Hg H48 R84 HM Hout Hvt Hinv
    isplitl [R72 R76 R80 R88 R92]
    · iunfold argsN; iframe R72 R76 R80 R88 R92
    iunfold logP
    rw [show (1066728 : UInt32).toNat + 12 = 1066740 from rfl, show (189 : UInt32).toNat = 189 from rfl]
    iframe Hlo H189 Ht189
    iunfold logX
    iframe Hu Hlut HW Hab Hp0 Hp1
  icases HQ with ⟨%hrs, Hg, H48, HA, R84, %q, HO⟩
  subst hrs
  iunfold logOut at HO
  icases HO with ⟨Hlo, HM, H189, Ht189, HS, HX⟩
  iunfold StrSinkMulti.ssink at HS
  icases HS with ⟨Hvt, %ptr, %cap, %hl', %F', %rest, %⟨hok', hwr⟩, V0, V4, V8, Hb, Hinv⟩
  have hTB := tail_bounds hF hok'
  obtain ⟨⟨j, hj2, -, -, hcj⟩, hcB, -, -, hp0, hpc⟩ := hok'
  have hcap0 : cap ≠ 0 := by
    intro hc0; subst hc0
    have : 1 ≤ 2 ^ j := Nat.one_le_two_pow
    simp at hcj <;> omega
  -- 779: `(ptr, len)` at sp
  icases stkSp 4 4 rfl $$ S0 with ⟨S0a, S0b⟩
  iunfold stk at S0a S0b
  icases S0a with ⟨%o0, %ho0, S0a⟩
  icases S0b with ⟨%o4, %ho4, S0b⟩
  ihave S0a := memBytes_addr (show sp.toNat = (sp : UInt32).toNat by rfl) $$ S0a
  repeat mstep
  mcall (SerdeAccountId.f779_s (GF := GF) cfg lim (d + 1) types[14]! rfl inst mi n hn Cg sp (sp + 112) ptr cap
    (UInt32.ofNat (logW (decDigits (val lo hi)) ab 4).length) o0 o4 ho0 ho4) using [V0 V4 V8 S0a S0b]
  · iframe V0 V4 V8 S0a S0b
  icases HQ with ⟨%hrs, V0, V4, V8, S0a, S0b⟩
  subst hrs
  -- 546: `log_str(ptr, len)`
  repeat mstep
  mstep [S0a]
  repeat mstep
  mstep [S0b]
  repeat mstep
  have hTt : (UInt32.ofNat (logW (decDigits (val lo hi)) ab 4).length).toNat =
      (logW (decDigits (val lo hi)) ab 4).length := by simp; omega
  have hok2 : LogStr.LogOk h (logW (decDigits (val lo hi)) ab 4)
      (UInt32.ofNat (logW (decDigits (val lo hi)) ab 4).length).toNat := by rw [hTt]; exact hok
  icases stkSp 16 32 rfl $$ H48 with ⟨P48, H32⟩
  icases stkSp 16 16 rfl $$ H32 with ⟨P32, H16⟩
  icases stkSp 8 8 rfl $$ H16 with ⟨P16, H8⟩
  icases stkSp 4 4 rfl $$ H8 with ⟨W8, W12⟩
  iunfold stk at W8 W12
  icases W8 with ⟨%s8, %hs8, W8⟩
  icases W12 with ⟨%s12, %hs12, W12⟩
  ihave W8 := memBytes_addr (show sp.toNat - 48 + 16 + 16 + 8 = (sp - 16).toNat + 8 by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le] <;> omega) $$ W8
  ihave W12 := memBytes_addr (show sp.toNat - 48 + 16 + 16 + 8 + 4 = (sp - 16).toNat + 12 by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le] <;> omega) $$ W12
  ihave W8 := memBytes_eq (ReadRegister.bytes32_of s8 hs8) $$ W8
  ihave W12 := memBytes_eq (ReadRegister.bytes32_of s12 hs12) $$ W12
  have h32 : (sp - 16 - 16).toNat = sp.toNat - 48 + 16 := by
    have h1 : (sp - 16).toNat = sp.toNat - 16 := by
      rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
    have h2 : (16 : UInt32) ≤ sp - 16 := by simp [UInt32.le_iff_toNat_le, h1]; omega
    rw [UInt32.toNat_sub_of_le _ _ h2, h1]; simp; omega
  icases ReadRegister.stk_frame4 n _ (sp - 16 - 16) h32 $$ P32 with ⟨%w0, %w4, %w8, %w12, P32⟩
  icases splitB (a := ptr.toNat) (b := ptr.toNat + (logW (decDigits (val lo hi)) ab 4).length)
    (logW (decDigits (val lo hi)) ab 4) rest rfl $$ Hb with ⟨Hb, Hrest⟩
  have S546 := LogStr.f546_spec (GF := GF) cfg lim (d + 1) types[14]! rfl inst mi e A n g ta mx hm (by omega) Cg
    ⟨gt, .i32 sp⟩ sp rfl (by omega) hal h ptr (UInt32.ofNat (logW (decDigits (val lo hi)) ab 4).length)
    (logW (decDigits (val lo hi)) ab 4) hok2 (UInt32.ofNat (Memory.decodeLE s8))
    (UInt32.ofNat (Memory.decodeLE s12)) w0 w4 w8 w12
  rw [hTt] at S546
  mcall S546 using [Hg HI HL W8 W12 P32 Hb Hh]
  · iunfold LogStr.pre
    iframe Hg HI HL W8 W12 P32 Hb Hh
    ipureintro; rfl
  iunfold LogStr.post at HQ
  icases HQ with ⟨%hrs, Hg, HI, HL, W8, W12, P32, Hb, Hh⟩
  subst hrs
  -- 68: the log's `String` freed
  ihave Hblk : block n ptr.toNat cap.toNat $$ [Hb Hrest]
  · iunfold block
    iexists (logW (decDigits (val lo hi)) ab 4) ++ rest
    isplitr; · ipureintro; simp; omega
    iapply joinB (a := ptr.toNat) (b := ptr.toNat + (logW (decDigits (val lo hi)) ab 4).length)
      (logW (decDigits (val lo hi)) ab 4) rest rfl
    iframe Hb Hrest
  repeat mstep
  mcall (DropVec.f68_spec (GF := GF) cfg lim (d + 1) types[0]! rfl inst mi A n g ta hm (by omega) Cg maxP hl'
    ((ptr.toNat, cap.toNat) :: live) F' (sp + 112) ptr cap (UInt32.ofNat (logW (decDigits (val lo hi)) ab 4).length)
    hcap0 (by omega)) using [V0 V4 V8 Hinv Hblk]
  · iunfold DropVec.pre747
    iframe V0 V4 V8 Hinv Hblk
    ipureintro; exact ⟨rfl, List.mem_cons_self⟩
  iunfold DropVec.post747 at HQ
  icases HQ with ⟨%hrs, V0, V4, V8, Hinv⟩
  subst hrs
  rw [show ((ptr.toNat, cap.toNat) :: live).erase (ptr.toNat, cap.toNat) = live by simp]
  -- 68: the account's `String` freed
  iunfold logX at HX
  icases HX with ⟨⟨Hu, Hlut⟩, ⟨HW, Hab⟩, Hp0, Hp1⟩
  iunfold FmtStrPad.strW at HW
  icases HW with ⟨W0, W4, W8a⟩
  ihave Hablk : block n ap.toNat (UInt32.ofNat ab.length).toNat $$ [Hab]
  · iunfold block
    iexists ab
    iframe Hab
    ipureintro; exact hal'.symm
  have hab0' : UInt32.ofNat ab.length ≠ 0 := by
    intro h0
    have h1 : (UInt32.ofNat ab.length).toNat = 0 := by rw [h0]; rfl
    omega
  repeat mstep
  mcall (DropVec.f68_spec (GF := GF) cfg lim (d + 1) types[0]! rfl inst mi A n g ta hm (by omega) Cg maxP hl'
    live (F' + 1) (sp + 56) ap (UInt32.ofNat ab.length) (UInt32.ofNat ab.length) hab0' (by omega))
    using [W0 W4 W8a Hinv Hablk]
  · iunfold DropVec.pre747
    iframe W0 W4 W8a Hinv Hablk
    ipureintro; exact ⟨rfl, by rw [hal']; exact hlive⟩
  iunfold DropVec.post747 at HQ
  icases HQ with ⟨%hrs, W0, W4, W8a, Hinv⟩
  subst hrs
  rw [hal']
  -- what goes back
  have h16 : (sp - 16).toNat = sp.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  ihave P32 := ReadRegister.frame4_stk n _ (sp - 16 - 16) h32 _ _ _ _ $$ P32
  ihave W8 := stkW (b := sp.toNat - 48 + 16 + 16 + 8) _ (by omega) $$ W8
  ihave W12 := stkW (b := sp.toNat - 48 + 16 + 16 + 8 + 4) _ (by omega) $$ W12
  ihave Hs := stkJ (a := sp.toNat - 48 + 16 + 16 + 8) (b := sp.toNat - 48 + 16 + 16 + 8 + 4) (k1 := 4) (k2 := 4)
    (k := 8) rfl rfl $$ [W8 W12]
  · iframe W8 W12
  ihave Hs := stkJ (a := sp.toNat - 48 + 16 + 16) (b := sp.toNat - 48 + 16 + 16 + 8) (k1 := 8) (k2 := 8)
    (k := 16) rfl rfl $$ [P16 Hs]
  · iframe P16 Hs
  ihave Hs := stkJ (a := sp.toNat - 48 + 16) (b := sp.toNat - 48 + 16 + 16) (k1 := 16) (k2 := 16)
    (k := 32) rfl rfl $$ [P32 Hs]
  · iframe P32 Hs
  ihave Hs := stkJ (a := sp.toNat - 48) (b := sp.toNat - 48 + 16) (k1 := 16) (k2 := 32)
    (k := 48) rfl rfl $$ [P48 Hs]
  · iframe P48 Hs
  ihave Hlo := stkJ (a := sp.toNat - 272) (b := sp.toNat - 48) (k1 := 224) (k2 := 48)
    (k := 272) (by omega) rfl $$ [Hlo Hs]
  · iframe Hlo Hs
  ihave S0a := stkW (b := sp.toNat) _ rfl $$ S0a
  ihave S0b := stkW (b := sp.toNat + 4) _ rfl $$ S0b
  ihave S8 := stkB (b := sp.toNat + 8) (k := 8) _ rfl (by simp) $$ S8
  ihave S16 := stkB (b := sp.toNat + 16) (k := 8) _ rfl (by simp) $$ S16
  ihave S0 := stkJ (a := sp.toNat) (b := sp.toNat + 4) (k1 := 4) (k2 := 4) (k := 8) rfl rfl $$ [S0a S0b]
  · iframe S0a S0b
  ihave S0 := stkJ (a := sp.toNat) (b := sp.toNat + 8) (k1 := 8) (k2 := 8) (k := 16) rfl rfl $$ [S0 S8]
  · iframe S0 S8
  ihave S0 := stkJ (a := sp.toNat) (b := sp.toNat + 16) (k1 := 16) (k2 := 8) (k := 24) rfl rfl $$ [S0 S16]
  · iframe S0 S16
  iunfold argsN at HA
  icases HA with ⟨R72, R76, R80, R88, R92⟩
  ihave R72 := stkW (b := sp.toNat + 72) _ (by omega) $$ R72
  ihave R76 := stkW (b := sp.toNat + 72 + 4) _ (by omega) $$ R76
  ihave R80 := stkW (b := sp.toNat + 72 + 8) _ (by omega) $$ R80
  ihave R84 := stkB (b := sp.toNat + 72 + 12) (k := 4) _ (by omega) hjunk $$ R84
  ihave R88 := stkW (b := sp.toNat + 72 + 16) _ (by omega) $$ R88
  ihave R92 := stkW (b := sp.toNat + 72 + 20) _ (by omega) $$ R92
  ihave Ha := stkJ (a := sp.toNat + 72 + 16) (b := sp.toNat + 72 + 20) (k1 := 4) (k2 := 4) (k := 8) rfl rfl
    $$ [R88 R92]
  · iframe R88 R92
  ihave Ha := stkJ (a := sp.toNat + 72 + 12) (b := sp.toNat + 72 + 16) (k1 := 4) (k2 := 8) (k := 12) rfl rfl
    $$ [R84 Ha]
  · iframe R84 Ha
  ihave Ha := stkJ (a := sp.toNat + 72 + 8) (b := sp.toNat + 72 + 12) (k1 := 4) (k2 := 12) (k := 16) rfl rfl
    $$ [R80 Ha]
  · iframe R80 Ha
  ihave Ha := stkJ (a := sp.toNat + 72 + 4) (b := sp.toNat + 72 + 8) (k1 := 4) (k2 := 16) (k := 20) rfl rfl
    $$ [R76 Ha]
  · iframe R76 Ha
  ihave Ha := stkJ (a := sp.toNat + 72) (b := sp.toNat + 72 + 4) (k1 := 4) (k2 := 20) (k := 24) rfl rfl
    $$ [R72 Ha]
  · iframe R72 Ha
  ihave V0 := stkW (b := sp.toNat + 112) _ (by omega) $$ V0
  ihave V4 := stkW (b := sp.toNat + 112 + 4) _ (by omega) $$ V4
  ihave V8 := stkW (b := sp.toNat + 112 + 8) _ (by omega) $$ V8
  ihave Vo := stkJ (a := sp.toNat + 112 + 4) (b := sp.toNat + 112 + 8) (k1 := 4) (k2 := 4) (k := 8) rfl rfl
    $$ [V4 V8]
  · iframe V4 V8
  ihave Vo := stkJ (a := sp.toNat + 112) (b := sp.toNat + 112 + 4) (k1 := 4) (k2 := 8) (k := 12) rfl rfl
    $$ [V0 Vo]
  · iframe V0 Vo
  icases logM_to n ta A (sp + 128) (sp + 40) (sp + 56) $$ HM with ⟨HLS, A0, A4, A8, A12⟩
  ihave A0 := stkW (b := sp.toNat + 128) _ (by omega) $$ A0
  ihave A4 := stkW (b := sp.toNat + 128 + 4) _ (by omega) $$ A4
  ihave A8 := stkW (b := sp.toNat + 128 + 8) _ (by omega) $$ A8
  ihave A12 := stkW (b := sp.toNat + 128 + 12) _ (by omega) $$ A12
  ihave Ag := stkJ (a := sp.toNat + 128 + 8) (b := sp.toNat + 128 + 12) (k1 := 4) (k2 := 4) (k := 8) rfl rfl
    $$ [A8 A12]
  · iframe A8 A12
  ihave Ag := stkJ (a := sp.toNat + 128 + 4) (b := sp.toNat + 128 + 8) (k1 := 4) (k2 := 8) (k := 12) rfl rfl
    $$ [A4 Ag]
  · iframe A4 Ag
  ihave Ag := stkJ (a := sp.toNat + 128) (b := sp.toNat + 128 + 4) (k1 := 4) (k2 := 12) (k := 16) rfl rfl
    $$ [A0 Ag]
  · iframe A0 Ag
  ihave HSt : tailStat n ta A $$ [HLS H189 Ht189 Hlut Hp0 Hp1]
  · iunfold tailStat
    rw [show (1066728 : UInt32).toNat + 12 = 1066740 from rfl, show (189 : UInt32).toNat = 189 from rfl]
    iframe HLS H189 Ht189 Hlut Hp0 Hp1
  ihave HW : strW n (sp + 56) ap (UInt32.ofNat ab.length) (UInt32.ofNat ab.length) $$ [W0 W4 W8a]
  · iunfold strW; iframe W0 W4 W8a
  -- sp += 144; return
  mstep; mstep; mstep; mstep [Hg]
  mstep
  mcredits R
  have hfin : F' + 1 + 1 ≤ F + 4 ∧ hl' ≤ hl + 3 * 65536 ∧ hl' % 65536 = 0 ∧ 0 < hl' :=
    ⟨by omega, hTB.2.1, hTB.2.2.1, hTB.2.2.2⟩
  iapply Wk $$ %(UInt64.ofNat (Memory.decodeLE (bytes32 (sp + 40) ++ bytes32 5))) %hl' %(F' + 1 + 1) %hfin Hc Hg Hlo S0 Hu HW Ha Vo Ag HSt Hvt
    Hinv HI HL Hh

end Spec

end WNear.Binary.DepositTail
