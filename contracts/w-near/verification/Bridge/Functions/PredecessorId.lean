import Bridge.Functions.EnvPredecessor
import Bridge.Functions.ReadRegisterF
import Bridge.Functions.StorageReadWrap
import Bridge.Functions.FromUtf8Gen
import Bridge.Functions.BorshFT
import Bridge.Functions.FmtSink

/-!
# `env::predecessor_account_id()` (526)

```wat
;; 526 predecessor_account_id(out): sp -= 48
;;     455(1055020)                                   ;; register 0 := the predecessor (EnvPredecessor)
;;     523(sp + 8, 0)                                 ;; read_register(0): Some(vec)
;;     498(sp + 32, sp + 8, ..)                       ;; Option::expect: the Vec at sp + 32
;;     512(sp + 8, sp + 32)                           ;; String::from_utf8: Ok(String) at sp + 8
;;     499(out, sp + 8, ..)                           ;; Result::expect: the String at out
;;     sp += 48
;; 512 from_utf8(out, vec): sp -= 32
;;     779(sp + 8, vec); 927(sp + 16, ptr, len)       ;; core::str::from_utf8 on the bytes
;;     Ok: out+4 := vec (12 bytes); out := 0
;;     Err: out+4 := vec; out+16 := the error; out := 1
;;     sp += 32
;; 499 expect(out, res, loc): res = Ok(v): out := v (12 bytes); Err: panic (881)
```

* `f512_ok`: `String::from_utf8` on bytes with `utf8Ok`: `Ok(vec)`.
* `f499_ok`: `Result::<String, _>::expect` on `Ok`: the three words copied.
* `f526_spec`: `env::predecessor_account_id()` on the installed interface, the predecessor's
  bytes UTF-8 (they are a valid account id): the `String` at `out` is a fresh heap block holding
  them, register 0 holds them, at `cost526`.
-/

namespace WNear.Binary.PredecessorId

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary.Interface WNear.Binary.RegisterLen WNear.Binary.ValueReturn
open WNear.Binary.ReadRegister (ifaceR ifaceCodeR rrCode RegOk iface_of_ifaceR stk4_word stk_frame4 frame4_stk)
open WNear.Binary.ReadRegisterF (rrCodeF pre523F post523F cost523F f523_specF optVecAtF)
open WNear.Binary.EnvPredecessor (pslot pCode withPre withPost f455_spec)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_word stk_addr stk_intro roomFor grownLen)
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.AllocInv (heapInv)
open WNear.Binary.VecWithCap (okG)
open WNear.Binary.FromUtf8 (cost927 res927 res927_ok)
open WNear.Binary.FromUtf8Gen (utf8Width)

/-! ## `String::from_utf8` (512) on UTF-8 bytes -/

section L512

variable {GF : BundledGFunctors} [WasmGS NearState GF]

def pre512 (n g : Nat) (gt : GlobalType) (s out v p c l : UInt32) (bs o0 o1 o2 : List UInt8)
    (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 out, .i32 v]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 32) 32 ∗
    n ↦[i32][ v.toNat ] p ∗ n ↦[i32][ v.toNat + 4 ] c ∗ n ↦[i32][ v.toNat + 8 ] l ∗
    n ↦[wms][ p.toNat ] bs ∗ n ↦[wms][ out.toNat ] o0 ∗ n ↦[wms][ out.toNat + 4 ] o1 ∗
    n ↦[wms][ out.toNat + 12 ] o2 ∗ n ↦[wms][ 1071704 ] utf8Width)

def post512 (n g : Nat) (gt : GlobalType) (s out v p c l : UInt32) (bs : List UInt8)
    (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 32) 32 ∗
    n ↦[i32][ v.toNat ] p ∗ n ↦[i32][ v.toNat + 4 ] c ∗ n ↦[i32][ v.toNat + 8 ] l ∗
    n ↦[wms][ p.toNat ] bs ∗ n ↦[i32][ out.toNat ] 0 ∗ n ↦[wms][ out.toNat + 4 ] (bytes32 p ++ bytes32 c) ∗
    n ↦[i32][ out.toNat + 12 ] l ∗ n ↦[wms][ 1071704 ] utf8Width)

/-- The code of 512 (persistent). -/
def code512 (inst : Nat) (A : Nat → Nat) : IProp GF :=
  iprop(A 779 ↪[wf] FuncInst.wasm types[14]! inst f779 ∗ A 927 ↪[wf] FuncInst.wasm types[31]! inst f927)

instance (inst : Nat) (A : Nat → Nat) : Persistent (code512 (GF := GF) inst A) := by
  unfold code512; infer_instance

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **`String::from_utf8(vec)`** (512) on bytes `bs` with `utf8Ok`: `Ok(vec)` at `out`. -/
theorem f512_ok (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g : Nat)
    (hn : mi.memAddrs[0]? = some n) (hg : mi.globalAddrs[0]? = some g)
    (h779 : mi.funcAddrs[779]? = some (A 779)) (h927 : mi.funcAddrs[927]? = some (A 927))
    (hd : d + 2 < lim.maxCallDepth) (Cg : Nat) (gt : GlobalType) (s out v p c l : UInt32)
    (hs : 32 ≤ s.toNat) (bs o0 o1 o2 : List UInt8) (ho0 : o0.length = 4) (ho1 : o1.length = 8)
    (ho2 : o2.length = 4) (hout : out.toNat + 16 ≤ 2 ^ 32) (hv : v.toNat + 12 ≤ 2 ^ 32)
    (hbs : bs.length = l.toNat) (hp : p.toNat + l.toNat ≤ 2 ^ 32) (hok : Utf8.utf8Ok bs = true) :
    inst ↪[inst] mi ∗ code512 inst A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f512 Cg (pre512 n g gt s out v p c l bs o0 o1 o2)
        (fun _ => 80 * cfg.regularOpCost + cost927 l.toNat * cfg.regularOpCost)
        (post512 n g gt s out v p c l bs) := by
  iintro ⟨#Hi, #Hk⟩
  iunfold code512 at Hk
  icases Hk with ⟨#F779, #F927⟩
  have t14 : types[14]!.params.length = 2 := by rfl
  have t31 : types[31]!.params.length = 3 := by rfl
  have hlt := s.toNat_lt
  have h32 : (s - 32).toNat = s.toNat - 32 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have e8 : (s - 32 + 8).toNat = s.toNat - 24 := by simp [UInt32.toNat_add, h32]; omega
  have e16 : (s - 32 + 16).toNat = s.toNat - 16 := by simp [UInt32.toNat_add, h32]; omega
  generalize hK : cost927 l.toNat * cfg.regularOpCost = K
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold pre512 at HP
  icases HP with ⟨%hargs, Hg, Hs, V0, V4, V8, Hb, O0, O1, O2, Hw⟩
  subst hargs
  -- the frame: [0, 8) unused, [8, 16) the slice, [16, 28) the result, [28, 32) unused
  icases stk_split n (s.toNat - 32) 8 24 $$ Hs with ⟨F0, Hs⟩
  icases stk_split n (s.toNat - 32 + 8) 8 16 $$ Hs with ⟨SL, Hs⟩
  icases stk_split n (s.toNat - 32 + 8 + 8) 12 4 $$ Hs with ⟨RS, F28⟩
  iunfold stk at SL RS
  icases SL with ⟨%sb, %hsb, SL⟩
  icases RS with ⟨%rb, %hrb, RS⟩
  ihave SL := memBytes_addr (show s.toNat - 32 + 8 = (s - 32 + 8).toNat by omega) $$ SL
  ihave RS := memBytes_addr (show s.toNat - 32 + 8 + 8 = (s - 32 + 16).toNat by omega) $$ RS
  ihave VV := KeyGet.join64 n v.toNat p c $$ [V0 V4]
  · iframe V0 V4
  ihave VV := BorshFT.joinB (n := n) (a := v.toNat) (b := v.toNat + 8) (bytes32 p ++ bytes32 c) (bytes32 l)
    (by simp [bytes32]) $$ [VV V8]
  · iframe VV V8
  simp only [f512]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep; mstep; mstep
  mcall (VecDeref.f779_spec cfg lim (d + 1) types[14]! rfl inst mi n hn Cg (s - 32 + 8) v sb
      (bytes32 p ++ bytes32 c ++ bytes32 l) hsb (by simp [bytes32])) using [SL VV]
  · iunfold VecDeref.pre
    iframe SL VV
    ipureintro; rfl
  iunfold VecDeref.post at HQ
  icases HQ with ⟨%hrs, SL, VV⟩
  subst hrs
  have hpl : (bytes32 p ++ (bytes32 c ++ bytes32 l)).take 4 ++ (bytes32 p ++ (bytes32 c ++ bytes32 l)).drop 8 =
      bytes32 p ++ bytes32 l := by
    have l4 : ∀ x : UInt32, (bytes32 x).length = 4 := fun x => by simp [bytes32]
    rw [List.take_left' (l4 p), ← List.append_assoc, List.drop_left' (by simp [l4])]
  rw [hpl]; clear hpl
  ihave SL := KeyGet.split64 n (s - 32 + 8).toNat p l $$ SL
  icases SL with ⟨SL0, SL4⟩
  ihave SL0 := memBytes_addr (show (s - 32 + 8).toNat = (s - 32).toNat + 8 by omega) $$ SL0
  ihave SL4 := memBytes_addr (show (s - 32 + 8).toNat + 4 = (s - 32).toNat + 12 by omega) $$ SL4
  mstep; mstep; mstep; mstep; mstep [SL0] with (simp [bytes32, loadWidth, NumType.byteWidth])
  mstep; mstep [SL4] with (simp [bytes32, loadWidth, NumType.byteWidth])
  have S927 := FromUtf8Gen.f927_spec (GF := GF) cfg lim (d + 1) types[31]! rfl inst mi n hn Cg (s - 32 + 16) p l rb bs hrb
      (by omega) hbs hp
  rw [hK] at S927
  mcall S927 using [Hb RS Hw]
  · iframe Hb RS Hw
  icases HQ with ⟨%hrs, Hb, HR, Hw⟩
  subst hrs
  iunfold res927 at HR
  rw [if_pos hok]
  icases HR with ⟨R0, R4, R8⟩
  ihave R0 := memBytes_addr (show (s - 32 + 16).toNat = (s - 32).toNat + 16 by omega) $$ R0
  mstep; mstep
  mstep; mstep
  mstep; mstep [R0]; mstep; mstep
  mstep_taken
  mstep; mstep
  rw [← List.append_assoc]
  ihave VV := BorshFT.splitB (n := n) (a := v.toNat) (b := v.toNat + 8) (bytes32 p ++ bytes32 c) (bytes32 l)
    (by simp [bytes32]) $$ VV
  icases VV with ⟨VV, V8⟩
  mstep [VV]
  rw [VecFromElem.ofNat_decode_pair]
  mstep [O1] with omega
  rw [VecFromElem.storeBytes_pair64]
  mstep; mstep; mstep; mstep; mstep; mstep; mstep [V8]; mstep [O2]
  mstep; mstep
  mstep; mstep; mstep [O0]
  mstep; mstep; mstep; mstep [Hg]
  rw [show s - 32 + 32 = s by simp]
  mcredits R
  iframe Hc
  iunfold post512
  ihave VV := KeyGet.split64 n v.toNat p c $$ VV
  icases VV with ⟨V0, V4⟩
  iframe Hg V0 V4 V8 Hb O0 O1 O2 Hw
  isplitr
  · ipureintro; simp [htype]
  · ihave SL0 := stk_word n _ _ $$ SL0
    ihave SL4 := stk_word n _ _ $$ SL4
    ihave R0 := stk_word n _ _ $$ R0
    ihave R4 := stk_word n _ _ $$ R4
    ihave R8 := stk_word n _ _ $$ R8
    ihave SL := stk_join n _ 4 4 $$ [SL0 SL4]
    · iframe SL0 SL4
    ihave R := stk_join n _ 4 4 $$ [R0 R4]
    · rw [show (s - 32).toNat + 16 + 4 = (s - 32 + 16).toNat + 4 by omega]; iframe R0 R4
    ihave R := stk_join n _ 8 4 $$ [R R8]
    · rw [show (s - 32).toNat + 16 + 8 = (s - 32 + 16).toNat + 8 by omega]; iframe R R8
    ihave SL := stk_join n _ 8 12 $$ [SL R]
    · rw [show (s - 32).toNat + 8 + 8 = (s - 32).toNat + 16 by omega]; iframe SL R
    ihave SL := stk_join n _ 20 4 $$ [SL F28]
    · rw [show (s - 32).toNat + 8 + 20 = s.toNat - 32 + 8 + 8 + 12 by omega]; iframe SL F28
    ihave F := stk_join n _ 8 24 $$ [F0 SL]
    · rw [show s.toNat - 32 + 8 = (s - 32).toNat + 8 by omega]; iframe F0 SL
    iexact F

end L512

/-! ## `Result::expect` (499) on `Ok` -/

section L499

variable {GF : BundledGFunctors} [WasmGS NearState GF]

def pre499 (n g : Nat) (gt : GlobalType) (s out res a b l : UInt32) (ob1 ob2 : List UInt8)
    (args : List Value) : IProp GF :=
  iprop(⌜∃ loc : UInt32, args = [.i32 out, .i32 res, .i32 loc]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
    n ↦[i32][ res.toNat ] 0 ∗ n ↦[wms][ res.toNat + 4 ] (bytes32 a ++ bytes32 b) ∗
    n ↦[i32][ res.toNat + 12 ] l ∗ n ↦[wms][ out.toNat ] ob1 ∗ n ↦[wms][ out.toNat + 8 ] ob2)

def post499 (n g : Nat) (gt : GlobalType) (s out res a b l : UInt32) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
    n ↦[i32][ res.toNat ] 0 ∗ n ↦[wms][ res.toNat + 4 ] (bytes32 a ++ bytes32 b) ∗
    n ↦[i32][ res.toNat + 12 ] l ∗ n ↦[wms][ out.toNat ] (bytes32 a ++ bytes32 b) ∗ n ↦[i32][ out.toNat + 8 ] l)

set_option maxRecDepth 100000 in
/-- **`Result::<String, _>::expect`** (499) on `Ok(v)`: the `String`'s three words copied to `out`. -/
theorem f499_ok (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (n g : Nat)
    (hn : mi.memAddrs[0]? = some n) (hg : mi.globalAddrs[0]? = some g) (Cg : Nat) (gt : GlobalType)
    (s out res a b l : UInt32) (hs : 32 ≤ s.toNat) (ob1 ob2 : List UInt8)
    (hob1 : ob1.length = 8) (hob2 : ob2.length = 4) (hout : out.toNat + 12 ≤ 2 ^ 32)
    (hres : res.toNat + 16 ≤ 2 ^ 32) :
    ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f499 Cg (pre499 n g gt s out res a b l ob1 ob2)
        (fun _ => 30 * cfg.regularOpCost) (post499 n g gt s out res a b l) := by
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold pre499 at HP
  icases HP with ⟨%⟨loc, hargs⟩, Hg, R0, R4, R12, O0, O8⟩
  subst hargs
  have hlt := s.toNat_lt
  simp only [f499]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep
  mstep; mstep [R0]; mstep; mstep
  mstep_taken
  mstep; mstep
  mstep [R4]
  rw [VecFromElem.ofNat_decode_pair]
  mstep [O0]
  rw [VecFromElem.storeBytes_pair64]
  mstep; mstep; mstep; mstep; mstep; mstep; mstep [R12]; mstep [O8]
  mstep; mstep; mstep; mstep [Hg]
  rw [show s - 32 + 32 = s by simp]
  mcredits R
  iframe Hc
  iunfold post499
  iframe Hg R0 R4 R12 O0 O8
  ipureintro; simp [htype]

end L499

/-! ## `env::predecessor_account_id()` (526) -/

section L526

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The code of 526 (persistent). -/
def code526 (e inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n maxP : Nat) (mx : Option Nat) : IProp GF :=
  iprop(rrCodeF e inst mi A n maxP mx ∗ pCode e inst A ∗ code512 inst A ∗
    A 455 ↪[wf] FuncInst.wasm types[0]! inst f455 ∗ A 523 ↪[wf] FuncInst.wasm types[5]! inst f523 ∗
    A 498 ↪[wf] FuncInst.wasm types[39]! inst f498 ∗ A 512 ↪[wf] FuncInst.wasm types[14]! inst f512 ∗
    A 499 ↪[wf] FuncInst.wasm types[31]! inst f499)

instance (e inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n maxP : Nat) (mx : Option Nat) :
    Persistent (code526 (GF := GF) e inst mi A n maxP mx) := by
  unfold code526; infer_instance

def pre526 (n g ta : Nat) (A : Nat → Nat) (gt : GlobalType) (s out idx : UInt32) (maxP len : Nat)
    (live : List (Nat × Nat)) (F : Nat) (ob : List UInt8) (h : NearState) (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 out]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ ifaceR n ta A ∗ pslot n ta A ∗ stk n (s.toNat - 208) 208 ∗
    vt n 1057464 idx ta (A 578) ∗ heapInv n maxP len live F ∗ n ↦[wms][ out.toNat ] ob ∗
    n ↦[wms][ 1071704 ] utf8Width ∗ mhostPt h)

/-- The predecessor's bytes in a fresh heap block `p`, the `String` `(p, L, L)` at `out`. -/
def strAt (n maxP len : Nat) (live : List (Nat × Nat)) (F : Nat) (out : UInt32) (bs : List UInt8) : IProp GF :=
  iprop(∃ p : UInt32, ∃ len' : Nat, ⌜p ≠ 0 ∧ (len' = len ∨ len' = grownLen len (UInt32.ofNat bs.length))⌝ ∗
    heapInv n maxP len' ((p.toNat, bs.length) :: live) F ∗ n ↦[wms][ p.toNat ] bs ∗
    n ↦[i32][ out.toNat ] p ∗ n ↦[i32][ out.toNat + 4 ] UInt32.ofNat bs.length ∗
    n ↦[i32][ out.toNat + 8 ] UInt32.ofNat bs.length)

def post526 (n g ta : Nat) (A : Nat → Nat) (gt : GlobalType) (s out idx : UInt32) (maxP len : Nat)
    (live : List (Nat × Nat)) (F : Nat) (h : NearState) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ ifaceR n ta A ∗ pslot n ta A ∗ stk n (s.toNat - 208) 208 ∗
    vt n 1057464 idx ta (A 578) ∗ strAt n maxP len live F out h.context.predecessorAccountId ∗
    n ↦[wms][ 1071704 ] utf8Width ∗ mhostPt (predecessorHost h 0))

/-- The cost of 526, activation excluded. -/
def cost526 (cfg : WasmConfig) (F : Nat) (h : NearState) : Nat :=
  600 * cfg.regularOpCost + predecessorUse h + cost523F cfg F (predecessorHost h 0) 0 +
    cost927 h.context.predecessorAccountId.length * cfg.regularOpCost

theorem predecessorHost_reg (h : NearState) :
    (predecessorHost h 0).registers (UInt64.toNat 0) = some h.context.predecessorAccountId := by
  simp [predecessorHost, u64Max, NearState.setRegister]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **`env::predecessor_account_id()`** (526) on the installed interface, outside a view call, the
predecessor a valid account id within the register limit, UTF-8, with room for its block: the
`String` at `out` (`strAt`), register 0 holding the predecessor. -/
theorem f526_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (e : Nat) (A : Nat → Nat)
    (n g ta : Nat) (mx : Option Nat) (hm : IfaceMod mi A n g ta) (hd : d + 14 < lim.maxCallDepth)
    (Cg : Nat) (gt : GlobalType) (s out : UInt32) (hs : 208 ≤ s.toNat) (hal : s.toNat % 8 = 0)
    (hout : out.toNat + 12 ≤ 2 ^ 32) (idx : UInt32) (maxP len : Nat) (live : List (Nat × Nat)) (F : Nat)
    (hF : okG F) (ob : List UInt8) (hob : ob.length = 12) (h : NearState)
    (hview : h.context.isView = false)
    (hvalid : h.config.validAccountId h.context.predecessorAccountId = true)
    (hlim : withinLimit h.config.maxRegisterLen h.context.predecessorAccountId.length = true)
    (hok : RegOk maxP len (some h.context.predecessorAccountId))
    (hutf : Utf8.utf8Ok h.context.predecessorAccountId = true) :
    code526 e inst mi A n maxP mx
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f526 Cg
        (pre526 n g ta A gt s out idx maxP len live F ob h)
        (fun _ => cost526 cfg F h)
        (post526 n g ta A gt s out idx maxP len live F h) := by
  iintro #Hk
  iunfold code526 at Hk
  icases Hk with ⟨#Hrr, #HP, #H512, #F455, #F523, #F498, #F512, #F499⟩
  ihave #Hcode : ifaceCode e inst mi A n mx $$ []
  · iunfold rrCodeF, rrCode, ifaceCodeR at Hrr
    icases Hrr with ⟨⟨⟨#H, -⟩, -⟩, -⟩
    iexact H
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold ifaceCode at Hcode
    icases Hcode with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩
    iexact Hi
  ihave #HcP : (ifaceCode (GF := GF) e inst mi A n mx ∗ pCode e inst A) $$ []
  · iframe Hcode HP
  set pred := h.context.predecessorAccountId with hpred
  obtain ⟨hL0, hL28, hroom⟩ := hok
  have hn := hm.mem
  have hg := hm.glob
  have ha455 := hm.funcs 455 (by decide)
  have ha523 := hm.funcs 523 (by decide)
  have ha498 := hm.funcs 498 (by decide)
  have ha512 := hm.funcs 512 (by decide)
  have ha499 := hm.funcs 499 (by decide)
  have t0 : types[0]!.params.length = 1 := by rfl
  have t5 : types[5]!.params.length = 2 := by rfl
  have t39 : types[39]!.params.length = 5 := by rfl
  have t14 : types[14]!.params.length = 2 := by rfl
  have t31 : types[31]!.params.length = 3 := by rfl
  have hlt := s.toNat_lt
  have h48 : (s - 48).toNat = s.toNat - 48 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have h64 : (s - 48 - 16).toNat = s.toNat - 64 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le, h48] <;> omega
  have e8 : (s - 48 + 8).toNat = s.toNat - 40 := by simp [UInt32.toNat_add, h48]; omega
  have e32 : (s - 48 + 32).toNat = s.toNat - 16 := by simp [UInt32.toNat_add, h48]; omega
  have hLn : (UInt32.ofNat pred.length).toNat = pred.length := by
    simp; omega
  have S455 := fun w0 w4 w8 w12 => f455_spec (GF := GF) cfg lim (d + 1) types[0]! rfl inst mi e A n g ta mx hm
    (by omega) Cg ⟨gt, .i32 (s - 48)⟩ (s - 48) rfl (by omega) (by omega) h hview hvalid hlim w0 w4 w8 w12
  generalize hKp : predecessorUse h = Kp at S455
  generalize hK523 : cost523F cfg F (predecessorHost h 0) 0 = K523
  generalize hK927 : cost927 pred.length * cfg.regularOpCost = K927
  unfold cost526
  rw [hKp, hK523, ← hpred, hK927]
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HPre Hc
  iunfold pre526 at HPre
  icases HPre with ⟨%hargs, Hg, HI, HPs, Hs, Hvt, Hinv, Ho, Hw, Hhost⟩
  subst hargs
  -- the stack: Lo (160) below the frame; the frame F0 (8) O (12) X (4) Y (8) V (12) Z (4)
  icases stk_split n (s.toNat - 208) 160 48 $$ Hs with ⟨Lo, Fr⟩
  rw [show s.toNat - 208 + 160 = s.toNat - 48 by omega]
  icases stk_split n (s.toNat - 48) 8 40 $$ Fr with ⟨F0, Fr⟩
  icases stk_split n (s.toNat - 48 + 8) 12 28 $$ Fr with ⟨O, Fr⟩
  icases stk_split n (s.toNat - 48 + 8 + 12) 4 24 $$ Fr with ⟨X, Fr⟩
  icases stk_split n (s.toNat - 48 + 8 + 12 + 4) 8 16 $$ Fr with ⟨Y, Fr⟩
  icases stk_split n (s.toNat - 48 + 8 + 12 + 4 + 8) 12 4 $$ Fr with ⟨V, Z⟩
  icases stk_split n (s.toNat - 208) 144 16 $$ Lo with ⟨Lo, Lf⟩
  icases stk_frame4 n (s.toNat - 208 + 144) (s - 48 - 16) (by omega) $$ Lf with ⟨%w0, %w4, %w8, %w12, Lf⟩
  ihave HI := iface_of_ifaceR n ta A $$ HI
  icases HI with ⟨HI, HS12⟩
  ihave #S455' := S455 w0 w4 w8 w12 $$ HcP
  simp only [f526]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep
  mcall S455' using [Hg HI HPs Lf Hhost] with (mstep_norm_full; omega)
  · iunfold EnvPredecessor.withPre
    iframe Hg HI HPs Lf Hhost
    ipureintro; rfl
  iunfold EnvPredecessor.withPost at HQ
  icases HQ with ⟨%hrs, Hg, HI, HPs, Lf, Hhost⟩
  subst hrs
  -- read_register(0)
  ihave Lf := frame4_stk n (s.toNat - 208 + 144) (s - 48 - 16) (by omega) _ _ _ _ $$ Lf
  ihave Lo := stk_join n (s.toNat - 208) 144 16 $$ [Lo Lf]
  · iframe Lo Lf
  ihave Lo := stk_addr (show s.toNat - 208 = (s - 48).toNat - 160 by omega) $$ Lo
  iunfold stk at O
  icases O with ⟨%obb, %hobb, O⟩
  ihave O := memBytes_addr (show s.toNat - 48 + 8 = (s - 48 + 8).toNat by omega) $$ O
  have S523 := f523_specF (GF := GF) cfg lim (d + 1) types[5]! rfl inst mi e A n g ta mx hm (by omega) Cg gt
    (s - 48) (s - 48 + 8) (by omega) (by omega) (by omega) 0 idx maxP len live F hF obb hobb (predecessorHost h 0)
    (by rw [predecessorHost_reg]; exact ⟨hL0, hL28, hroom⟩)
  rw [hK523] at S523
  ihave #S523' := S523 $$ Hrr
  mstep; mstep; mstep; mstep
  mcall S523' using [Hg HI HS12 Lo Hvt Hinv O Hhost] with (mstep_norm_full; omega)
  · iunfold pre523F, ifaceR
    iframe Hg HI HS12 Lo Hvt Hinv O Hhost
    ipureintro; rfl
  iunfold post523F at HQ
  icases HQ with ⟨%hrs, Hg, HIR, Lo, Hvt, HV, Hhost⟩
  subst hrs
  rw [predecessorHost_reg]
  iunfold optVecAtF at HV
  icases HV with ⟨%p, P0, P4, P8, %len', %⟨hp0, hl'⟩, Hinv, Pb⟩
  icases FmtSink.heapInv_bound (p := p.toNat) (s := pred.length) (by simp [hpred]) $$ Hinv with ⟨%hpb, Hinv⟩
  -- Option::expect: the Vec at sp + 32
  iunfold stk at V
  icases V with ⟨%vb, %hvb, V⟩
  ihave V := memBytes_addr (show s.toNat - 48 + 8 + 12 + 4 + 8 = (s - 48 + 32).toNat by omega) $$ V
  mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
  mcall (StorageReadWrap.f498_spec cfg lim (d + 1) types[39]! rfl inst mi n hn Cg (s - 48 + 32) (s - 48 + 8) p
      (UInt32.ofNat pred.length) (UInt32.ofNat pred.length) vb hvb hp0 (by omega) (by omega)) using [P0 P4 P8 V]
  · iunfold StorageReadWrap.pre498
    iframe P0 P4 P8 V
    ipureintro; exact ⟨_, _, _, rfl⟩
  iunfold StorageReadWrap.post498 at HQ
  icases HQ with ⟨%hrs, P0, P4, P8, V0, V4, V8⟩
  subst hrs
  -- String::from_utf8: Ok(String) at sp + 8
  iunfold stk at X
  icases X with ⟨%xb, %hxb, X⟩
  ihave X := memBytes_addr (show s.toNat - 48 + 8 + 12 = (s - 48 + 8).toNat + 12 by omega) $$ X
  ihave P48 := KeyGet.join64 n ((s - 48 + 8).toNat + 4) (UInt32.ofNat pred.length) (UInt32.ofNat pred.length)
    $$ [P4 P8]
  · rw [show (s - 48 + 8).toNat + 4 + 4 = (s - 48 + 8).toNat + 8 by omega]; iframe P4 P8
  ihave Lo := stk_addr (show (s - 48).toNat - 160 = s.toNat - 208 by omega) $$ Lo
  icases stk_split n (s.toNat - 208) 128 32 $$ Lo with ⟨Lo, L32⟩
  ihave L32 := stk_addr (show s.toNat - 208 + 128 = (s - 48).toNat - 32 by omega) $$ L32
  have S512 := f512_ok (GF := GF) cfg lim (d + 1) types[14]! rfl inst mi A n g hn hg
    (hm.funcs 779 (by decide)) (hm.funcs 927 (by decide)) (by omega) Cg gt (s - 48) (s - 48 + 8) (s - 48 + 32)
    p (UInt32.ofNat pred.length) (UInt32.ofNat pred.length) (by omega) pred (bytes32 p)
    (bytes32 (UInt32.ofNat pred.length) ++ bytes32 (UInt32.ofNat pred.length)) xb (by simp [bytes32])
    (by simp [bytes32]) hxb (by omega) (by omega) hLn.symm (by omega) hutf
  rw [hLn, hK927] at S512
  ihave #S512' := S512 $$ [Hi H512]
  · iframe Hi H512
  mstep; mstep; mstep; mstep; mstep; mstep
  mcall S512' using [Hg L32 V0 V4 V8 Pb P0 P48 X Hw] with (mstep_norm_full; omega)
  · iunfold pre512
    iframe Hg L32 V0 V4 V8 Pb P0 P48 X Hw
    ipureintro; rfl
  iunfold post512 at HQ
  icases HQ with ⟨%hrs, Hg, L32, V0, V4, V8, Pb, R0, R4, R12, Hw⟩
  subst hrs
  -- Result::expect: the String at out
  have ho8 : (ob.take 8).length = 8 := by simp; omega
  have ho4 : (ob.drop 8).length = 4 := by simp; omega
  ihave Ho := U128From.memBytes_split n out.toNat 8 ob (by omega) $$ Ho
  icases Ho with ⟨Ho0, Ho8⟩
  mstep; mstep; mstep; mstep; mstep
  mcall (f499_ok cfg lim (d + 1) types[31]! rfl inst mi n g hn hg Cg gt (s - 48) out (s - 48 + 8) p
      (UInt32.ofNat pred.length) (UInt32.ofNat pred.length) (by omega) (ob.take 8) (ob.drop 8) ho8 ho4 hout
      (by omega)) using [Hg R0 R4 R12 Ho0 Ho8]
  · iunfold pre499
    iframe Hg R0 R4 R12 Ho0 Ho8
    ipureintro; exact ⟨_, rfl⟩
  iunfold post499 at HQ
  icases HQ with ⟨%hrs, Hg, R0, R4, R12, Ho0, Ho8⟩
  subst hrs
  mstep; mstep; mstep; mstep [Hg]
  rw [show s - 48 + 48 = s by simp]
  mcredits R
  iframe Hc
  iunfold post526
  isplitr
  · ipureintro; simp [htype]
  iframe Hg HPs Hvt Hw Hhost
  isplitl [HIR]
  · iexact HIR
  isplitr [Ho0 Ho8 Hinv Pb]
  · ihave R0 := BorshFT.stkW (n := n) (b := s.toNat - 40) _ (by omega) $$ R0
    ihave R4 := BorshFT.stkB (n := n) (b := s.toNat - 36) (k := 8) _ (by omega) (by simp [bytes32]) $$ R4
    ihave R12 := BorshFT.stkW (n := n) (b := s.toNat - 28) _ (by omega) $$ R12
    ihave V0 := BorshFT.stkW (n := n) (b := s.toNat - 16) _ (by omega) $$ V0
    ihave V4 := BorshFT.stkW (n := n) (b := s.toNat - 12) _ (by omega) $$ V4
    ihave V8 := BorshFT.stkW (n := n) (b := s.toNat - 8) _ (by omega) $$ V8
    ihave Y := BorshFT.stkA (n := n) (k := 8) (b := s.toNat - 24) (by omega) $$ Y
    ihave Z := BorshFT.stkA (n := n) (k := 4) (b := s.toNat - 4) (by omega) $$ Z
    ihave L32 := BorshFT.stkA (n := n) (k := 32) (b := s.toNat - 80) (by omega) $$ L32
    ihave S := BorshFT.stkJ (n := n) (a := s.toNat - 208) (b := s.toNat - 80) (k1 := 128) (k2 := 32) (k := 160)
      (by omega) (by omega) $$ [Lo L32]
    · iframe Lo L32
    ihave S := BorshFT.stkJ (n := n) (a := s.toNat - 208) (b := s.toNat - 48) (k1 := 160) (k2 := 8) (k := 168)
      (by omega) (by omega) $$ [S F0]
    · iframe S F0
    ihave S := BorshFT.stkJ (n := n) (a := s.toNat - 208) (b := s.toNat - 40) (k1 := 168) (k2 := 4) (k := 172)
      (by omega) (by omega) $$ [S R0]
    · iframe S R0
    ihave S := BorshFT.stkJ (n := n) (a := s.toNat - 208) (b := s.toNat - 36) (k1 := 172) (k2 := 8) (k := 180)
      (by omega) (by omega) $$ [S R4]
    · iframe S R4
    ihave S := BorshFT.stkJ (n := n) (a := s.toNat - 208) (b := s.toNat - 28) (k1 := 180) (k2 := 4) (k := 184)
      (by omega) (by omega) $$ [S R12]
    · iframe S R12
    ihave S := BorshFT.stkJ (n := n) (a := s.toNat - 208) (b := s.toNat - 24) (k1 := 184) (k2 := 8) (k := 192)
      (by omega) (by omega) $$ [S Y]
    · iframe S Y
    ihave S := BorshFT.stkJ (n := n) (a := s.toNat - 208) (b := s.toNat - 16) (k1 := 192) (k2 := 4) (k := 196)
      (by omega) (by omega) $$ [S V0]
    · iframe S V0
    ihave S := BorshFT.stkJ (n := n) (a := s.toNat - 208) (b := s.toNat - 12) (k1 := 196) (k2 := 4) (k := 200)
      (by omega) (by omega) $$ [S V4]
    · iframe S V4
    ihave S := BorshFT.stkJ (n := n) (a := s.toNat - 208) (b := s.toNat - 8) (k1 := 200) (k2 := 4) (k := 204)
      (by omega) (by omega) $$ [S V8]
    · iframe S V8
    ihave S := BorshFT.stkJ (n := n) (a := s.toNat - 208) (b := s.toNat - 4) (k1 := 204) (k2 := 4) (k := 208)
      (by omega) (by omega) $$ [S Z]
    · iframe S Z
    iexact S
  · iunfold strAt
    iexists p, len'
    ihave Ho0 := KeyGet.split64 n out.toNat p (UInt32.ofNat pred.length) $$ Ho0
    icases Ho0 with ⟨Ho0, Ho4⟩
    iframe Hinv Pb Ho0 Ho4 Ho8
    ipureintro; exact ⟨hp0, hl'⟩

end L526

end WNear.Binary.PredecessorId
