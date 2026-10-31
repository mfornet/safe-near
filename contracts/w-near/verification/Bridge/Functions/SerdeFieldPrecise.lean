import NearLogic.Tactic.Control
import Bridge.Functions.SerdeKeyPrecise
import Bridge.Functions.SerdeNextKey

set_option maxRecDepth 100000

namespace WNear.Binary.SerdeKeyTight
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.SerdeKey
section Proof
variable {GF : BundledGFunctors} [WasmGS NearState GF]
theorem f755_length_ne (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (n : Nat)
    (hn : mi.memAddrs[0]? = some n) (a953 : Nat) (ha953 : mi.funcAddrs[953]? = some a953)
    (hd : d + 1 < lim.maxCallDepth) (Cg : Nat) (a la b lb : UInt32) (xs ys : List UInt8)
    (hx : xs.length = la.toNat) (hy : ys.length = lb.toNat)
    (ha : a.toNat + la.toNat ≤ 2 ^ 32) (hb : b.toNat + lb.toNat ≤ 2 ^ 32) (hl : la ≠ lb) :
    a953 ↪[wf] FuncInst.wasm types[15]! inst f953 ∗ inst ↪[inst] mi ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f755 Cg
        (fun args => iprop(⌜args = [.i32 a, .i32 la, .i32 b, .i32 lb]⌝ ∗ n ↦[wms][ a.toNat ] xs ∗
          n ↦[wms][ b.toNat ] ys))
        (fun _ => 30 * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗
          n ↦[wms][ a.toNat ] xs ∗ n ↦[wms][ b.toNat ] ys)) := by
  iintro ⟨#F953, #Hi⟩
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hx, Hy⟩
  subst hargs
  have hc : Numeric.bool (Numeric.irelop32 IRelOp.ne la lb) = 1 := by
    simp [Numeric.bool, Numeric.irelop32, hl]
  simp only [f755]
  repeat mstep
  isplitl [Hc]
  · iapply BorrowMut.credits_le
    iframe Hc
    ipureintro; omega
  iframe Hx Hy
  ipureintro
  simp [htype]

theorem f754_length_ne (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (n : Nat)
    (hn : mi.memAddrs[0]? = some n) (a755 a953 : Nat) (ha755 : mi.funcAddrs[755]? = some a755)
    (ha953 : mi.funcAddrs[953]? = some a953)
    (hd : d + 2 < lim.maxCallDepth) (Cg : Nat) (a la b lb : UInt32) (xs ys : List UInt8)
    (hx : xs.length = la.toNat) (hy : ys.length = lb.toNat)
    (ha : a.toNat + la.toNat ≤ 2 ^ 32) (hb : b.toNat + lb.toNat ≤ 2 ^ 32) (hl : la ≠ lb) :
    a755 ↪[wf] FuncInst.wasm types[33]! inst f755 ∗ a953 ↪[wf] FuncInst.wasm types[15]! inst f953 ∗
      inst ↪[inst] mi ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f754 Cg
        (fun args => iprop(⌜args = [.i32 a, .i32 la, .i32 b, .i32 lb]⌝ ∗ n ↦[wms][ a.toNat ] xs ∗
          n ↦[wms][ b.toNat ] ys))
        (fun _ => 50 * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗
          n ↦[wms][ a.toNat ] xs ∗ n ↦[wms][ b.toNat ] ys)) := by
  iintro ⟨#F755, #F953, #Hi⟩
  ihave #S755 := f755_length_ne (GF := GF) cfg lim (d + 1) types[33]! (by rfl) inst mi n hn a953 ha953 (by omega) Cg
    a la b lb xs ys hx hy ha hb hl $$ [F953 Hi]
  · iframe F953 Hi
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hx, Hy⟩
  subst hargs
  have t33 : types[33]!.params.length = 4 := by rfl
  simp only [f754, cost754]
  rw [show (20 + 30) * cfg.regularOpCost + R = 20 * cfg.regularOpCost + (30 * cfg.regularOpCost + R) by
    rw [Nat.add_mul]; omega]
  have e := Nat.add_mul 12 (30) cfg.regularOpCost
  repeat mstep
  mcall S755 using [Hx Hy]
  · iframe Hx Hy
  icases HQ with ⟨%hrs, Hx, Hy⟩
  subst hrs
  rw [show 16 * cfg.regularOpCost + (30 * cfg.regularOpCost + R) -
    (12 + 30) * cfg.regularOpCost = 4 * cfg.regularOpCost + R by rw [Nat.add_mul]; omega]
  iapply NearLogic.mfunc_normal_intro' (K := 4 * cfg.regularOpCost + R)
  iframe Hc
  isplitr
  · ipureintro; simp [htype]
  iintro Hc
  simp only [htype, List.length_cons, List.length_nil, Nat.add_zero, Nat.sub_self, List.drop_zero]
  isplitl [Hc]
  · iapply BorrowMut.credits_le
    iframe Hc
    ipureintro; omega
  iframe Hx Hy

theorem f194_length_ne (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (n : Nat)
    (hn : mi.memAddrs[0]? = some n) (a754 a755 a953 : Nat) (ha754 : mi.funcAddrs[754]? = some a754)
    (ha755 : mi.funcAddrs[755]? = some a755) (ha953 : mi.funcAddrs[953]? = some a953)
    (hd : d + 3 < lim.maxCallDepth) (Cg : Nat) (p k : UInt32) (key : List UInt8)
    (hk : key.length = k.toNat) (hp : p.toNat + k.toNat ≤ 2 ^ 32) (hne : key.length ≠ 10) :
    a754 ↪[wf] FuncInst.wasm types[33]! inst f754 ∗ a755 ↪[wf] FuncInst.wasm types[33]! inst f755 ∗
      a953 ↪[wf] FuncInst.wasm types[15]! inst f953 ∗ inst ↪[inst] mi ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f194 Cg
        (fun args => iprop(⌜args = [.i32 p, .i32 k]⌝ ∗ n ↦[wms][ p.toNat ] key ∗
          n ↦[wms][ 1051092 ] WNear.BalanceOfArgs.keyBytes))
        (fun _ => 80 * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = [.i64 256]⌝ ∗
          n ↦[wms][ p.toNat ] key ∗ n ↦[wms][ 1051092 ] WNear.BalanceOfArgs.keyBytes)) := by
  iintro ⟨#F754, #F755, #F953, #Hi⟩
  have hkl : WNear.BalanceOfArgs.keyBytes.length = (10 : UInt32).toNat := rfl
  ihave #S754 := f754_length_ne (GF := GF) cfg lim (d + 1) types[33]! (by rfl) inst mi n hn a755 a953 ha755 ha953
    (by omega) Cg p k 1051092 10 key WNear.BalanceOfArgs.keyBytes hk hkl hp (by decide) (by intro h; apply hne; rw [hk, h]; rfl) $$ [F755 F953 Hi]
  · iframe F755 F953 Hi
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hk, Hd⟩
  subst hargs
  have t33 : types[33]!.params.length = 4 := by rfl
  simp only [f194]
  rw [show (30 + 50) * cfg.regularOpCost + R = 30 * cfg.regularOpCost + (50 * cfg.regularOpCost + R) by
    rw [Nat.add_mul]; omega]
  have e := Nat.add_mul 11 (50) cfg.regularOpCost
  repeat mstep
  mcall S754 using [Hk Hd]
  · iframe Hk Hd
  icases HQ with ⟨%hrs, Hk, Hd⟩
  subst hrs
  rw [show 24 * cfg.regularOpCost + (50 * cfg.regularOpCost + R) -
    (11 + 50) * cfg.regularOpCost = 13 * cfg.regularOpCost + R by rw [Nat.add_mul]; omega]
  have h := mwpi_select_false (GF := GF) (vs := []) (cfg := cfg) (lim := lim) (d := d)
    (f := { locals := #[Value.i32 p, Value.i32 k], inst := inst, mi := mi }) (Cg := Cg) (R := 12 * cfg.regularOpCost + R)
    (Φ := Post.mfunc cfg Cg type.results.length
      { ret := fun rs => iprop(credits Cg R ∗ ⌜rs = [Value.i64 256]⌝ ∗
          n ↦[wms][ p.toNat ] key ∗ n ↦[wms][ 1051092 ] WNear.BalanceOfArgs.keyBytes) })
    none (.i64 0) (.i64 256)
  simp only [List.nil_append] at h
  rw [show 13 * cfg.regularOpCost + R = cfg.regularOpCost + (12 * cfg.regularOpCost + R) by omega]
  iapply h
  isplitl [Hc]
  · iexact Hc
  inext
  iintro Hc
  iapply NearLogic.mfunc_normal_intro' (K := 12 * cfg.regularOpCost + R)
  iframe Hc
  isplitr
  · ipureintro; simp [htype]
  iintro Hc
  simp only [htype, List.length_cons, List.length_nil, Nat.add_zero, Nat.sub_self, List.drop_zero]
  isplitl [Hc]
  · iapply BorrowMut.credits_le
    iframe Hc
    ipureintro; omega
  iframe Hk Hd

def fieldCost (key : List UInt8) : Nat := if key.length = 10 then SerdeKey.cost194 else 80

theorem f194_precise (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (n : Nat)
    (hn : mi.memAddrs[0]? = some n) (a754 a755 a953 : Nat) (ha754 : mi.funcAddrs[754]? = some a754)
    (ha755 : mi.funcAddrs[755]? = some a755) (ha953 : mi.funcAddrs[953]? = some a953)
    (hd : d + 3 < lim.maxCallDepth) (Cg : Nat) (p k : UInt32) (key : List UInt8)
    (hk : key.length = k.toNat) (hp : p.toNat + k.toNat ≤ 2 ^ 32) :
    a754 ↪[wf] FuncInst.wasm types[33]! inst f754 ∗ a755 ↪[wf] FuncInst.wasm types[33]! inst f755 ∗
      a953 ↪[wf] FuncInst.wasm types[15]! inst f953 ∗ inst ↪[inst] mi ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f194 Cg
        (fun args => iprop(⌜args = [.i32 p, .i32 k]⌝ ∗ n ↦[wms][ p.toNat ] key ∗
          n ↦[wms][ 1051092 ] WNear.BalanceOfArgs.keyBytes))
        (fun _ => fieldCost key * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = [.i64 (if key = WNear.BalanceOfArgs.keyBytes then 0 else 256)]⌝ ∗
          n ↦[wms][ p.toNat ] key ∗ n ↦[wms][ 1051092 ] WNear.BalanceOfArgs.keyBytes)) := by
  by_cases hlen : key.length = 10
  · simp only [fieldCost, if_pos hlen]
    exact SerdeKey.f194_spec cfg lim d type htype inst mi n hn a754 a755 a953 ha754 ha755 ha953 hd Cg p k key hk hp
  · have hkey : key ≠ WNear.BalanceOfArgs.keyBytes := by
      intro heq
      apply hlen
      rw [heq]
      rfl
    simp only [fieldCost, if_neg hlen, if_neg hkey]
    exact f194_length_ne cfg lim d type htype inst mi n hn a754 a755 a953 ha754 ha755 ha953 hd Cg p k key hk hp hlen

theorem fieldCost_le_legacy (key : List UInt8) : fieldCost key ≤ SerdeKey.cost194 := by
  unfold fieldCost
  split
  · exact le_rfl
  · decide

end Proof
end WNear.Binary.SerdeKeyTight
namespace WNear.Binary.SerdeNextKeyTight
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.AllocTwo (code310)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_intro stk_word stk_addr)
open WNear.Binary.SerdeRead (rd optByte wsLen)
open WNear.Binary.SerdeErrBox (errCode costErr heapA roomFor4)
open WNear.Binary.SerdeEnds (endCode some_bit byte_is125 byte_is44 byte_is34)

open WNear.Binary.SerdeNextKey
section Proof
variable {GF : BundledGFunctors} [WasmGS NearState GF]

set_option hygiene false in
/-- The key block of 193, from its `block`s to the end of the function: the quote at `jq`, eaten;
the scratch cleared (82); `parse_str` (646, `S646`); the field visitor (194) on its reference. -/
local macro "key_tail_tight" : tactic => `(tactic| (
  mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
  rw [SerdeRead.optByte_byte]
  mstep; mstep; mstep
  mstep_taken with decide
  mstep; mstep [Hacc]; mstep
  mcall (SerdeRead.f333_spec cfg lim (d + 1) types[0]! (by rfl) inst mi n hn Cg de ptr bs jq (getElem_lt hq1)
    (by omega) (by omega)) using [Hrd]
  · iframe Hrd
  icases HQ with ⟨%hrs, Hrd⟩
  subst hrs
  mcredits (150 * cfg.regularOpCost + (K646 + (C194 + R)))
  mstep; mstep; mstep; mstep
  mcall S82 using [Hsc]
  · iframe Hsc
  icases HQ with ⟨%hrs, Hsc⟩
  subst hrs
  mcredits (100 * cfg.regularOpCost + (K646 + (C194 + R)))
  mstep; mstep; mstep
  mcall S646 using [Hg H160 Hob Hrd Hsc HP]
  · iframe Hg H160 Hob Hrd Hsc HP
  icases HQ with ⟨%hrs, Hg, H160, %t, %p, %⟨hp, hkl⟩, O0, O4, O8, O12, Hk, Hw⟩
  subst hrs
  mcredits (60 * cfg.regularOpCost + (C194 + R))
  mstep; mstep; mstep [O0]; mstep; mstep
  mstep_taken with decide
  mstep; mstep; mstep; mstep; mstep
  mstep [O8] with (simp [UInt32.toNat_add]; omega)
  mstep; mstep; mstep
  mstep [O12] with (simp [UInt32.toNat_add]; omega)
  have s194 := SerdeKeyTight.f194_precise (GF := GF) cfg lim (d + 1) types[30]! (by rfl) inst mi n hn (A 754) (A 755) (A 953)
    (hm.funcs 754 (by decide)) (hm.funcs 755 (by decide)) (hm.funcs 953 (by decide)) (by omega) Cg p
    (UInt32.ofNat kb.length) kb (by simp; omega) (by simp; omega)
  rw [hC194] at s194
  ihave #S194 := s194 $$ [F754 F755 F953 Hi]
  · iframe F754 F755 F953 Hi
  clear s194
  mcall S194 using [Hk Hkey]
  · iframe Hk Hkey
  icases HQ with ⟨%hrs, Hk, Hkey⟩
  subst hrs
  mcredits (30 * cfg.regularOpCost + R)
  ihave HQ := Hw $$ Hk
  have hf : (if kb = WNear.BalanceOfArgs.keyBytes then (0 : UInt64) else 256) &&& 1 = 0 := by split <;> decide
  mstep; mstep; mstep
  rw [hf]
  mstep; mstep
  mstep_not_taken with decide
  mstep; mstep; mstep; mstep; mstep; mstep; mstep
  mstep; mstep; mstep; mstep; mstep
  (try simp only [Post.mloop]); (try mctrl_norm); (repeat mpay)
  mstep; mstep; mstep; mstep [Hg]
  rw [show sp - 16 + 16 = sp by simp]
  repeat mstep
  isplitl [Hc]
  · iapply BorrowMut.credits_le
    iframe Hc
    ipureintro; omega
  iframe Hacc Hg Hkey HQ
  isplitr
  · ipureintro
    rw [htype]
    simp only [fieldOf]
    split <;> decide
  isplitl [Hfb]
  · first | iexact Hfb | (iapply store0; iexact Hfb)
  ihave O0 := stk_word $$ O0
  ihave O4 := stk_word $$ O4
  ihave O8 := stk_word $$ O8
  ihave O12 := stk_word $$ O12
  ihave F16 := VecFromElem.stk16_join n (sp - 16).toNat $$ [O0 O4 O8 O12]
  · iframe O0 O4 O8 O12
  ihave F16 := stk_addr (show (sp - 16).toNat = sp.toNat - 176 + 160 by omega) $$ F16
  iapply stk_join n (sp.toNat - 176) 160 16
  iframe H160 F16))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
theorem f193_key_precise_field (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 12 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp acc de ptr : UInt32) (first : Bool) (ob bs kb : List UInt8) (i q : Nat) (x : UInt32)
    (maxP : Nat) (hob : ob.length = 16)
    (hlen : bs.length + 1 < 2 ^ 28) (hptr : ptr.toNat + bs.length < 2 ^ 32) (hde : de.toNat + 24 ≤ 2 ^ 32)
    (hacc : acc.toNat + 8 ≤ 2 ^ 32) (hsp : 176 ≤ sp.toNat) (hi : i ≤ bs.length)
    (hq : keyQ first bs i = some q) (P646 : IProp GF) (K646 : Nat) (Q646 : IProp GF) :
    code193 n maxP inst mi A ∗ Spec646 cfg lim (d + 1) inst mi n g Cg gt sp de ptr ob bs q kb P646 K646 Q646 ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f193 Cg
        (fun args => iprop(⌜args = [.i32 acc]⌝ ∗ n ↦[i32][ acc.toNat ] de ∗
          n ↦[wms][ acc.toNat + 4 ] [if first then 1 else 0] ∗
          g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 176) 160 ∗ n ↦[wms][ (sp - 16).toNat ] ob ∗
          rd n de ptr bs i ∗ n ↦[i32][ (de + 12).toNat + 8 ] x ∗
          n ↦[wms][ 1051092 ] WNear.BalanceOfArgs.keyBytes ∗ P646))
        (fun _ => (572 + 96 * keyWs first bs i + SerdeKeyTight.fieldCost kb) * cfg.regularOpCost + K646)
        (fun _ rs => iprop(⌜rs = [.i64 (fieldOf kb)]⌝ ∗ n ↦[i32][ acc.toNat ] de ∗ n ↦[wms][ acc.toNat + 4 ] [0] ∗
          g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 176) 176 ∗
          n ↦[wms][ 1051092 ] WNear.BalanceOfArgs.keyBytes ∗ Q646)) := by
  iintro ⟨#Hv, #S646⟩
  iunfold Spec646 at S646
  iunfold code193 at Hv
  icases Hv with ⟨#Hv, #F82, #F674, #F646, #F194, #F754, #F755, #F953⟩
  iunfold endCode at Hv
  icases Hv with ⟨#Hcode, -, -, #F332, #F333, #F339⟩
  iunfold errCode at Hcode
  icases Hcode with ⟨#H310c, -, -, -, -, -, -, -, -, -⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold code310 at H310c
    icases H310c with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩
    iexact Hi
  have hn := hm.mem
  have hg := hm.glob
  have ha339 := hm.funcs 339 (by decide)
  have ha333 := hm.funcs 333 (by decide)
  have ha82 := hm.funcs 82 (by decide)
  have ha646 := hm.funcs 646 (by decide)
  have ha194 := hm.funcs 194 (by decide)
  have t11 : types[11]!.params.length = 1 := by rfl
  have t0 : types[0]!.params.length = 1 := by rfl
  have t31 : types[31]!.params.length = 3 := by rfl
  have t30 : types[30]!.params.length = 2 := by rfl
  have s82 := SerdeDeStr.f343_s (GF := GF) cfg lim (d + 1) types[0]! (by rfl) inst mi A n g ta hm (by omega) Cg
    (de + 12) x (by simp [UInt32.toNat_add]; omega)
  rw [← f82_eq] at s82
  ihave #S82 := s82 $$ [F674 Hi]
  · iframe F674 Hi
  clear s82
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hacc, Hfb, Hg, H160, Hob, Hrd, Hsc, Hkey, HP⟩
  subst hargs
  have hlt := sp.toNat_lt
  have h16 : (sp - 16).toNat = sp.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  generalize hC194 : SerdeKeyTight.fieldCost kb * cfg.regularOpCost = C194
  simp only [f193]
  unfold keyQ at hq
  simp only [keyWs]
  have key := SerdeRead.f339_spec (GF := GF) cfg lim (d + 1) types[11]! (by rfl) inst mi n hn (A 332) (A 333)
    (hm.funcs 332 (by decide)) (hm.funcs 333 (by decide)) (by omega) Cg de ptr bs i hi (by omega) (by omega) (by omega)
  generalize hw : wsLen (bs.drop i) = w at hq key ⊢
  generalize hj : i + w = j at hq key
  have hjl : j ≤ bs.length := by have := SerdeRead.wsLen_le (bs.drop i); simp at this; omega
  generalize hW : (100 + 96 * w) * cfg.regularOpCost = W at key
  cases first with
  | true =>
    simp only [if_true] at hq ⊢
    split at hq
    · rename_i hb
      simp only [Option.some.injEq] at hq
      subst hq
      rw [show (572 + 96 * w + SerdeKeyTight.fieldCost kb) * cfg.regularOpCost + K646 + R =
        120 * cfg.regularOpCost + (W + (352 * cfg.regularOpCost + (K646 + (C194 + R)))) by
          rw [← hW, ← hC194]; simp only [Nat.add_mul]; omega]
      mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
      mstep; mstep; mstep; mstep; mstep
      mstep [Hacc]
      mcall key using [Hrd]
      · iframe Hrd
      clear key
      mcredits (260 * cfg.regularOpCost + (K646 + (C194 + R)))
      icases HQ with ⟨%hrs, Hrd⟩
      subst hrs
      rw [hb]
      mstep; mstep; mstep; mstep
      mstep_taken with decide
      mstep; mstep; mstep; mstep; mstep; mstep
      mstep_taken with decide
      mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
      rw [SerdeRead.optByte_byte]
      mstep; mstep; mstep
      mstep_taken with decide
      mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
      mstep_taken with decide
      mstep; mstep [Hfb]; mstep
      mstep_not_taken with decide
      (try simp only [Post.mloop]); (try mctrl_norm); (repeat mpay)
      mstep; mstep; mstep [Hfb]
      mstep
      have hq1 := hb
      generalize hjq : j = jq at hq1 hjl ⊢
      key_tail_tight
    · simp at hq
  | false =>
    simp only [Bool.false_eq_true, if_false] at hq ⊢
    split at hq
    · rename_i hb
      have hjlt := getElem_lt hb
      have key2 := SerdeRead.f339_spec (GF := GF) cfg lim (d + 1) types[11]! (by rfl) inst mi n hn (A 332) (A 333)
        (hm.funcs 332 (by decide)) (hm.funcs 333 (by decide)) (by omega) Cg de ptr bs (j + 1) (by omega) (by omega)
        (by omega) (by omega)
      generalize hw2 : wsLen (bs.drop (j + 1)) = w2 at hq key2 ⊢
      generalize hW2 : (100 + 96 * w2) * cfg.regularOpCost = W2 at key2
      have hj2l : j + 1 + w2 ≤ bs.length := by
        have := SerdeRead.wsLen_le (bs.drop (j + 1)); simp at this; omega
      split at hq
      · rename_i hb2
        simp only [Option.some.injEq] at hq
        subst hq
        rw [show (572 + 96 * (w + w2) + SerdeKeyTight.fieldCost kb) * cfg.regularOpCost + K646 + R =
          120 * cfg.regularOpCost + (W + (82 * cfg.regularOpCost + (W2 + (170 * cfg.regularOpCost +
            (K646 + (C194 + R)))))) by
            rw [← hW, ← hW2, ← hC194]; simp only [Nat.add_mul, Nat.mul_add]; omega]
        mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
        mstep; mstep; mstep; mstep; mstep
        mstep [Hacc]
        mcall key using [Hrd]
        · iframe Hrd
        clear key
        mcredits (180 * cfg.regularOpCost + (W2 + (170 * cfg.regularOpCost + (K646 + (C194 + R)))))
        icases HQ with ⟨%hrs, Hrd⟩
        subst hrs
        rw [hb]
        mstep; mstep; mstep; mstep
        mstep_taken with decide
        mstep; mstep; mstep; mstep; mstep; mstep
        mstep_taken with decide
        mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
        rw [SerdeRead.optByte_byte]
        mstep; mstep; mstep
        mstep_taken with decide
        mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
        mstep_not_taken with decide
        mstep; mstep [Hfb]
        mstep_not_taken with decide
        mstep; mstep [Hacc]
        mcall (SerdeRead.f333_spec cfg lim (d + 1) types[0]! (by rfl) inst mi n hn Cg de ptr bs j hjlt
          (by omega) (by omega)) using [Hrd]
        · iframe Hrd
        icases HQ with ⟨%hrs, Hrd⟩
        subst hrs
        mcredits (100 * cfg.regularOpCost + (W2 + (170 * cfg.regularOpCost + (K646 + (C194 + R)))))
        mstep; mstep [Hacc]
        mcall key2 using [Hrd]
        · iframe Hrd
        clear key2
        mcredits (250 * cfg.regularOpCost + (K646 + (C194 + R)))
        icases HQ with ⟨%hrs, Hrd⟩
        subst hrs
        rw [hb2]
        mstep; mstep; mstep; mstep
        mstep_taken with decide
        mstep; mstep; mstep; mstep; mstep
        mstep_not_taken with decide
        mstep; mstep; mstep; mstep; mstep; mstep
        (try simp only [Post.mloop]); (try mctrl_norm); (repeat mpay)
        have hq1 := hb2
        have hjl' := hj2l
        generalize hjq : j + 1 + w2 = jq at hq1 hjl' ⊢
        key_tail_tight
      · simp at hq
    · simp at hq


end Proof
end WNear.Binary.SerdeNextKeyTight
namespace WNear.Binary.SerdeKeyReuse
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.VecFromElem (stk stk_split stk_join)
open WNear.Binary.SerdeRead (rd)
open WNear.Binary.ParseStr (strRun borrowed plain roomRun code646)
open WNear.Binary.ParseStrSuccess (appendChunks)
open WNear.Binary.ScratchGrow (sbuf)
open WNear.Binary.SerdeValueState (scratchPre)
open WNear.Binary.SerdeKeyEsc (keyState)

section Resource
variable {GF : BundledGFunctors} [WasmGS NearState GF]

theorem f193_key_model_precise_field (cfg : WasmConfig) (lim : ExecLimits) (d inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 31 < lim.maxCallDepth)
    (Cg : Nat) (gt : GlobalType) (sp acc de ptr idx ptrS capS sl : UInt32)
    (bs : List UInt8) (first : Bool) (i q maxP hl F : Nat) (live : List (Nat × Nat))
    (key : String) (rest : List UInt8)
    (hlen : bs.length < 2 ^ 24) (hptr : ptr.toNat + bs.length < 2 ^ 32)
    (hde : de.toNat + 24 ≤ 2 ^ 32) (hacc : acc.toNat + 8 ≤ 2 ^ 32) (hsp : 208 ≤ sp.toNat)
    (hi : i ≤ bs.length) (hq : q ≤ bs.length) (hkey : SerdeNextKey.keyQ first bs i = some q)
    (hcap : capS.toNat < 2 ^ 25) (hroom : keyRoom maxP hl capS (bs.drop q))
    (hmodel : NearInterface.Json.stringBody (bs.drop q) [] = some (some key, rest)) :
    SerdeNextKey.code193 n maxP inst mi A ∗ code646 n maxP inst mi A ⊢
      MFunSpec (GF := GF) cfg lim d types[11]! inst mi f193 Cg
        (fun args => iprop(⌜args = [.i32 acc]⌝ ∗ n ↦[i32][ acc.toNat ] de ∗
          n ↦[wms][ acc.toNat + 4 ] [if first then 1 else 0] ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          stk n (sp.toNat - 208) 208 ∗ vt n 1057464 idx ta (A 578) ∗ SerdeValueState.tables n ∗
          rd n de ptr bs i ∗ scratchPre n maxP hl live F de ptrS capS sl ∗
          n ↦[wms][ 1051092 ] WNear.BalanceOfArgs.keyBytes))
        (fun _ => (572 + 96 * SerdeNextKey.keyWs first bs i + SerdeKeyTight.fieldCost key.toUTF8.toList) * cfg.regularOpCost +
          preciseCost cfg F capS bs key.toUTF8.toList rest q)
        (fun _ rs => iprop(⌜rs = [.i64 (SerdeNextKey.fieldOf key.toUTF8.toList)]⌝ ∗
          n ↦[i32][ acc.toNat ] de ∗ n ↦[wms][ acc.toNat + 4 ] [0] ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          stk n (sp.toNat - 208) 208 ∗ vt n 1057464 idx ta (A 578) ∗ SerdeValueState.tables n ∗
          n ↦[wms][ 1051092 ] WNear.BalanceOfArgs.keyBytes ∗
          keyState n maxP hl live F de ptr ptrS capS bs key.toUTF8.toList rest q)) := by
  have hlt := sp.toNat_lt
  have h16 : (sp - 16).toNat = sp.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have hsc : (de + 12).toNat = de.toNat + 12 := by simp [UInt32.toNat_add]; omega
  let P : IProp GF := iprop(stk n (sp.toNat - 208) 32 ∗ vt n 1057464 idx ta (A 578) ∗
    SerdeValueState.tables n ∗ n ↦[i32][ de.toNat + 12 ] ptrS ∗ n ↦[i32][ de.toNat + 16 ] capS ∗
    sbuf n maxP hl live F ptrS capS [])
  let Q : IProp GF := iprop(stk n (sp.toNat - 208) 32 ∗ vt n 1057464 idx ta (A 578) ∗
    SerdeValueState.tables n ∗ keyState n maxP hl live F de ptr ptrS capS bs key.toUTF8.toList rest q)
  iintro ⟨#C193, #C646⟩
  have keySpec (ob : List UInt8) (hob : ob.length = 16) :=
    f646_key_precise (GF := GF) cfg lim (d + 1) inst mi A n g ta hm (by omega) Cg gt sp de ptr idx ptrS capS
      ob bs q maxP hl F live key rest hob hlen hptr hde hsp hq hcap hroom hmodel
  iunfold MFunSpec
  imodintro
  iintro %args %R Hpre Hc
  icases Hpre with ⟨%ha, Hacc, Hfirst, Hg, H208, Hvt, Htables, Hrd, Hscratch, Hkey⟩
  iunfold scratchPre at Hscratch
  icases Hscratch with ⟨S8, S0, S4, Hsb⟩
  icases stk_split n (sp.toNat - 208) 32 176 $$ H208 with ⟨H32, H176⟩
  rw [show sp.toNat - 208 + 32 = sp.toNat - 176 by omega]
  icases stk_split n (sp.toNat - 176) 160 16 $$ H176 with ⟨H160, Hob⟩
  rw [show sp.toNat - 176 + 160 = (sp - 16).toNat by omega]
  iunfold stk at Hob
  icases Hob with ⟨%ob, %hob, Hob⟩
  ihave #S646 := keySpec ob hob $$ C646
  have s := SerdeNextKeyTight.f193_key_precise_field (GF := GF) cfg lim d types[11]! rfl inst mi A n g ta hm (by omega)
    Cg gt sp acc de ptr first ob bs key.toUTF8.toList i q sl maxP hob (by omega) hptr hde hacc
    (by omega) hi hkey P (preciseCost cfg F capS bs key.toUTF8.toList rest q) Q
  ihave #S := s $$ [C193 S646]
  · iframe C193 S646
  iunfold MFunSpec at S
  ihave Hrun := S $$ %args %R [Hacc Hfirst Hg H160 Hob Hrd S8 H32 Hvt Htables S0 S4 Hsb Hkey] Hc
  · simp only [hsc, Nat.add_assoc, show 12 + 8 = 20 from rfl]
    iframe Hacc Hfirst Hg H160 Hob Hrd S8 Hkey
    isplitr
    · ipureintro; exact ha
    dsimp only [P]
    iframe H32 Hvt Htables S0 S4 Hsb
  iapply mwpInvoke_wand
  isplitl [Hrun]
  · iexact Hrun
  isplit
  · iintro %rs ⟨Hc, %hrs, Hacc, Hfirst, Hg, H176, Hkey, HQ⟩
    iunfold Q at HQ
    icases HQ with ⟨H32, Hvt, Htables, Hstate⟩
    ihave H208 := stk_join n (sp.toNat - 208) 32 176 $$ [H32 H176]
    · rw [show sp.toNat - 208 + 32 = sp.toNat - 176 by omega]
      iframe H32 H176
    dsimp only
    iframe Hc Hacc Hfirst Hg H208 Hvt Htables Hkey Hstate
    ipureintro; exact hrs
  · iintro Htrap; iexact Htrap

end Resource
end WNear.Binary.SerdeKeyReuse
namespace WNear.Binary.SerdeKeyReuse
open Wasm Wasm.Near

def bundledCost (cfg : WasmConfig) (F : Nat) (cap : UInt32) (bs bytes rest : List UInt8) (q : Nat) : Nat :=
  preciseCost cfg F cap bs bytes rest q + SerdeKeyTight.fieldCost bytes * cfg.regularOpCost -
    SerdeKey.cost194 * cfg.regularOpCost

theorem bundledCost_funds_reader_and_field (cfg : WasmConfig) (F : Nat) (cap : UInt32)
    (bs bytes rest : List UInt8) (q : Nat) :
    preciseCost cfg F cap bs bytes rest q + SerdeKeyTight.fieldCost bytes * cfg.regularOpCost ≤
      SerdeKey.cost194 * cfg.regularOpCost + bundledCost cfg F cap bs bytes rest q := by
  unfold bundledCost
  omega

theorem bundledCost_le_preciseCost (cfg : WasmConfig) (F : Nat) (cap : UInt32)
    (bs bytes rest : List UInt8) (q : Nat) :
    bundledCost cfg F cap bs bytes rest q ≤ preciseCost cfg F cap bs bytes rest q := by
  have hf := Nat.mul_le_mul_right cfg.regularOpCost (SerdeKeyTight.fieldCost_le_legacy bytes)
  unfold bundledCost
  omega

end WNear.Binary.SerdeKeyReuse
