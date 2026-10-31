import Mathlib.Tactic.IntervalCases
import Bridge.Functions.ParseStrEsc
import Bridge.Functions.SerdeDebugBody
namespace WNear.Binary.SerdeErrorWriters
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.Interface
variable {GF : BundledGFunctors} [WasmGS NearState GF]
set_option maxRecDepth 100000

theorem error_code_debug_table : wTable.elems[126]? = some (Ref.func 591) := rfl

theorem string_debug_table : wTable.elems[127]? = some (Ref.func 619) := rfl

theorem u32_display_table : wTable.elems[3]? = some (Ref.func 870) := rfl

set_option maxHeartbeats 16000000 in
/-- Actual ErrorCode Debug dereference calls the selected enum formatter, preserving the owned descriptor. -/
theorem f591_delegate (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 1 < lim.maxCallDepth) (Cg : Nat)
    (desc e fmt : UInt32) (Kw : Nat) (P Q : IProp GF) (hdesc : desc.toNat + 4 ≤ 2 ^ 32) :
    inst ↪[inst] mi ∗ A 592 ↪[wf] FuncInst.wasm types[13]! inst f592 ∗
      PanicDebug.DebugCalleeSpec cfg lim (d + 1) inst mi f592 e fmt Kw Cg P Q ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f591 Cg
        (fun args => iprop(⌜args = [.i32 desc, .i32 fmt]⌝ ∗ n ↦[i32][ desc.toNat ] e ∗ P))
        (fun _ => 4 * cfg.regularOpCost + activationGas cfg.regularOpCost (entryLocals f592 [.i32 e, .i32 fmt]) + Kw)
        (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ n ↦[i32][ desc.toNat ] e ∗ Q)) := by
  unfold PanicDebug.DebugCalleeSpec
  iintro ⟨#Hi, #F592, #HS⟩
  have hn := hm.mem
  have ha592 := hm.funcs 592 (by decide)
  have t13 : types[13]!.params.length = 2 := rfl
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Desc, HP⟩
  subst hargs
  simp only [f591]
  mstep; mstep [Desc]; mstep
  mcall HS using [HP] with (mstep_norm_full; omega)
  · iframe HP
  icases HQ with ⟨%hrs, HQ⟩
  subst hrs
  mcredits R
  simp [Post.mfunc, htype]
  iframe Hc Desc HQ
  iintro Hret
  iexact Hret

/-- The actual string-slice Debug formatter, including its quoted/escaped output and selected sink. -/
def StringDebugSliceSpec (cfg : WasmConfig) (lim : ExecLimits) (d inst : Nat) (mi : ModuleInst)
    (g : Nat) (gt : GlobalType) (sp p len fmt : UInt32) (K Cg : Nat) (P Q : IProp GF) : IProp GF :=
  MFunSpec cfg lim d types[15]! inst mi f920 Cg
    (fun args => iprop(⌜args = [.i32 p, .i32 len, .i32 fmt]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ P)) (fun _ => K)
    (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ Q))

set_option maxHeartbeats 16000000 in
/-- Actual String Debug wrapper constructs its borrowed slice, calls the real quoted/escaped writer and restores its frame. -/
theorem f619_delegate (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 1 < lim.maxCallDepth) (Cg : Nat) (gt : GlobalType)
    (sp vec p len fmt : UInt32) (Kw : Nat) (P Q : IProp GF)
    (hsp : 16 ≤ sp.toNat) (hv : vec.toNat + 12 ≤ 2 ^ 32) :
    inst ↪[inst] mi ∗ A 728 ↪[wf] FuncInst.wasm types[14]! inst f728 ∗
      A 920 ↪[wf] FuncInst.wasm types[15]! inst f920 ∗
      StringDebugSliceSpec cfg lim (d + 1) inst mi g gt (sp - 16) p len fmt Kw Cg P Q ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f619 Cg
        (fun args => iprop(⌜args = [.i32 vec, .i32 fmt]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          VecFromElem.stk n (sp.toNat - 16) 16 ∗ n ↦[i32][ vec.toNat ] p ∗ n ↦[i32][ vec.toNat + 8 ] len ∗ P))
        (fun _ => 50 * cfg.regularOpCost +
          activationGas cfg.regularOpCost (entryLocals f920 [.i32 p, .i32 len, .i32 fmt]) + Kw)
        (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          VecFromElem.stk n (sp.toNat - 16) 16 ∗ n ↦[i32][ vec.toNat ] p ∗ n ↦[i32][ vec.toNat + 8 ] len ∗ Q)) := by
  unfold StringDebugSliceSpec
  iintro ⟨#Hi, #F728, #F920, #HS⟩
  have hn := hm.mem
  have hg := hm.glob
  have ha728 := hm.funcs 728 (by decide)
  have ha920 := hm.funcs 920 (by decide)
  have t14 : types[14]!.params.length = 2 := rfl
  have t15 : types[15]!.params.length = 3 := rfl
  have hlt := sp.toNat_lt
  have h16 : (sp - 16).toNat = sp.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have h8 : (sp - 16 + 8).toNat = (sp - 16).toNat + 8 := by simp [UInt32.toNat_add]; omega
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, V0, V8, HP⟩
  subst hargs
  ihave Hs := VecFromElem.stk_addr h16.symm $$ Hs
  icases VecFromElem.stk_split n _ 8 8 $$ Hs with ⟨Pad, Out⟩
  iunfold VecFromElem.stk at Out
  icases Out with ⟨%ob, %hob, Out⟩
  simp only [f619]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep; mstep; mstep
  mcall (ParseStr.f728_spec cfg lim (d + 1) types[14]! rfl inst mi n hn Cg
    (sp - 16 + 8) vec p len ob hob) using [Out V0 V8] with (mstep_norm_full; omega)
  · simp only [h8]
    iframe Out V0 V8
  icases HQ with ⟨%hrs, O0, O4, V0, V8⟩
  subst hrs
  mstep; mstep [O0]; mstep; mstep [O4]; mstep
  mcall HS using [Hg HP] with (mstep_norm_full; omega)
  · iframe Hg HP
  icases HQ with ⟨%hrs, Hg, HQ⟩
  subst hrs
  mstep; mstep; mstep; mstep; mstep [Hg]; mstep
  simp only [UInt32.sub_add_cancel]
  ihave O0 := VecFromElem.stk_word n (sp - 16 + 8).toNat p $$ O0
  ihave O4 := VecFromElem.stk_word n ((sp - 16 + 8).toNat + 4) len $$ O4
  ihave Out := VecFromElem.stk_join n (sp - 16 + 8).toNat 4 4 $$ [O0 O4]
  · iframe O0 O4
  simp only [h8]
  ihave Hs := VecFromElem.stk_join n (sp - 16).toNat 8 8 $$ [Pad Out]
  · iframe Pad Out
  ihave Hs := VecFromElem.stk_addr h16 $$ Hs
  mcredits R
  simp [Post.mfunc, htype]
  iframe Hc Hg Hs V0 V8 HQ

/-- Exact static payload selected by the deployed ErrorCode discriminant. -/
def syntaxSlice (tag : UInt32) : UInt32 × UInt32 :=
  match tag.toNat with
  | 2 => (1061464, 24) | 3 => (1061437, 27) | 4 => (1061411, 26) | 5 => (1061386, 25)
  | 6 => (1061374, 12) | 7 => (1061355, 19) | 8 => (1061336, 19) | 9 => (1061322, 14)
  | 10 => (1061308, 14) | 11 => (1061294, 14) | 12 => (1061280, 14) | 13 => (1061261, 19)
  | 14 => (1061235, 26) | 15 => (1061173, 62) | 16 => (1061153, 20) | 17 => (1061117, 36)
  | 18 => (1061103, 14) | 19 => (1061084, 19) | 20 => (1061056, 28) | 21 => (1061032, 24)
  | _ => (0, 0)

/-- Exact selected borrowed-slice write, with its actual Formatter and owned sink/payload state. -/
def StaticWriteSpec (cfg : WasmConfig) (lim : ExecLimits) (d inst : Nat) (mi : ModuleInst)
    (fmt ptr len : UInt32) (K Cg : Nat) (P Q : IProp GF) : IProp GF :=
  MFunSpec cfg lim d types[15]! inst mi f912 Cg
    (fun args => iprop(⌜args = [.i32 fmt, .i32 ptr, .i32 len]⌝ ∗ P)) (fun _ => K)
    (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ Q))

set_option maxHeartbeats 32000000 in
/-- All actual static syntax-error branches. Dynamic message and I/O payload variants are excluded explicitly. -/
theorem f592_syntax (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 1 < lim.maxCallDepth) (Cg : Nat)
    (e fmt tag : UInt32) (Kw : Nat) (P Q : IProp GF) (he : e.toNat + 4 ≤ 2 ^ 32)
    (hlow : 2 ≤ tag.toNat) (hhigh : tag.toNat ≤ 21) :
    inst ↪[inst] mi ∗ A 912 ↪[wf] FuncInst.wasm types[15]! inst f912 ∗
      StaticWriteSpec cfg lim (d + 1) inst mi fmt (syntaxSlice tag).1 (syntaxSlice tag).2 Kw Cg P Q ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f592 Cg
        (fun args => iprop(⌜args = [.i32 e, .i32 fmt]⌝ ∗ n ↦[i32][ e.toNat ] tag ∗ P))
        (fun _ => 100 * cfg.regularOpCost +
          activationGas cfg.regularOpCost (entryLocals f912 [.i32 fmt, .i32 (syntaxSlice tag).1, .i32 (syntaxSlice tag).2]) + Kw)
        (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ n ↦[i32][ e.toNat ] tag ∗ Q)) := by
  unfold StaticWriteSpec
  generalize htag : tag.toNat = k at *
  have heq : tag = UInt32.ofNat k := by rw [← htag]; simp
  subst tag
  interval_cases k
  all_goals
    simp only [syntaxSlice, UInt32.toNat_ofNat', Nat.reduceMod]
    iintro ⟨#Hi, #F912, #HS⟩
    have hn := hm.mem
    have ha912 := hm.funcs 912 (by decide)
    have t15 : types[15]!.params.length = 3 := rfl
    iapply MFunSpec_intro
    imodintro
    iintro %args %R HP Hc
    icases HP with ⟨%hargs, Tag, HP⟩
    subst hargs
    simp only [f592]
    repeat mstep
    mstep [Tag]
    repeat mstep
    simp only [UInt32.toNat_ofNat', Nat.reduceMod]
    mstep_post
    repeat mstep
    mcall HS using [HP] with (mstep_norm_full; omega)
    · iframe HP
    icases HQ with ⟨%hrs, HQ⟩
    subst hrs
    repeat mstep
    mstep_post
    mcredits R
    try simp [Post.mfunc, htype]
    iframe Hc Tag HQ
    try (iintro Hret; iexact Hret)

set_option maxHeartbeats 32000000 in
/-- Actual ErrorCode descriptor wrapper instantiates every static syntax variant from the checked branch table. -/
theorem f591_syntax (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 2 < lim.maxCallDepth) (Cg : Nat)
    (desc e fmt tag : UInt32) (Kw : Nat) (P Q : IProp GF)
    (hdesc : desc.toNat + 4 ≤ 2 ^ 32) (he : e.toNat + 4 ≤ 2 ^ 32)
    (hlow : 2 ≤ tag.toNat) (hhigh : tag.toNat ≤ 21) :
    inst ↪[inst] mi ∗ A 592 ↪[wf] FuncInst.wasm types[13]! inst f592 ∗
      A 912 ↪[wf] FuncInst.wasm types[15]! inst f912 ∗
      StaticWriteSpec cfg lim (d + 2) inst mi fmt (syntaxSlice tag).1 (syntaxSlice tag).2 Kw Cg P Q ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f591 Cg
        (fun args => iprop(⌜args = [.i32 desc, .i32 fmt]⌝ ∗
          n ↦[i32][ desc.toNat ] e ∗ n ↦[i32][ e.toNat ] tag ∗ P))
        (fun _ => 123 * cfg.regularOpCost + Kw)
        (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ n ↦[i32][ desc.toNat ] e ∗ n ↦[i32][ e.toNat ] tag ∗ Q)) := by
  iintro ⟨#Hi, #F592, #F912, HS⟩
  ihave S592 : PanicDebug.DebugCalleeSpec cfg lim (d + 1) inst mi f592 e fmt
      (100 * cfg.regularOpCost + activationGas cfg.regularOpCost
        (entryLocals f912 [.i32 fmt, .i32 (syntaxSlice tag).1, .i32 (syntaxSlice tag).2]) + Kw) Cg
      iprop(n ↦[i32][ e.toNat ] tag ∗ P) iprop(n ↦[i32][ e.toNat ] tag ∗ Q) $$ [Hi F912 HS]
  · unfold PanicDebug.DebugCalleeSpec
    iapply (f592_syntax cfg lim (d + 1) types[13]! rfl inst mi A n g ta hm (by omega) Cg
      e fmt tag Kw P Q he hlow hhigh)
    iframe Hi F912 HS
  have H := f591_delegate (GF := GF) cfg lim d type htype inst mi A n g ta hm (by omega) Cg desc e fmt
    (100 * cfg.regularOpCost + activationGas cfg.regularOpCost
      (entryLocals f912 [.i32 fmt, .i32 (syntaxSlice tag).1, .i32 (syntaxSlice tag).2]) + Kw)
    iprop(n ↦[i32][ e.toNat ] tag ∗ P) iprop(n ↦[i32][ e.toNat ] tag ∗ Q) hdesc
  have a592 : activationGas cfg.regularOpCost (entryLocals f592 [.i32 e, .i32 fmt]) = 9 * cfg.regularOpCost := by
    simp [activationGas, entryLocals, f592, ValType.default]
  have a912 : activationGas cfg.regularOpCost
      (entryLocals f912 [.i32 fmt, .i32 (syntaxSlice tag).1, .i32 (syntaxSlice tag).2]) = 10 * cfg.regularOpCost := by
    simp [activationGas, entryLocals, f912, ValType.default]
  rw [a592, a912] at H
  have hcost : 4 * cfg.regularOpCost + 9 * cfg.regularOpCost +
      (100 * cfg.regularOpCost + 10 * cfg.regularOpCost + Kw) = 123 * cfg.regularOpCost + Kw := by omega
  rw [hcost] at H
  simp only [a912]
  iapply H
  iframe Hi F592 S592

/-- Exact selected write_str method; descriptor dispatch alone does not establish sink behavior. -/
def WriteSliceCalleeSpec (cfg : WasmConfig) (lim : ExecLimits) (d inst : Nat) (mi : ModuleInst)
    (code : Func) (data ptr len : UInt32) (K Cg : Nat) (P Q : IProp GF) : IProp GF :=
  MFunSpec cfg lim d types[15]! inst mi code Cg
    (fun args => iprop(⌜args = [.i32 data, .i32 ptr, .i32 len]⌝ ∗ P)) (fun _ => K)
    (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ Q))

set_option maxHeartbeats 16000000 in
/-- Actual borrowed-slice Formatter wrapper preserves its descriptors and invokes the selected write_str method. -/
theorem f912_delegate (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 1 < lim.maxCallDepth) (Cg : Nat)
    (fmt data vt idx ptr len : UInt32) (af : Nat) (code : Func) (Kw : Nat) (P Q : IProp GF)
    (hf : fmt.toNat + 32 ≤ 2 ^ 32) (hvt : vt.toNat + 16 ≤ 2 ^ 32) :
    inst ↪[inst] mi ∗ af ↪[wf] FuncInst.wasm types[15]! inst code ∗
      WriteSliceCalleeSpec cfg lim (d + 1) inst mi code data ptr len Kw Cg P Q ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f912 Cg
        (fun args => iprop(⌜args = [.i32 fmt, .i32 ptr, .i32 len]⌝ ∗
          n ↦[i32][ fmt.toNat + 24 ] data ∗ n ↦[i32][ fmt.toNat + 28 ] vt ∗
          n ↦[i32][ vt.toNat + 12 ] idx ∗ ta ↦[wt][ idx.toNat ] Ref.func af ∗ P))
        (fun _ => 10 * cfg.regularOpCost +
          activationGas cfg.regularOpCost (entryLocals code [.i32 data, .i32 ptr, .i32 len]) + Kw)
        (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗
          n ↦[i32][ fmt.toNat + 24 ] data ∗ n ↦[i32][ fmt.toNat + 28 ] vt ∗
          n ↦[i32][ vt.toNat + 12 ] idx ∗ ta ↦[wt][ idx.toNat ] Ref.func af ∗ Q)) := by
  unfold WriteSliceCalleeSpec
  iintro ⟨#Hi, #HF, #HS⟩
  have hn := hm.mem
  have hta := hm.table
  have hty : types[15]! = mi.types[15]! := by rw [hm.types]
  have t15 : types[15]!.params.length = 3 := rfl
  generalize hact : activationGas cfg.regularOpCost (entryLocals code [.i32 data, .i32 ptr, .i32 len]) = ACT
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Data, Vtab, Slot, HT, HP⟩
  subst hargs
  simp only [f912]
  mstep; mstep [Data]; mstep; mstep; mstep; mstep; mstep; mstep [Vtab]; mstep [Slot]
  iapply mwpi_cons
  iapply (Borrow.mwpi_call_indirect' (ty := 15) (t := 0) (ta := ta) (idx := idx) (a := af)
    (type := types[15]!) (inst := inst) (mi := mi) (code := code) [.i32 data, .i32 ptr, .i32 len])
  iframe HS HF Hi HT
  isplitr
  · ipureintro; exact ⟨rfl, hta, hty, rfl, hd⟩
  isplitl [Hc]
  · iexact Hc
  isplitr
  · ipureintro; rw [hact]; omega
  isplitl [HP]
  · iframe HP
    ipureintro; rfl
  inext
  iintro %rs HT Hc HQ
  icases HQ with ⟨%hrs, HQ⟩
  subst hrs
  ihave HR : credits Cg R $$ [Hc]
  · iapply BorrowMut.credits_le
    iframe Hc
    ipureintro; rw [hact]; omega
  mstep_post
  mstep
  simp [Post.mfunc, htype]
  iframe HR Data Vtab Slot HT HQ
  iintro Hret
  iexact Hret

set_option maxHeartbeats 16000000 in
/-- Every static syntax variant follows the deployed ErrorCode wrapper and selected Formatter write_str dispatch. -/
theorem f591_syntax_sink (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 3 < lim.maxCallDepth) (Cg : Nat)
    (desc e fmt tag data vt idx : UInt32) (af : Nat) (code : Func) (Kw : Nat) (P Q : IProp GF)
    (hdesc : desc.toNat + 4 ≤ 2 ^ 32) (he : e.toNat + 4 ≤ 2 ^ 32)
    (hlow : 2 ≤ tag.toNat) (hhigh : tag.toNat ≤ 21)
    (hf : fmt.toNat + 32 ≤ 2 ^ 32) (hvt : vt.toNat + 16 ≤ 2 ^ 32) :
    inst ↪[inst] mi ∗ A 592 ↪[wf] FuncInst.wasm types[13]! inst f592 ∗
      A 912 ↪[wf] FuncInst.wasm types[15]! inst f912 ∗
      af ↪[wf] FuncInst.wasm types[15]! inst code ∗
      WriteSliceCalleeSpec cfg lim (d + 3) inst mi code data
        (syntaxSlice tag).1 (syntaxSlice tag).2 Kw Cg P Q ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f591 Cg
        (fun args => iprop(⌜args = [.i32 desc, .i32 fmt]⌝ ∗
          n ↦[i32][ desc.toNat ] e ∗ n ↦[i32][ e.toNat ] tag ∗
          n ↦[i32][ fmt.toNat + 24 ] data ∗ n ↦[i32][ fmt.toNat + 28 ] vt ∗
          n ↦[i32][ vt.toNat + 12 ] idx ∗ ta ↦[wt][ idx.toNat ] Ref.func af ∗ P))
        (fun _ => 133 * cfg.regularOpCost +
          activationGas cfg.regularOpCost
            (entryLocals code [.i32 data, .i32 (syntaxSlice tag).1, .i32 (syntaxSlice tag).2]) + Kw)
        (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗
          n ↦[i32][ desc.toNat ] e ∗ n ↦[i32][ e.toNat ] tag ∗
          n ↦[i32][ fmt.toNat + 24 ] data ∗ n ↦[i32][ fmt.toNat + 28 ] vt ∗
          n ↦[i32][ vt.toNat + 12 ] idx ∗ ta ↦[wt][ idx.toNat ] Ref.func af ∗ Q)) := by
  iintro ⟨#Hi, #F592, #F912, #HF, HS⟩
  ihave S912 : StaticWriteSpec cfg lim (d + 2) inst mi fmt
      (syntaxSlice tag).1 (syntaxSlice tag).2
      (10 * cfg.regularOpCost + activationGas cfg.regularOpCost
        (entryLocals code [.i32 data, .i32 (syntaxSlice tag).1, .i32 (syntaxSlice tag).2]) + Kw) Cg
      iprop(n ↦[i32][ fmt.toNat + 24 ] data ∗ n ↦[i32][ fmt.toNat + 28 ] vt ∗
        n ↦[i32][ vt.toNat + 12 ] idx ∗ ta ↦[wt][ idx.toNat ] Ref.func af ∗ P)
      iprop(n ↦[i32][ fmt.toNat + 24 ] data ∗ n ↦[i32][ fmt.toNat + 28 ] vt ∗
        n ↦[i32][ vt.toNat + 12 ] idx ∗ ta ↦[wt][ idx.toNat ] Ref.func af ∗ Q) $$ [Hi HF HS]
  · unfold StaticWriteSpec
    iapply (f912_delegate cfg lim (d + 2) types[15]! rfl inst mi A n g ta hm (by omega) Cg
      fmt data vt idx (syntaxSlice tag).1 (syntaxSlice tag).2 af code Kw P Q hf hvt)
    iframe Hi HF HS
  have H := f591_syntax (GF := GF) cfg lim d type htype inst mi A n g ta hm (by omega) Cg
    desc e fmt tag
    (10 * cfg.regularOpCost + activationGas cfg.regularOpCost
      (entryLocals code [.i32 data, .i32 (syntaxSlice tag).1, .i32 (syntaxSlice tag).2]) + Kw)
    iprop(n ↦[i32][ fmt.toNat + 24 ] data ∗ n ↦[i32][ fmt.toNat + 28 ] vt ∗
      n ↦[i32][ vt.toNat + 12 ] idx ∗ ta ↦[wt][ idx.toNat ] Ref.func af ∗ P)
    iprop(n ↦[i32][ fmt.toNat + 24 ] data ∗ n ↦[i32][ fmt.toNat + 28 ] vt ∗
      n ↦[i32][ vt.toNat + 12 ] idx ∗ ta ↦[wt][ idx.toNat ] Ref.func af ∗ Q)
    hdesc he hlow hhigh
  have hc : 123 * cfg.regularOpCost + (10 * cfg.regularOpCost +
      activationGas cfg.regularOpCost
        (entryLocals code [.i32 data, .i32 (syntaxSlice tag).1, .i32 (syntaxSlice tag).2]) + Kw) =
      133 * cfg.regularOpCost + activationGas cfg.regularOpCost
        (entryLocals code [.i32 data, .i32 (syntaxSlice tag).1, .i32 (syntaxSlice tag).2]) + Kw := by omega
  rw [hc] at H
  iapply H
  iframe Hi F592 F912 S912
end WNear.Binary.SerdeErrorWriters
