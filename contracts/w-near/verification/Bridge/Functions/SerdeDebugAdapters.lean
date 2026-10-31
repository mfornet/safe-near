import Bridge.Functions.SerdeDebugResources

namespace WNear.Binary.SerdeDebug
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_addr stk_intro stk_word)
open WNear.Binary.PanicHook (stk4_word)
variable {GF : BundledGFunctors} [WasmGS NearState GF]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- Actual String::write_fmt adapter retains original Arguments and lends a stack copy to the real writer. -/
theorem f598_delegate (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 1 < lim.maxCallDepth) (Cg : Nat) (gt : GlobalType)
    (sp self ar : UInt32) (a0 a8 a16 : UInt64) (ret : UInt32) (Kw : Nat) (P Q : IProp GF)
    (hsp : 32 ≤ sp.toNat) (har : ar.toNat + 24 ≤ 2 ^ 32) :
    inst ↪[inst] mi ∗ A 872 ↪[wf] FuncInst.wasm types[15]! inst f872 ∗
      StringFmtEngineSpec cfg lim (d + 1) inst mi n g gt sp self a0 a8 a16 ret Kw Cg P Q
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f598 Cg
        (fun args => iprop(⌜args = [.i32 self, .i32 ar]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          stk n (sp.toNat - 32) 32 ∗ args24 n ar a0 a8 a16 ∗ P))
        (fun _ => 60 * cfg.regularOpCost +
          activationGas cfg.regularOpCost (entryLocals f872 [.i32 0, .i32 0, .i32 0]) + Kw)
        (fun _ rs => iprop(⌜rs = [.i32 ret]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          stk n (sp.toNat - 32) 32 ∗ args24 n ar a0 a8 a16 ∗ Q)) := by
  unfold StringFmtEngineSpec
  iintro ⟨#Hi, #F872, #HS⟩
  have hn := hm.mem
  have hg := hm.glob
  have ha872 := hm.funcs 872 (by decide)
  have t15 : types[15]!.params.length = 3 := rfl
  have hlt := sp.toNat_lt
  have h32 : (sp - 32).toNat = sp.toNat - 32 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have h8 : (sp - 32 + 8).toNat = (sp - 32).toNat + 8 := by simp [UInt32.toNat_add]; omega
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, HA, HP⟩
  subst hargs
  iunfold args24 at HA
  icases HA with ⟨A0, A8, A16⟩
  ihave Hs := stk_addr h32.symm $$ Hs
  icases stk_split n _ 4 28 $$ Hs with ⟨Pad, Hs⟩
  icases stk_split n _ 4 24 $$ Hs with ⟨Ptr, Hs⟩
  icases stk_split n _ 8 16 $$ Hs with ⟨W0, Hs⟩
  icases stk_split n _ 8 8 $$ Hs with ⟨W8, W16⟩
  icases stk4_word n _ $$ Ptr with ⟨%oldPtr, Ptr⟩
  iunfold stk at W0 W8 W16
  icases W0 with ⟨%b0, %hb0, W0⟩
  icases W8 with ⟨%b8, %hb8, W8⟩
  icases W16 with ⟨%b16, %hb16, W16⟩
  simp only [f598]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep; mstep [Ptr]
  mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep [A16]; mstep [W16]
  mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep [A8]; mstep [W8]
  mstep; mstep; mstep [A0]; mstep [W0]
  mstep; mstep; mstep; mstep; mstep; mstep; mstep
  simp only [U128From.decodeLE_storeBytes_i64, UInt64.ofNat_toNat]
  mcall HS using [Hg Ptr W0 W8 W16 HP] with (mstep_norm_full; omega)
  · iframe Hg Ptr HP
    iunfold args24
    have e0 : (sp - 32).toNat + 4 + 4 = (sp - 32 + 8).toNat := by omega
    have e8 : (sp - 32).toNat + 4 + 4 + 8 = (sp - 32 + 8).toNat + 8 := by omega
    have e16 : (sp - 32).toNat + 4 + 4 + 8 + 8 = (sp - 32 + 8).toNat + 16 := by omega
    simp only [e0, e8, e16]
    iframe W0 W8 W16
  icases HQ with ⟨%hrs, Hg, Ptr, HA, HQ⟩
  subst hrs
  iunfold args24 at HA
  icases HA with ⟨W0, W8, W16⟩
  mstep; mstep; mstep; mstep; mstep [Hg]; mstep
  simp only [UInt32.sub_add_cancel]
  mcredits R
  simp only [Post.mfunc, htype, Nat.sub_self, List.drop_zero]
  ihave Ptr := stk_word n ((sp - 32).toNat + 4) self $$ Ptr
  ihave W0 := stk_intro n ((sp - 32 + 8).toNat) (storeBytes (.i64 a0) 8) $$ W0
  ihave W8 := stk_intro n ((sp - 32 + 8).toNat + 8) (storeBytes (.i64 a8) 8) $$ W8
  ihave W16 := stk_intro n ((sp - 32 + 8).toNat + 16) (storeBytes (.i64 a16) 8) $$ W16
  have hb (v : UInt64) : (storeBytes (.i64 v) 8).length = 8 := by simp [storeBytes, storeRaw]
  simp only [h8, hb, Nat.add_assoc, Nat.reduceAdd]
  ihave Hs := stk_join n (sp - 32).toNat 4 4 $$ [Pad Ptr]
  · iframe Pad Ptr
  ihave Hs := stk_join n (sp - 32).toNat 8 8 $$ [Hs W0]
  · iframe Hs W0
  ihave Hs := stk_join n (sp - 32).toNat 16 8 $$ [Hs W8]
  · simp only [Nat.add_assoc, Nat.reduceAdd]; iframe Hs W8
  ihave Hs := stk_join n (sp - 32).toNat 24 8 $$ [Hs W16]
  · iframe Hs W16
  ihave Hs := stk_addr h32 $$ Hs
  iframe Hc Hg Hs HQ
  iunfold args24
  iframe A0 A8 A16

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- Actual Formatter::write_fmt adapter retains the sink and original Arguments while lending an owned stack copy. -/
theorem f913_delegate (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 1 < lim.maxCallDepth) (Cg : Nat) (gt : GlobalType)
    (sp fmt data vtab ar : UInt32) (a0 a8 a16 : UInt64) (ret : UInt32) (Kw : Nat) (P Q : IProp GF)
    (hsp : 32 ≤ sp.toNat) (hfmt : fmt.toNat + 32 ≤ 2 ^ 32) (har : ar.toNat + 24 ≤ 2 ^ 32) :
    inst ↪[inst] mi ∗ A 872 ↪[wf] FuncInst.wasm types[15]! inst f872 ∗
      FormatterFmtEngineSpec cfg lim (d + 1) inst mi n g gt sp data vtab a0 a8 a16 ret Kw Cg P Q
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f913 Cg
        (fun args => iprop(⌜args = [.i32 fmt, .i32 ar]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          stk n (sp.toNat - 32) 32 ∗ n ↦[i32][ fmt.toNat + 24 ] data ∗
          n ↦[i32][ fmt.toNat + 28 ] vtab ∗ args24 n ar a0 a8 a16 ∗ P))
        (fun _ => 65 * cfg.regularOpCost +
          activationGas cfg.regularOpCost (entryLocals f872 [.i32 0, .i32 0, .i32 0]) + Kw)
        (fun _ rs => iprop(⌜rs = [.i32 ret]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          stk n (sp.toNat - 32) 32 ∗ n ↦[i32][ fmt.toNat + 24 ] data ∗
          n ↦[i32][ fmt.toNat + 28 ] vtab ∗ args24 n ar a0 a8 a16 ∗ Q)) := by
  unfold FormatterFmtEngineSpec
  iintro ⟨#Hi, #F872, #HS⟩
  have hn := hm.mem
  have hg := hm.glob
  have ha872 := hm.funcs 872 (by decide)
  have t15 : types[15]!.params.length = 3 := rfl
  have hlt := sp.toNat_lt
  have h32 : (sp - 32).toNat = sp.toNat - 32 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have h8 : (sp - 32 + 8).toNat = (sp - 32).toNat + 8 := by simp [UInt32.toNat_add]; omega
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, Data, Vtab, HA, HP⟩
  subst hargs
  iunfold args24 at HA
  icases HA with ⟨A0, A8, A16⟩
  ihave Hs := stk_addr h32.symm $$ Hs
  icases stk_split n _ 8 24 $$ Hs with ⟨Pad, Hs⟩
  icases stk_split n _ 8 16 $$ Hs with ⟨W0, Hs⟩
  icases stk_split n _ 8 8 $$ Hs with ⟨W8, W16⟩
  iunfold stk at W0 W8 W16
  icases W0 with ⟨%b0, %hb0, W0⟩
  icases W8 with ⟨%b8, %hb8, W8⟩
  icases W16 with ⟨%b16, %hb16, W16⟩
  simp only [f913]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep; mstep; mstep [Vtab]; mstep
  mstep; mstep [Data]; mstep
  mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep [A16]; mstep [W16]
  mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep [A8]; mstep [W8]
  mstep; mstep; mstep [A0]; mstep [W0]
  mstep; mstep; mstep; mstep; mstep
  simp only [U128From.decodeLE_storeBytes_i64, UInt64.ofNat_toNat]
  mcall HS using [Hg W0 W8 W16 HP] with (mstep_norm_full; omega)
  · iframe Hg HP
    iunfold args24
    have e0 : (sp - 32).toNat + 4 + 4 = (sp - 32 + 8).toNat := by omega
    have e8 : (sp - 32).toNat + 4 + 4 + 8 = (sp - 32 + 8).toNat + 8 := by omega
    have e16 : (sp - 32).toNat + 4 + 4 + 8 + 8 = (sp - 32 + 8).toNat + 16 := by omega
    simp only [e0, e8, e16]
    iframe W0 W8 W16
  icases HQ with ⟨%hrs, Hg, HA, HQ⟩
  subst hrs
  iunfold args24 at HA
  icases HA with ⟨W0, W8, W16⟩
  mstep; mstep; mstep; mstep; mstep [Hg]; mstep
  simp only [UInt32.sub_add_cancel]
  mcredits R
  simp only [Post.mfunc, htype, Nat.sub_self, List.drop_zero]
  ihave W0 := stk_intro n ((sp - 32 + 8).toNat) (storeBytes (.i64 a0) 8) $$ W0
  ihave W8 := stk_intro n ((sp - 32 + 8).toNat + 8) (storeBytes (.i64 a8) 8) $$ W8
  ihave W16 := stk_intro n ((sp - 32 + 8).toNat + 16) (storeBytes (.i64 a16) 8) $$ W16
  have hb (v : UInt64) : (storeBytes (.i64 v) 8).length = 8 := by simp [storeBytes, storeRaw]
  simp only [h8, hb, Nat.add_assoc, Nat.reduceAdd]
  ihave Hs := stk_join n (sp - 32).toNat 8 8 $$ [Pad W0]
  · iframe Pad W0
  ihave Hs := stk_join n (sp - 32).toNat 16 8 $$ [Hs W8]
  · simp only [Nat.add_assoc, Nat.reduceAdd]; iframe Hs W8
  ihave Hs := stk_join n (sp - 32).toNat 24 8 $$ [Hs W16]
  · iframe Hs W16
  ihave Hs := stk_addr h32 $$ Hs
  iframe Hc Hg Hs Data Vtab HQ
  iunfold args24
  iframe A0 A8 A16

/-- The deployed String deallocation wrapper is byte-for-byte the existing checked Global deallocator. -/
theorem string_deallocator_eq : f601 = f777 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- Actual String drop reads the retained vector and frees its live allocation exactly once. -/
theorem f599_drop (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 0) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 6 < lim.maxCallDepth) (Cg maxP len : Nat)
    (live : List (Nat × Nat)) (F : Nat) (v ptr cap : UInt32) (hv : v.toNat + 8 ≤ 2 ^ 32) :
    DropVec.dropCode inst mi A ∗ A 601 ↪[wf] FuncInst.wasm types[31]! inst f601 ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f599 Cg
        (fun args => iprop(⌜args = [.i32 v]⌝ ∗ n ↦[i32][ v.toNat ] ptr ∗
          n ↦[i32][ v.toNat + 4 ] cap ∗ AllocInv.heapInv n maxP len live F ∗
          (if cap = 0 then emp else ⌜(ptr.toNat, cap.toNat) ∈ live⌝ ∗ AllocInv.block n ptr.toNat cap.toNat)))
        (fun _ => 300 * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ n ↦[i32][ v.toNat ] ptr ∗ n ↦[i32][ v.toNat + 4 ] cap ∗
          AllocInv.heapInv n maxP len (if cap = 0 then live else live.erase (ptr.toNat, cap.toNat))
            (if cap = 0 then F else F + 1))) := by
  iintro ⟨#HD, #F601⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold DropVec.dropCode at HD
    icases HD with ⟨#Hi, -⟩
    iexact Hi
  have hn := hm.mem
  have ha601 := hm.funcs 601 (by decide)
  have t31 : types[31]!.params.length = 3 := rfl
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Ptr, Cap, Hinv, Hb⟩
  subst hargs
  by_cases hc : cap = 0
  · subst cap
    simp only [↓reduceIte, f599]
    mstep; mstep; mstep [Cap]; mstep; mstep; mstep
    mcredits R
    iframe Hc Ptr Cap Hinv
  · simp only [hc, ↓reduceIte]
    icases Hb with ⟨%hmem, Hb⟩
    ihave #S601 := DropVec.f777_spec cfg lim (d + 1) types[31]! rfl inst mi A n g ta hm
      (by omega) Cg maxP len live F ptr cap hc $$ HD
    simp only [f599]
    mstep; mstep; mstep [Cap]; mstep; mstep; mstep with simp [hc]
    mstep; mstep [Ptr]; mstep; mstep
    simp only [string_deallocator_eq]
    mcall S601 using [Hinv Hb] with (mstep_norm_full; omega)
    · iunfold DropVec.pre777
      iframe Hinv Hb
      ipureintro; exact ⟨rfl, hmem⟩
    iunfold DropVec.post777 at HQ
    icases HQ with ⟨%hrs, Hinv⟩
    subst hrs
    mcredits R
    iframe Hc Ptr Cap Hinv
    ipureintro; simp

end WNear.Binary.SerdeDebug
