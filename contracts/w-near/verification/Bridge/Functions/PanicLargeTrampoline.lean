import NearLogic.Hosts.PanicUtf8Large
import Bridge.Functions.PanicStr
import Bridge.Functions.PanicHook

namespace WNear.Binary.PanicTotal
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.PanicStr NearLogic.PanicUtf8Large
open WNear.Binary.Interface
open WNear.Binary.RegisterLen (frame4)
open WNear.Binary.SetBlockchainInterface (blockchainInterfaceCells)
open WNear.Binary.PanicHook
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_word stk_intro stk_addr)
variable {GF : BundledGFunctors} [WasmGS NearState GF]
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

/-- Exact controlled host failure and the single gas credit resource left by the oversize branch. -/
def failedLarge (Cg : Nat) (h : NearState) (len : UInt64) (limit : Nat) : IProp GF :=
  iprop(∃ h', ⌜erase h' = erase { h with lastError := some (largeError h len.toNat limit) }⌝ ∗
    mhostPt h' ∗ ∃ R, credits Cg R)

/-- Actual panic_utf8 trampoline uses the controlled oversize host contract, with no message-memory read. -/
theorem f262_large (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (inst : Nat) (mi : ModuleInst) (e n a22 : Nat) (mx : Option Nat)
    (hn : mi.memAddrs[0]? = some n) (ha : mi.funcAddrs[22]? = some a22) (Cg : Nat)
    (h : NearState) (dp : UInt32) (len ptr : UInt64) (limit : Nat)
    (hlen : len ≠ u64Max) (hlimit : h.config.maxLogLen = some limit)
    (hlarge : limit - (h.logs.map List.length).sum < len.toNat) :
    a22 ↪[wf] FuncInst.host (metered e "panic_utf8" panicUtf8Metered).toHostFn ∗ n ↪[wmlimit] mx ⊢
      MFunSpecT (GF := GF) cfg lim d type inst mi f262 Cg (trampPre n h dp len ptr [])
        (fun _ => 3 * cfg.regularOpCost + largeUse h) (fun _ _ => iprop(False))
        (fun _ => failedLarge Cg h len limit) := by
  iintro ⟨#Hh, #Hm⟩
  iapply MFunSpecT_intro
  imodintro
  iintro %args %R HP Hc
  iunfold trampPre at HP
  icases HP with ⟨%hargs, Hb, Hhost⟩
  subst hargs
  simp only [f262]
  mstep; mstep
  have hc := panicUtf8_large_contract (C := Cg) e h len ptr limit hlen hlimit hlarge
  iapply mwpi_call_host_trap' 22 a22 n ptr.toNat _ h _ mx [] [.i64 len, .i64 ptr] _ ha hn rfl hc
  iframe Hc Hh Hm Hhost Hb
  isplitr
  · ipureintro; mstep_norm_full; omega
  inext
  iintro %h' %hq Hhost Hc
  simp only [Post.mfunc]
  iunfold failedLarge
  iexists h'
  iframe Hhost Hc
  ipureintro; exact hq
open WNear.Binary.Interface
open WNear.Binary.RegisterLen (frame4)
open WNear.Binary.SetBlockchainInterface (blockchainInterfaceCells)
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000 in
/-- The actual installed-interface and RefCell path reaches the controlled oversized panic host failure. -/
theorem f448_large (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (inst : Nat) (mi : ModuleInst) (e : Nat) (A : Nat → Nat)
    (n g ta : Nat) (mx : Option Nat) (hm : IfaceMod mi A n g ta) (hd : d + 3 < lim.maxCallDepth)
    (Cg : Nat) (gi : GlobalInst) (sp : UInt32) (hgi : gi.value = .i32 sp) (hsp : 16 ≤ sp.toNat)
    (hal : sp.toNat % 8 = 0) (cp ptr len : UInt32) (w0 w4 w8 w12 : UInt32) (h : NearState) (limit : Nat)
    (hlimit : h.config.maxLogLen = some limit)
    (hlarge : limit - (h.logs.map List.length).sum < len.toNat) :
    ifaceCode e inst mi A n mx ∗ panicCode e inst mi A
      ⊢ MFunSpecT (GF := GF) cfg lim d type inst mi f448 Cg
        (withPre n g ta A gi sp cp ptr len [] w0 w4 w8 w12 h)
        (fun _ => 168 * cfg.regularOpCost + largeUse h) (fun _ _ => iprop(False))
        (fun _ => failedLarge Cg h (UInt64.ofNat len.toNat) limit) := by
  iintro ⟨#Hcode, #Hpc⟩
  iunfold ifaceCode at Hcode
  icases Hcode with ⟨#F565, #F468, #F429, #F494, #F672, #F430, #F431, #F432, #F433, #F241, #F260, #F284,
    #H1, #H20, #H43, #Hm, #Hi⟩
  iunfold panicCode at Hpc
  icases Hpc with ⟨#F262, #H22, -⟩
  iapply MFunSpecT_intro
  imodintro
  iintro %args %R HP Hc
  iunfold withPre at HP
  icases HP with ⟨%hargs, Hg, HI, HS, Hp, Hl, Hb, HF, Hhost⟩
  subst hargs
  iunfold iface, slot, blockchainInterfaceCells at HI
  icases HI with ⟨Hkey, T116, ⟨Hst, Hfl, Hda, Hvt⟩, -, -, -⟩
  iunfold panicSlot, slot at HS
  icases HS with ⟨S100, T60⟩
  iunfold frame4 at HF
  icases HF with ⟨W0, W4, W8, W12⟩
  obtain ⟨gt, gv⟩ := gi
  simp only at hgi
  subst hgi
  have hlt := sp.toNat_lt
  have ha429 := hm.funcs 429 (by decide)
  have ha430 := hm.funcs 430 (by decide)
  have t429 : types[31]!.params.length = 3 := by rfl
  have t430 : types[13]!.params.length = 2 := by rfl
  have hg := hm.glob
  have hn := hm.mem
  simp only [f448]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep
  mstep; mstep [Hkey]
  -- `__getit` through the table
  iapply mwpi_cons
  iapply (Borrow.mwpi_call_indirect' (ty := 1) (t := 0) (ta := ta) (idx := 116) (a := A 565)
    (type := types[1]!) (inst := inst) (mi := mi) (code := f565) [])
  isplitr
  · iapply (Borrow.f565_spec cfg lim (d + 1) types[1]! (by rfl) inst mi n (A 468) hm.mem
      (hm.funcs 468 (by decide)) types[13]! (by rfl) (by rfl) (by omega) Cg)
    mpersist
  isplitr
  · iexact F565
  isplitr
  · iexact Hi
  isplitl [T116]
  · simp only [UInt32.reduceToNat]; iexact T116
  isplitr
  · ipureintro; exact ⟨rfl, hm.table, by simp [hm.types], rfl, by omega⟩
  isplitl [Hc]
  · iexact Hc
  isplitr
  · ipureintro; mstep_norm_full; omega
  isplitl [Hst]
  · iunfold Borrow.getItPre
    iframe Hst
    ipureintro; rfl
  inext
  iintro %rs T116 Hc HQ
  iunfold Borrow.getItPost at HQ
  icases HQ with ⟨%hrs, Hst⟩
  subst hrs
  mctrl_norm
  -- not null
  mstep; mstep; mstep
  -- `RefCell::borrow`
  mstep; mstep; mstep
  mcall (Borrow.f429_spec cfg lim (d + 1) types[31]! (by rfl) inst mi n g (A 494) (A 672) hm.mem
      hm.glob (hm.funcs 494 (by decide)) (hm.funcs 672 (by decide)) types[32]! types[13]! (by rfl)
      (by rfl) (by rfl) (by rfl) (by omega) Cg { type := gt, value := .i32 (sp - 16) } (sp - 16) rfl
      (sp - 16) 1074904 1056196 w0 w4 (by decide)) using [Hg Hfl W0 W4]
  · iunfold Borrow.borrowPre
    simp only [UInt32.reduceToNat]
    iframe Hg Hfl W0 W4
  iunfold Borrow.borrowPost at HQ
  icases HQ with ⟨%hrs, Hg, Hfl, W0, W4⟩
  subst hrs
  simp only [UInt32.reduceToNat, UInt32.reduceAdd]
  -- the `Ref` copied
  mstep; mstep; mstep [W4]; mstep [W12]
  mstep; mstep; mstep [W0]; mstep; mstep [W8]
  -- the result flag
  mstep; mstep
  -- `Some`: the box
  mstep; mstep
  simp only [UInt32.reduceOfNat]
  mstep
  mstep [Hda]
  simp only [UInt32.reduceOfNat]
  iapply mwpi_cons
  iapply Borrow.mwpi_select_true'
  isplitl [Hc]
  · iexact Hc
  isplitr
  · ipureintro; exact ⟨by mstep_norm_full; omega, by decide⟩
  inext
  iintro Hc
  mctrl_norm
  mstep
  mcall (Borrow.f430_spec cfg lim (d + 1) types[13]! (by rfl) inst mi Cg 1074908 1056212
    (by decide))
  · iunfold Borrow.expectSomePre
    ipureintro; rfl
  iunfold Borrow.expectSomePost at HQ
  icases HQ with %hrs
  subst hrs
  -- the vtable's `panic_utf8`
  mstep; mstep [Hda]; mstep; mstep [Hl]; mstep; mstep [Hp]
  mstep; mstep [Hvt]
  simp only [UInt32.reduceOfNat]
  mstep [S100]
  simp only [UInt32.reduceOfNat, loadValue_i64_u32]
  iapply mwpi_cons
  iapply (mwpi_call_indirectT' (ty := 4) (t := 0) (ta := ta) (idx := 60) (a := A 262)
    (type := types[4]!) (inst := inst) (mi := mi) (code := f262)
    [.i32 1, .i64 (UInt64.ofNat len.toNat), .i64 (UInt64.ofNat ptr.toNat)])
  isplitr
  · iapply (f262_large cfg lim (d + 1) types[4]! inst mi e n (A 22) mx hm.mem (hm.funcs 22 (by decide))
      Cg h 1 (UInt64.ofNat len.toNat) (UInt64.ofNat ptr.toNat) limit (u64_ne len) hlimit
      (by rw [u64_toNat]; exact hlarge))
    mpersist
  isplitr
  · iexact F262
  isplitr
  · iexact Hi
  isplitl [T60]
  · simp only [UInt32.reduceToNat]; iexact T60
  isplitr
  · ipureintro; exact ⟨rfl, hm.table, by simp [hm.types], by rfl, by omega⟩
  isplitl [Hc]
  · iexact Hc
  isplitr
  · ipureintro; mstep_norm_full; omega
  isplitl [Hb Hhost]
  · iunfold trampPre
    rw [u64_toNat]
    iframe Hb Hhost
    ipureintro; rfl
  inext
  isplit
  · iintro %rs - - HF
    iexfalso
    iexact HF
  · iintro HT
    simp only [Post.mseq_trap, Post.mblock, Post.mfunc]
    iexact HT

set_option maxHeartbeats 16000000 in
/-- Actual env::panic_str follows its installed interface into the controlled oversized panic failure. -/
theorem f521_large (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (inst : Nat) (mi : ModuleInst) (e : Nat) (A : Nat → Nat)
    (n g ta : Nat) (mx : Option Nat) (hm : IfaceMod mi A n g ta) (hd : d + 4 < lim.maxCallDepth)
    (Cg : Nat) (gi : GlobalInst) (sp : UInt32) (hgi : gi.value = .i32 sp) (hsp : 32 ≤ sp.toNat)
    (hal : sp.toNat % 8 = 0) (ptr len : UInt32) (c0 c4 w0 w4 w8 w12 : UInt32)
    (h : NearState) (limit : Nat) (hlimit : h.config.maxLogLen = some limit)
    (hlarge : limit - (h.logs.map List.length).sum < len.toNat) :
    A 448 ↪[wf] FuncInst.wasm types[14]! inst f448 ∗ ifaceCode e inst mi A n mx ∗
      panicCode e inst mi A
      ⊢ MFunSpecT (GF := GF) cfg lim d type inst mi f521 Cg
        (pre n g ta A gi sp ptr len [] c0 c4 w0 w4 w8 w12 h)
        (fun _ => 194 * cfg.regularOpCost + largeUse h) (fun _ _ => iprop(False))
        (fun _ => failedLarge Cg h (UInt64.ofNat len.toNat) limit) := by
  iintro ⟨#F448, #Hcode, #Hpc⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold panicCode at Hpc
    icases Hpc with ⟨-, -, #Hi⟩
    iexact Hi
  iapply MFunSpecT_intro
  imodintro
  iintro %args %R HP Hc
  iunfold pre at HP
  icases HP with ⟨%hargs, Hg, HI, HS, C0, C4, HF, Hb, Hhost⟩
  subst hargs
  obtain ⟨gt, gv⟩ := gi
  simp only at hgi
  subst hgi
  have hlt := sp.toNat_lt
  have hg := hm.glob
  have hn := hm.mem
  have h16 : (sp - 16).toNat = sp.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have e8 : (sp - 16 + 8).toNat = (sp - 16).toNat + 8 := by simp [UInt32.toNat_add]; omega
  simp only [f521]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep; mstep [C4]
  mstep; mstep; mstep [C0]
  mstep; mstep; mstep; mstep
  iapply mwpi_cons
  iapply (mwpi_callT' (i := 448) (a := A 448) (type := types[14]!) (inst := inst) (mi := mi)
    (code := f448) [.i32 1055020, .i32 (sp - 16 + 8)])
  isplitr
  · iapply (f448_large cfg lim (d + 1) types[14]! inst mi e A n g ta mx hm (by omega) Cg
      { type := gt, value := .i32 (sp - 16) } (sp - 16) rfl (by omega) (by omega) (sp - 16 + 8) ptr len
      w0 w4 w8 w12 h limit hlimit hlarge)
    iframe Hcode Hpc
  isplitr
  · iexact F448
  isplitr
  · iexact Hi
  isplitr
  · ipureintro; exact ⟨rfl, hm.funcs 448 (by decide), rfl, by omega⟩
  isplitl [Hc]
  · iexact Hc
  isplitr
  · ipureintro; mstep_norm_full; omega
  isplitl [Hg HI HS C0 C4 HF Hb Hhost]
  · iunfold withPre
    rw [e8, show (sp - 16).toNat + 8 + 4 = (sp - 16).toNat + 12 by omega]
    iframe Hg HI HS C0 C4 HF Hb Hhost
    ipureintro; rfl
  inext
  isplit
  · iintro %rs - HF
    iexfalso
    iexact HF
  · iintro HT
    simp only [Post.mseq_trap, Post.mfunc]
    iexact HT

end WNear.Binary.PanicTotal
