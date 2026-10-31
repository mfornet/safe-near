import Bridge.Functions.PanicLargeTrampoline
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

open WNear.Binary.PanicHook
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_word stk_intro stk_addr)

def cost474Large (cfg : WasmConfig) (K : Nat) (h : NearState) : Nat :=
  285 * cfg.regularOpCost + K + largeUse h

theorem nilBytes (n ptr : Nat) : ⊢ (n ↦[wms][ ptr ] ([] : List UInt8) : IProp GF) := by
  unfold WasmLogic.memBytes
  simp only [byteCells]
  exact BigSepL.bigSepL_nil.2

set_option maxHeartbeats 16000000 in
/-- Actual panic hook formats its message and follows the controlled oversized-message failure. -/
theorem f474_large (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (inst : Nat) (mi : ModuleInst) (e : Nat) (A : Nat → Nat) (n g ta : Nat) (mx : Option Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 6 < lim.maxCallDepth) (Cg : Nat) (gt : GlobalType)
    (sp ip : UInt32) (S : Nat) (hS : 32 ≤ S) (hsp : S + 32 ≤ sp.toNat) (hal : sp.toNat % 8 = 0)
    (D : IProp GF) (K : Nat) (bs : List UInt8) (hlen : bs.length < 2 ^ 32)
    (h : NearState) (limit : Nat) (hlimit : h.config.maxLogLen = some limit)
    (hlarge : limit - (h.logs.map List.length).sum < bs.length) :
    hookCode e inst mi A n mx ∗ ToStr cfg lim (d + 1) inst mi Cg n g gt (sp - 32) ip S D K bs
      ⊢ MFunSpecT (GF := GF) cfg lim d type inst mi f474 Cg (hookPre n g ta A gt sp ip S D h)
        (fun _ => cost474Large cfg K h) (fun _ _ => iprop(False)) (fun _ => failedLarge Cg h (UInt64.ofNat bs.length) limit) := by
  iintro ⟨#Hcode, #Hts⟩
  iunfold hookCode at Hcode
  icases Hcode with ⟨#F470, #F511, #F779, #F521, #F448, #Hic, #Hpc⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold panicCode at Hpc
    icases Hpc with ⟨-, -, #Hi⟩
    iexact Hi
  have hn := hm.mem
  have hg := hm.glob
  have hlt := sp.toNat_lt
  have h32 : (sp - 32).toNat = sp.toNat - 32 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have e16 : (sp - 32 + 16).toNat = (sp - 32).toNat + 16 := by simp [UInt32.toNat_add]; omega
  have e8 : (sp - 32 + 8).toNat = (sp - 32).toNat + 8 := by simp [UInt32.toNat_add]; omega
  have ha470 := hm.funcs 470 (by decide)
  have ha511 := hm.funcs 511 (by decide)
  have ha521 := hm.funcs 521 (by decide)
  iunfold ToStr at Hts
  have t14 : types[14]!.params.length = 2 := by rfl
  iapply MFunSpecT_intro
  imodintro
  iintro %args %R HP Hc
  iunfold hookPre at HP
  icases HP with ⟨%hargs, Hg, Hs, HI, HS, HD, Hh⟩
  subst hargs
  icases stk_hook n sp S hS hsp $$ Hs with ⟨Hlo, -, H8, Hstr, -⟩
  simp only [f474, cost474Large]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep; mstep; mstep
  -- `info.to_string()`
  mcall Hts using [Hg Hlo Hstr HD]
  · iframe Hg Hlo HD Hstr
  icases HQ with ⟨%hrs, Hg, Hlo, %ptr, %cap, Q16, Q20, Q24, Hb⟩
  subst hrs
  -- `as_str`
  icases stk_split n _ 4 4 $$ H8 with ⟨H8, H12⟩
  icases stk4_word n _ $$ H8 with ⟨%o0, H8⟩
  icases stk4_word n _ $$ H12 with ⟨%o4, H12⟩
  icases stk_split' n _ S (S - 16) 16 (by omega) $$ Hlo with ⟨Hlo, Hf⟩
  icases stk_split n _ 8 8 $$ Hf with ⟨Hf0, Hf8⟩
  icases stk_split n _ 4 4 $$ Hf8 with ⟨Ha, Hb'⟩
  icases stk4_word n _ $$ Ha with ⟨%a, Ha⟩
  icases stk4_word n _ $$ Hb' with ⟨%b, Hb'⟩
  have hs16 : (sp - 32 - 16).toNat = (sp - 32).toNat - 16 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le] <;> omega
  mstep; mstep; mstep; mstep; mstep; mstep
  mcall (f511_spec cfg lim (d + 1) types[14]! (by rfl) inst mi A n g ta hm (by omega) Cg gt (sp - 32)
      (sp - 32 + 8) (sp - 32 + 16) ptr (UInt32.ofNat bs.length) o0 o4 a b (by omega))
    using [Hg Ha Hb' H8 H12 Q16 Q24]
  · iunfold asStrPre
    rw [hs16, e8, e16]
    isplitr
    · ipureintro; rfl
    iframe Hg
    isplitl [Ha]
    · iapply memBytes_congr (by omega) |>.1 $$ Ha
    isplitl [Hb']
    · iapply memBytes_congr (by omega) |>.1 $$ Hb'
    isplitl [H8]
    · iexact H8
    isplitl [H12]
    · iapply memBytes_congr (by omega) |>.1 $$ H12
    isplitl [Q16]
    · iexact Q16
    iapply memBytes_congr (by omega) |>.1 $$ Q24
  iunfold asStrPost at HQ
  icases HQ with ⟨%hrs, Hg, Ha, Hb', H8, H12, Q16, Q24⟩
  subst hrs
  rw [e8] at *
  -- `env::panic_str(ptr, len)`
  mstep; mstep [H8]
  mstep; mstep [H12]
  have hL : (UInt32.ofNat bs.length).toNat = bs.length := by
    simp only [UInt32.toNat_ofNat']; omega
  icases stk_split' n _ (S - 16) (S - 32) 16 (by omega) $$ Hlo with ⟨-, Hfr⟩
  have h64 : (sp - 32 - 16 - 16).toNat = sp.toNat - 64 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le, hs16, h32] <;> omega
  ihave Hfr := stk_addr (show (sp - 32).toNat - S + (S - 32) = (sp - 32 - 16 - 16).toNat by omega) $$ Hfr
  icases stk16_frame4 n _ $$ Hfr with ⟨%w0, %w4, %w8, %w12, Hfr⟩
  iapply mwpi_cons
  iapply mwpi_callT' (i := 521) (a := A 521) (type := types[14]!) (inst := inst) (mi := mi)
    (code := f521) [.i32 ptr, .i32 (UInt32.ofNat bs.length)]
  isplitr
  · iapply (f521_large cfg lim (d + 1) types[14]! inst mi e A n g ta mx hm (by omega) Cg
      { type := gt, value := .i32 (sp - 32) } (sp - 32) rfl (by omega) (by omega) ptr
      (UInt32.ofNat bs.length) ptr (UInt32.ofNat bs.length) w0 w4 w8 w12 h limit hlimit
      (by rw [hL]; exact hlarge))
    iframe F448 Hic Hpc
  isplitr
  · iexact F521
  isplitr
  · iexact Hi
  isplitr
  · ipureintro; exact ⟨rfl, ha521, rfl, by omega⟩
  isplitl [Hc]
  · iexact Hc
  isplitr
  · ipureintro; mstep_norm_full; omega
  isplitl [Hg HI HS Ha Hb' Hfr Hh]
  · iunfold PanicStr.pre
    iframe Hg HI HS Ha Hb' Hfr Hh
    isplitr
    · ipureintro; rfl
    iapply nilBytes
  inext
  isplit
  · iintro %rs - HF
    iexfalso
    iexact HF
  · iintro HT
    simp only [Post.mseq_trap, Post.mfunc, hL]
    iexact HT


/-- Larger gas allowances can fund the same checked trapping behavior without creating a second credit resource. -/
theorem trap_cost_mono (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (inst : Nat) (mi : ModuleInst) (code : Func) (Cg : Nat) (P : List Value → IProp GF)
    (K0 K1 : List Value → Nat) (Q : List Value → List Value → IProp GF) (T : List Value → IProp GF)
    (hK : ∀ args, K0 args ≤ K1 args) :
    MFunSpecT cfg lim d type inst mi code Cg P K0 Q T ⊢ MFunSpecT cfg lim d type inst mi code Cg P K1 Q T := by
  unfold MFunSpecT
  iintro #H
  imodintro
  iintro %args %R HP Hc
  iapply H $$ %args %R HP
  iapply BorrowMut.credits_le
  iframe Hc
  ipureintro
  have := hK args
  omega

theorem largeUse_le (h : NearState) (n : Nat) : largeUse h ≤ panicUtf8Use h n := by
  simp only [largeUse, largeCharges, panicUtf8Use, panicUtf8Charges, chargesUse, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil]
  omega

/-- Exact host error selected by the actual explicit-length panic reader. -/
def expectedError (h : NearState) (bs : List UInt8) : HostError :=
  match h.config.maxLogLen with
  | none => .guestPanic (utf8String bs)
  | some limit => if limit - (h.logs.map List.length).sum < bs.length
      then largeError h bs.length limit else .guestPanic (utf8String bs)

def failedWith (Cg : Nat) (h : NearState) (error : HostError) : IProp GF :=
  iprop(∃ h', ⌜erase h' = erase { h with lastError := some error }⌝ ∗ mhostPt h' ∗ ∃ R, credits Cg R)

set_option maxHeartbeats 16000000 in
/-- Actual panic hook covers fitting and oversized messages with the exact selected protocol error. -/
theorem f474_total (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (inst : Nat) (mi : ModuleInst) (e : Nat) (A : Nat → Nat) (n g ta : Nat) (mx : Option Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 6 < lim.maxCallDepth) (Cg : Nat) (gt : GlobalType)
    (sp ip : UInt32) (S : Nat) (hS : 32 ≤ S) (hsp : S + 32 ≤ sp.toNat) (hal : sp.toNat % 8 = 0)
    (D : IProp GF) (K : Nat) (bs : List UInt8) (hpos : 0 < bs.length) (hlen : bs.length < 2 ^ 32)
    (hutf : validUtf8 bs = true) (h : NearState)
    (hov : h.extCosts.cost "read_memory_byte" * bs.length < 2 ^ 64) :
    hookCode e inst mi A n mx ∗ ToStr cfg lim (d + 1) inst mi Cg n g gt (sp - 32) ip S D K bs ⊢
      MFunSpecT (GF := GF) cfg lim d type inst mi f474 Cg (hookPre n g ta A gt sp ip S D h)
        (fun _ => cost474 cfg K bs h) (fun _ _ => iprop(False))
        (fun _ => failedWith Cg h (expectedError h bs)) := by
  iintro ⟨#HC, #HS⟩
  by_cases hfit : LogFits h bs.length
  · have he : expectedError h bs = .guestPanic (utf8String bs) := by
      unfold expectedError
      cases hc : h.config.maxLogLen with
      | none => rfl
      | some limit =>
        have hf := hfit limit hc
        have hn : ¬ limit - (h.logs.map List.length).sum < bs.length := by omega
        simp only [if_neg hn]
    have ht : panicked (GF := GF) Cg h bs = failedWith Cg h (expectedError h bs) := by
      simp only [panicked, failedWith, he]
    rw [← ht]
    iapply (f474_spec cfg lim d type inst mi e A n g ta mx hm hd Cg gt sp ip S hS hsp hal D K bs
      hpos hlen hutf h hfit hov)
    iframe HC HS
  · obtain ⟨limit, hc, hl⟩ := (log_length_cases h bs.length hpos).resolve_left hfit
    have he : expectedError h bs = largeError h bs.length limit := by simp only [expectedError, hc, if_pos hl]
    have h64 : (UInt64.ofNat bs.length).toNat = bs.length := by
      simp only [UInt64.toNat_ofNat']; omega
    have ht : failedLarge (GF := GF) Cg h (UInt64.ofNat bs.length) limit =
        failedWith Cg h (expectedError h bs) := by simp only [failedLarge, failedWith, he, h64]
    rw [← ht]
    iapply (trap_cost_mono cfg lim d type inst mi f474 Cg (hookPre n g ta A gt sp ip S D h)
      (fun _ => cost474Large cfg K h) (fun _ => cost474 cfg K bs h) (fun _ _ => iprop(False))
      (fun _ => failedLarge Cg h (UInt64.ofNat bs.length) limit)
      (by intro args; have := largeUse_le h bs.length; unfold cost474Large cost474; omega))
    iapply (f474_large cfg lim d type inst mi e A n g ta mx hm hd Cg gt sp ip S hS hsp hal D K bs
      hlen h limit hc hl)
    iframe HC HS

/-- Both selected panic outcomes are concrete protocol failures. -/
theorem expectedError_no_issue (h : NearState) (bs : List UInt8) :
    FunctionCallError.issue? (.hostError (expectedError h bs)) = none := by
  unfold expectedError
  split
  · rfl
  · split <;> rfl

theorem expectedError_not_out_of_gas (h : NearState) (bs : List UInt8) :
    FunctionCallError.isOutOfGas (.hostError (expectedError h bs)) = false := by
  unfold expectedError
  split
  · rfl
  · split <;> rfl

set_option maxHeartbeats 16000000 in
/-- Actual installed hook callback composes both message-size branches without a LogFits premise. -/
theorem f473_total (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (inst : Nat) (mi : ModuleInst) (e : Nat) (A : Nat → Nat) (n g ta : Nat) (mx : Option Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 7 < lim.maxCallDepth) (Cg : Nat) (gt : GlobalType)
    (sp self ip : UInt32) (S : Nat) (hS : 32 ≤ S) (hsp : S + 32 ≤ sp.toNat) (hal : sp.toNat % 8 = 0)
    (D : IProp GF) (K : Nat) (bs : List UInt8) (hpos : 0 < bs.length) (hlen : bs.length < 2 ^ 32)
    (hutf : validUtf8 bs = true) (h : NearState)
    (hov : h.extCosts.cost "read_memory_byte" * bs.length < 2 ^ 64) :
    A 474 ↪[wf] FuncInst.wasm types[0]! inst f474 ∗ hookCode e inst mi A n mx ∗
      ToStr cfg lim (d + 2) inst mi Cg n g gt (sp - 32) ip S D K bs
      ⊢ MFunSpecT (GF := GF) cfg lim d type inst mi f473 Cg
        (fun args => iprop(⌜args = [.i32 self, .i32 ip]⌝ ∗ hookPre n g ta A gt sp ip S D h [.i32 ip]))
        (fun _ => 11 * cfg.regularOpCost + cost474 cfg K bs h) (fun _ _ => iprop(False))
        (fun _ => failedWith Cg h (expectedError h bs)) := by
  iintro ⟨#F474, #Hcode, #Hts⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold hookCode, panicCode at Hcode
    icases Hcode with ⟨-, -, -, -, -, -, -, -, #Hi⟩
    iexact Hi
  have ha474 := hm.funcs 474 (by decide)
  iapply MFunSpecT_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, HP⟩
  subst hargs
  simp only [f473]
  mstep
  iapply mwpi_cons
  iapply mwpi_callT' (i := 474) (a := A 474) (type := types[0]!) (inst := inst) (mi := mi)
    (code := f474) [.i32 ip]
  isplitr
  · iapply (f474_total cfg lim (d + 1) types[0]! inst mi e A n g ta mx hm (by omega) Cg gt sp ip S hS hsp
      hal D K bs hpos hlen hutf h hov)
    iframe Hcode Hts
  isplitr
  · iexact F474
  isplitr
  · iexact Hi
  isplitr
  · ipureintro; exact ⟨rfl, ha474, rfl, by omega⟩
  isplitl [Hc]
  · iexact Hc
  isplitr
  · ipureintro; mstep_norm_full; omega
  isplitl [HP]
  · iexact HP
  inext
  isplit
  · iintro %rs - HF
    iexfalso
    iexact HF
  · iintro HT
    simp only [Post.mseq_trap, Post.mfunc]
    iexact HT

end WNear.Binary.PanicTotal
