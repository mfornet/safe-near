import Bridge.Functions.FmtGrowRe

/-!
# `fmt::write`'s `String` sink (759) without room on a nonempty `String`

`FmtSink` specifies `write_str` (759 → 757 → 734 → 735 → 768 → 775) with room and on an empty
`String`. Here the third case: the `String` `(ptr, cap, |w|)` holds a live block, `cap ≠ 0`, and
the `k` bytes do not fit (`cap < |w| + k`). `reserve` (775) calls `grow_amortized` (776,
`FmtGrowRe.f776_re`), which reallocates the block to `c = growCap cap (|w| + k)`; then the copy.

734, 735 and 775 are `VecGrow`'s 697, 698 and 715 (same code, other callees), and the proofs are
theirs; 768 is `FmtSink.f768_grow`'s shape (`handle_reserve`, 773). The shapes `growPreS` and
`growPostS` are `VecGrow.growPre`/`growPost` with 112 bytes of stack (768's frame, 776's 48, 772's
16, the realloc's 16, and `Layout`'s).

Cost of 759 (`regular_op_cost`s, activation excluded): `costGrowS cfg F cap c`, i.e.
`640 + mc k` and the realloc's `cost154 cfg F cap c`.
-/

namespace WNear.Binary.FmtSinkRe

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.AllocNewCell (memBytes_addr cellPages)
open WNear.Binary.AllocZeroed (allocCode)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_word stk_addr roomFor grownLen)
open WNear.Binary.VecWithCap (vecCode2)
open WNear.Binary.BorshFT (splitB joinB stkJ stkSp stkA)
open WNear.Binary.VecGrow (reallocCode reallocated cost154 growCap growCap_toNat grownV)
open WNear.Binary.FmtSink (sinkCode add_sub_left f773_ok)
open WNear.Binary.FmtGrowRe (pre776r post776r f776_re)

section Spec

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The code of the sink with the realloc (persistent). -/
def sinkCodeR (n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) : IProp GF :=
  iprop(sinkCode n maxP inst mi A ∗ reallocCode n maxP inst mi A)

instance (n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) :
    Persistent (sinkCodeR (GF := GF) n maxP inst mi A) := by
  unfold sinkCodeR; infer_instance

theorem sinkCodeR_inst (n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) :
    sinkCodeR (GF := GF) n maxP inst mi A ⊢ inst ↪[inst] mi := by
  iintro #Hk
  iunfold sinkCodeR, sinkCode at Hk
  icases Hk with ⟨⟨#Hv, -⟩, -⟩
  iunfold vecCode2, allocCode at Hv
  icases Hv with ⟨⟨-, -, -, -, -, -, -, -, -, -, -, #Hi⟩, -⟩
  iexact Hi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- `reserve(out, vec, len, k)` (775) without room on a nonempty buffer: `grow_amortized` (776). -/
theorem f775_re (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 11 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s out vec len k ptr cap : UInt32) (idx : UInt32) (maxP hl : Nat)
    (live : List (Nat × Nat)) (F : Nat) (bs ob : List UInt8) (hs : 96 ≤ s.toNat) (hob : ob.length = 4)
    (hout : out.toNat + 4 ≤ 2 ^ 32) (hvec : vec.toNat + 8 ≤ 2 ^ 32) (hptr : ptr ≠ 0) (hcap : 0 < cap.toNat)
    (hcap2 : cap.toNat < 2 ^ 27) (hlen : len.toNat ≤ cap.toNat) (hgrow : cap.toNat < len.toNat + k.toNat)
    (hlk : len.toNat + k.toNat < 2 ^ 28) (hbs : bs.length = cap.toNat)
    (hlive : (ptr.toNat, cap.toNat) ∈ live) (hr : roomFor hl maxP (growCap cap (len + k))) :
    sinkCodeR n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f775 Cg
        (pre776r n g gt s out vec len k ptr cap idx ta (A 578) maxP hl live F bs ob)
        (fun _ => 430 * cfg.regularOpCost + cost154 cfg F cap (growCap cap (len + k)))
        (post776r n g gt s out vec len k ptr cap idx ta (A 578) maxP hl live F bs) := by
  iintro #Hk
  ihave #Hi := sinkCodeR_inst n maxP inst mi A $$ Hk
  iunfold sinkCodeR, sinkCode at Hk
  icases Hk with ⟨⟨#Hv, #H772, #H776, -⟩, #HR⟩
  ihave #S776 := f776_re (GF := GF) cfg lim (d + 1) types[45]! rfl inst mi A n g ta hm (by omega) Cg gt s out vec
    len k ptr cap idx maxP hl live F bs ob hs hob hout hvec hptr hcap hcap2 hlk hbs hlive hr $$ [Hv HR H772]
  · iframe Hv HR H772
  have hn := hm.mem
  have ha776 := hm.funcs 776 (by decide)
  have t45 : types[45]!.params.length = 4 := by rfl
  have hge : Numeric.bool (Numeric.irelop32 IRelOp.ge_u (cap - len) k) = 0 := by
    have : (cap - len).toNat = cap.toNat - len.toNat := by
      rw [UInt32.toNat_sub_of_le]; simp [UInt32.le_iff_toNat_le]; omega
    simp [Numeric.irelop32, Numeric.bool, UInt32.le_iff_toNat_le, this]; omega
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold pre776r at HP
  icases HP with ⟨%hargs, Hg, Hs, Hvt, Hinv, Hp, Hcap, Hbs, Ho⟩
  subst hargs
  simp only [f775]
  repeat mstep
  mstep [Hcap]
  repeat mstep
  mcall S776 using [Hg Hs Hvt Hinv Hp Hcap Hbs Ho]
  · iunfold pre776r
    iframe Hg Hs Hvt Hinv Hp Hcap Hbs Ho
    ipureintro; rfl
  repeat mstep
  mcredits R
  iframe Hc
  iunfold post776r at HQ
  icases HQ with ⟨%hrs, HQ⟩
  subst hrs
  rw [htype]
  iunfold post776r
  isplitr
  · ipureintro; rfl
  iexact HQ

/-- 768 and 735 without room: the precondition (112 bytes of stack). -/
def pre768g (n g : Nat) (gt : GlobalType) (s vec ptr cap len : UInt32) (idx : UInt32) (ta a578 maxP hl : Nat)
    (live : List (Nat × Nat)) (F : Nat) (bs : List UInt8) : IProp GF :=
  iprop(g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 112) 112 ∗ vt n 1057464 idx ta a578 ∗
    heapInv n maxP hl live F ∗ n ↦[i32][ vec.toNat ] ptr ∗ n ↦[i32][ vec.toNat + 4 ] cap ∗
    n ↦[i32][ vec.toNat + 8 ] len ∗ n ↦[wms][ ptr.toNat ] bs)

/-- … and the postcondition: the buffer reallocated at `q` with the capacity `c`. -/
def post768g (n g : Nat) (gt : GlobalType) (s vec ptr cap len c : UInt32) (idx : UInt32) (ta a578 maxP hl : Nat)
    (live : List (Nat × Nat)) (F : Nat) (bs : List UInt8) : IProp GF :=
  iprop(∃ q : UInt32, g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 112) 112 ∗ vt n 1057464 idx ta a578 ∗
    n ↦[i32][ vec.toNat ] q ∗ n ↦[i32][ vec.toNat + 4 ] c ∗ n ↦[i32][ vec.toNat + 8 ] len ∗
    reallocated n maxP hl live F ptr cap c q bs)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- `do_reserve_and_handle(vec, len, k)` (768) without room on a nonempty buffer: `reserve` (775)
grows, `handle_reserve` (773) on `Ok`. -/
theorem f768_re (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 12 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s vec len k ptr cap : UInt32) (idx : UInt32) (maxP hl : Nat)
    (live : List (Nat × Nat)) (F : Nat) (bs : List UInt8) (hs : 112 ≤ s.toNat)
    (hvec : vec.toNat + 12 ≤ 2 ^ 32) (hptr : ptr ≠ 0) (hcap : 0 < cap.toNat)
    (hcap2 : cap.toNat < 2 ^ 27) (hlen : len.toNat ≤ cap.toNat) (hgrow : cap.toNat < len.toNat + k.toNat)
    (hlk : len.toNat + k.toNat < 2 ^ 28) (hbs : bs.length = cap.toNat)
    (hlive : (ptr.toNat, cap.toNat) ∈ live) (hr : roomFor hl maxP (growCap cap (len + k))) :
    sinkCodeR n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f768 Cg
        (fun args => iprop(⌜args = [.i32 vec, .i32 len, .i32 k]⌝ ∗
          pre768g n g gt s vec ptr cap len idx ta (A 578) maxP hl live F bs))
        (fun _ => 480 * cfg.regularOpCost + cost154 cfg F cap (growCap cap (len + k)))
        (fun _ rs => iprop(⌜rs = []⌝ ∗
          post768g n g gt s vec ptr cap len (growCap cap (len + k)) idx ta (A 578) maxP hl live F bs)) := by
  iintro #Hk
  ihave #Hi := sinkCodeR_inst n maxP inst mi A $$ Hk
  ihave #Hk' := Hk
  iunfold sinkCodeR, sinkCode at Hk'
  icases Hk' with ⟨⟨-, -, -, #H775, #H773, -⟩, -⟩
  have hn := hm.mem
  have hg := hm.glob
  have ha775 := hm.funcs 775 (by decide)
  have ha773 := hm.funcs 773 (by decide)
  have t45 : types[45]!.params.length = 4 := by rfl
  have t0 : types[0]!.params.length = 1 := by rfl
  have hlt := s.toNat_lt
  have h16 : (s - 16).toNat = s.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, HP⟩
  iunfold pre768g at HP
  icases HP with ⟨Hg, Hs, Hvt, Hinv, Hp, Hcap, Hlen, Hbs⟩
  subst hargs
  icases stk_split n (s.toNat - 112) 96 16 $$ Hs with ⟨Lo, Hs⟩
  icases stk_split n (s.toNat - 112 + 96) 4 12 $$ Hs with ⟨O, U⟩
  iunfold stk at O
  icases O with ⟨%ob, %hob, O⟩
  ihave O := memBytes_addr (show s.toNat - 112 + 96 = (s - 16).toNat by omega) $$ O
  ihave #S775 := f775_re (GF := GF) cfg lim (d + 1) types[45]! rfl inst mi A n g ta hm (by omega) Cg gt (s - 16)
    (s - 16) vec len k ptr cap idx maxP hl live F bs ob (by omega) hob (by omega) (by omega) hptr hcap hcap2 hlen
    hgrow hlk hbs hlive hr $$ Hk
  simp only [f768]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  repeat mstep
  mcall S775 using [Hg Lo Hvt Hinv Hp Hcap Hbs O]
  · iunfold pre776r
    ihave Lo := stk_addr (show s.toNat - 112 = (s - 16).toNat - 96 by omega) $$ Lo
    iframe Hg Lo Hvt Hinv Hp Hcap Hbs O
    ipureintro; rfl
  iunfold post776r at HQ
  icases HQ with ⟨%hrs, %q, Hg, Lo, Hvt, Hp, Hcap, O, HA⟩
  subst hrs
  repeat mstep
  mcall (f773_ok cfg lim (d + 1) types[0]! (by rfl) inst mi n hn Cg (s - 16) (by omega)) using [O]
  · iframe O
  icases HQ with ⟨%hrs, O⟩
  subst hrs
  repeat mstep
  mstep [Hg]
  rw [show s - 16 + 16 = s by simp]
  repeat mstep
  mcredits R
  iframe Hc
  isplitr
  · ipureintro; simp [htype]
  iunfold post768g
  iexists q
  iframe Hg Hvt Hp Hcap Hlen HA
  ihave Lo := stk_addr (show (s - 16).toNat - 96 = s.toNat - 112 by omega) $$ Lo
  ihave O := stk_word n _ 0 $$ O
  ihave O := stk_addr (show (s - 16).toNat = s.toNat - 112 + 96 by omega) $$ O
  ihave O := stk_join n (s.toNat - 112 + 96) 4 12 $$ [O U]
  · iframe O U
  iapply stk_join n (s.toNat - 112) 96 16
  iframe Lo O

/-- `reserve(vec, k)` (735) without room on a nonempty buffer: `do_reserve_and_handle` (768). -/
theorem f735_re (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 13 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s vec len k ptr cap : UInt32) (idx : UInt32) (maxP hl : Nat)
    (live : List (Nat × Nat)) (F : Nat) (bs : List UInt8) (hs : 112 ≤ s.toNat)
    (hvec : vec.toNat + 12 ≤ 2 ^ 32) (hptr : ptr ≠ 0) (hcap : 0 < cap.toNat)
    (hcap2 : cap.toNat < 2 ^ 27) (hlen : len.toNat ≤ cap.toNat) (hgrow : cap.toNat < len.toNat + k.toNat)
    (hlk : len.toNat + k.toNat < 2 ^ 28) (hbs : bs.length = cap.toNat)
    (hlive : (ptr.toNat, cap.toNat) ∈ live) (hr : roomFor hl maxP (growCap cap (len + k))) :
    sinkCodeR n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f735 Cg
        (fun args => iprop(⌜args = [.i32 vec, .i32 k]⌝ ∗
          pre768g n g gt s vec ptr cap len idx ta (A 578) maxP hl live F bs))
        (fun _ => 500 * cfg.regularOpCost + cost154 cfg F cap (growCap cap (len + k)))
        (fun _ rs => iprop(⌜rs = []⌝ ∗
          post768g n g gt s vec ptr cap len (growCap cap (len + k)) idx ta (A 578) maxP hl live F bs)) := by
  iintro #Hk
  ihave #S768 := f768_re (GF := GF) cfg lim (d + 1) types[31]! rfl inst mi A n g ta hm (by omega) Cg gt s vec
    len k ptr cap idx maxP hl live F bs hs hvec hptr hcap hcap2 hlen hgrow hlk hbs hlive hr $$ Hk
  ihave #Hi := sinkCodeR_inst n maxP inst mi A $$ Hk
  iunfold sinkCodeR, sinkCode at Hk
  icases Hk with ⟨⟨-, -, -, -, -, #H768, -⟩, -⟩
  have hn := hm.mem
  have ha768 := hm.funcs 768 (by decide)
  have t31 : types[31]!.params.length = 3 := by rfl
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, HP⟩
  subst hargs
  iunfold pre768g at HP
  icases HP with ⟨Hg, Hs, Hvt, Hinv, Hp, Hcap, Hlen, Hbs⟩
  simp only [f735]
  repeat mstep
  mstep [Hlen]
  repeat mstep
  mcall S768 using [Hg Hs Hvt Hinv Hp Hcap Hlen Hbs]
  · iunfold pre768g
    iframe Hg Hs Hvt Hinv Hp Hcap Hlen Hbs
  icases HQ with ⟨%hrs, HQ⟩
  subst hrs
  mcredits R
  iframe Hc HQ
  ipureintro; simp [htype]

/-- 734 and above without room: the `String` `(ptr, cap, |w|)` at `vec` holding `w` then `rest`,
live; the `k` bytes `sb` at `p`; 112 bytes of stack. -/
def growPreS (n g : Nat) (gt : GlobalType) (s vec ptr cap p : UInt32) (idx : UInt32) (ta a578 maxP hl : Nat)
    (live : List (Nat × Nat)) (F : Nat) (w rest sb : List UInt8) : IProp GF :=
  iprop(g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 112) 112 ∗ vt n 1057464 idx ta a578 ∗
    heapInv n maxP hl live F ∗ n ↦[i32][ vec.toNat ] ptr ∗ n ↦[i32][ vec.toNat + 4 ] cap ∗
    n ↦[i32][ vec.toNat + 8 ] UInt32.ofNat w.length ∗ n ↦[wms][ ptr.toNat ] (w ++ rest) ∗ n ↦[wms][ p.toNat ] sb)

/-- … after: `sb` appended in the buffer reallocated at `q` with the capacity `c`. -/
def growPostS (n g : Nat) (gt : GlobalType) (s vec ptr cap c p : UInt32) (idx : UInt32) (ta a578 maxP hl : Nat)
    (live : List (Nat × Nat)) (F : Nat) (w sb : List UInt8) : IProp GF :=
  iprop(∃ q : UInt32, g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 112) 112 ∗ vt n 1057464 idx ta a578 ∗
    n ↦[i32][ vec.toNat ] q ∗ n ↦[i32][ vec.toNat + 4 ] c ∗
    n ↦[i32][ vec.toNat + 8 ] UInt32.ofNat (w ++ sb).length ∗ n ↦[wms][ q.toNat ] (w ++ sb) ∗
    (∃ tail : List UInt8, ⌜(w ++ sb).length + tail.length = c.toNat⌝ ∗
      n ↦[wms][ q.toNat + (w ++ sb).length ] tail) ∗
    grownV n maxP hl live F ptr cap c q ∗ n ↦[wms][ p.toNat ] sb)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- `spec_extend(vec, p, p + k)` (734) without room on a nonempty buffer: `reserve` (735) grows the
buffer, then the copy (951). -/
theorem f734_re (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 14 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s vec ptr cap p k : UInt32) (idx : UInt32) (maxP hl : Nat)
    (live : List (Nat × Nat)) (F : Nat) (w rest sb : List UInt8) (hs : 112 ≤ s.toNat)
    (hvec : vec.toNat + 12 ≤ 2 ^ 32) (hptr : ptr ≠ 0) (hcap : 0 < cap.toNat) (hcap2 : cap.toNat < 2 ^ 27)
    (hwr : w.length + rest.length = cap.toNat) (hsb : sb.length = k.toNat)
    (hgrow : cap.toNat < w.length + k.toNat) (hlk : w.length + k.toNat < 2 ^ 28)
    (hp : p.toNat + k.toNat ≤ 2 ^ 32)
    (hlive : (ptr.toNat, cap.toNat) ∈ live) (hr : roomFor hl maxP (growCap cap (UInt32.ofNat w.length + k))) :
    sinkCodeR n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f734 Cg
        (fun args => iprop(⌜args = [.i32 vec, .i32 p, .i32 (p + k)]⌝ ∗
          growPreS n g gt s vec ptr cap p idx ta (A 578) maxP hl live F w rest sb))
        (fun _ => 600 * cfg.regularOpCost + MemCpy.cost k.toNat * cfg.regularOpCost +
          cost154 cfg F cap (growCap cap (UInt32.ofNat w.length + k)))
        (fun _ rs => iprop(⌜rs = []⌝ ∗ growPostS n g gt s vec ptr cap (growCap cap (UInt32.ofNat w.length + k)) p
          idx ta (A 578) maxP hl live F w sb)) := by
  have hwl : (UInt32.ofNat w.length).toNat = w.length := by
    simp only [UInt32.toNat_ofNat']; omega
  iintro #Hk
  ihave #S735 := f735_re (GF := GF) cfg lim (d + 1) types[14]! rfl inst mi A n g ta hm (by omega) Cg gt s vec
    (UInt32.ofNat w.length) k ptr cap idx maxP hl live F (w ++ rest) hs hvec hptr hcap hcap2 (by omega)
    (by omega) (by omega) (by simp; omega) hlive hr $$ Hk
  ihave #Hi := sinkCodeR_inst n maxP inst mi A $$ Hk
  iunfold sinkCodeR, sinkCode at Hk
  icases Hk with ⟨⟨#Hv, -, -, -, -, -, #H735, -⟩, -⟩
  ihave #H951 : A 951 ↪[wf] FuncInst.wasm types[15]! inst f951 $$ []
  · iunfold vecCode2 at Hv
    icases Hv with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, #H, -⟩
    iexact H
  have hn := hm.mem
  have ha735 := hm.funcs 735 (by decide)
  have ha951 := hm.funcs 951 (by decide)
  have t14 : types[14]!.params.length = 2 := by rfl
  have t15 : types[15]!.params.length = 3 := by rfl
  have hc := growCap_toNat cap (UInt32.ofNat w.length + k) (by omega)
  have hwk : (UInt32.ofNat w.length + k).toNat = w.length + k.toNat := by
    rw [UInt32.toNat_add, hwl]; omega
  rw [hwk] at hc
  generalize hC : growCap cap (UInt32.ofNat w.length + k) = c at hc
  generalize hM : MemCpy.cost k.toNat * cfg.regularOpCost = M
  generalize hK : cost154 cfg F cap c = K
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, HP⟩
  subst hargs
  iunfold growPreS at HP
  icases HP with ⟨Hg, Hs, Hvt, Hinv, Hp, Hcap, Hlen, Hbs, Hsb⟩
  simp only [f734]
  repeat mstep
  rw [add_sub_left]
  mcall S735 using [Hg Hs Hvt Hinv Hp Hcap Hlen Hbs]
  · iunfold pre768g
    iframe Hg Hs Hvt Hinv Hp Hcap Hlen Hbs
  icases HQ with ⟨%hrs, HQ⟩
  subst hrs
  iunfold post768g at HQ
  icases HQ with ⟨%q, Hg, Hs, Hvt, Hp, Hcap, Hlen, HA⟩
  iunfold reallocated at HA
  icases HA with ⟨%⟨hq0, hqb⟩, HH, Hq, %junk, %hjunk, Hj⟩
  mcredits (40 * cfg.regularOpCost + M + R)
  icases splitB (a := q.toNat) (b := q.toNat + w.length) w rest rfl $$ Hq with ⟨Hw, Hr⟩
  ihave Hr := joinB (a := q.toNat + w.length) (b := q.toNat + cap.toNat) rest junk (by omega) $$ [Hr Hj]
  · iframe Hr Hj
  icases U128From.memBytes_split n (q.toNat + w.length) k.toNat (rest ++ junk) (by simp; omega) $$ Hr
    with ⟨Ho, Ht⟩
  have hql : (q + UInt32.ofNat w.length).toNat = q.toNat + w.length := by
    rw [UInt32.toNat_add, hwl]; omega
  have S951 : ⊢ MFunSpec (GF := GF) cfg lim (d + 1) types[15]! inst mi f951 Cg
      (MemCpy.pre n (q + UInt32.ofNat w.length) p k ((rest ++ junk).take k.toNat) sb) (fun _ => M)
      (MemCpy.post n (q + UInt32.ofNat w.length) p sb) := by
    rw [← hM]
    exact MemCpy.f951_spec cfg lim (d + 1) types[15]! (by rfl) inst mi n hn Cg (q + UInt32.ofNat w.length) p k
      ((rest ++ junk).take k.toNat) sb (by simp; omega) hsb (by omega) hp
  repeat mstep
  mstep [Hp]
  repeat mstep
  mstep [Hlen]
  repeat mstep
  ihave Ho := memBytes_addr (show q.toNat + w.length = (q + UInt32.ofNat w.length).toNat by omega) $$ Ho
  mcall S951 using [Ho Hsb]
  · iunfold MemCpy.pre
    iframe Ho Hsb
    ipureintro; rfl
  iunfold MemCpy.post at HQ
  icases HQ with ⟨%hrs, Ho, Hsb⟩
  subst hrs
  repeat mstep
  mstep [Hlen]
  repeat mstep
  mstep [Hlen]
  mcredits R
  iframe Hc
  isplitr
  · ipureintro; simp [htype]
  iunfold growPostS
  iexists q
  iframe Hg Hs Hvt Hp Hcap Hsb
  isplitl [Hlen]
  · iapply (show (n ↦[i32][ vec.toNat + 8 ] (UInt32.ofNat w.length + k) : IProp GF) ⊢
        n ↦[i32][ vec.toNat + 8 ] UInt32.ofNat (w ++ sb).length by
      rw [show UInt32.ofNat w.length + k = UInt32.ofNat (w ++ sb).length by
        apply UInt32.toNat_inj.mp; rw [UInt32.toNat_add, hwl]; simp only [UInt32.toNat_ofNat', List.length_append]
        omega]) $$ Hlen
  ihave Ho := memBytes_addr (show (q + UInt32.ofNat w.length).toNat = q.toNat + w.length by omega) $$ Ho
  isplitl [Hw Ho]
  · iapply joinB (a := q.toNat) (b := q.toNat + w.length) w sb rfl
    iframe Hw Ho
  isplitl [Ht]
  · iexists (rest ++ junk).drop k.toNat
    isplitr
    · ipureintro; simp; omega
    iapply memBytes_addr (show q.toNat + w.length + k.toNat = q.toNat + (w ++ sb).length by simp; omega) $$ Ht
  iunfold grownV
  iframe HH
  ipureintro; exact ⟨hq0, hqb⟩

/-- `extend_from_slice(vec, p, k)` (757) without room on a nonempty buffer. -/
theorem f757_re (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 15 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s vec ptr cap p k : UInt32) (idx : UInt32) (maxP hl : Nat)
    (live : List (Nat × Nat)) (F : Nat) (w rest sb : List UInt8) (hs : 112 ≤ s.toNat)
    (hvec : vec.toNat + 12 ≤ 2 ^ 32) (hptr : ptr ≠ 0) (hcap : 0 < cap.toNat) (hcap2 : cap.toNat < 2 ^ 27)
    (hwr : w.length + rest.length = cap.toNat) (hsb : sb.length = k.toNat)
    (hgrow : cap.toNat < w.length + k.toNat) (hlk : w.length + k.toNat < 2 ^ 28)
    (hp : p.toNat + k.toNat ≤ 2 ^ 32)
    (hlive : (ptr.toNat, cap.toNat) ∈ live) (hr : roomFor hl maxP (growCap cap (UInt32.ofNat w.length + k))) :
    sinkCodeR n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f757 Cg
        (fun args => iprop(⌜args = [.i32 vec, .i32 p, .i32 k]⌝ ∗
          growPreS n g gt s vec ptr cap p idx ta (A 578) maxP hl live F w rest sb))
        (fun _ => 620 * cfg.regularOpCost + MemCpy.cost k.toNat * cfg.regularOpCost +
          cost154 cfg F cap (growCap cap (UInt32.ofNat w.length + k)))
        (fun _ rs => iprop(⌜rs = []⌝ ∗ growPostS n g gt s vec ptr cap (growCap cap (UInt32.ofNat w.length + k)) p
          idx ta (A 578) maxP hl live F w sb)) := by
  iintro #Hk
  ihave #S734 := f734_re (GF := GF) cfg lim (d + 1) types[31]! (by rfl) inst mi A n g ta hm (by omega) Cg
    gt s vec ptr cap p k idx maxP hl live F w rest sb hs hvec hptr hcap hcap2 hwr hsb hgrow hlk hp hlive hr $$ Hk
  ihave #Hi := sinkCodeR_inst n maxP inst mi A $$ Hk
  iunfold sinkCodeR, sinkCode at Hk
  icases Hk with ⟨⟨-, -, -, -, -, -, -, #H734, -⟩, -⟩
  have ha734 := hm.funcs 734 (by decide)
  have t31 : types[31]!.params.length = 3 := by rfl
  generalize hM : MemCpy.cost k.toNat * cfg.regularOpCost = M
  generalize hK : cost154 cfg F cap (growCap cap (UInt32.ofNat w.length + k)) = K
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, HP⟩
  subst hargs
  simp only [f757]
  repeat mstep
  mcall S734 using [HP]
  · iframe HP
  icases HQ with ⟨%hrs, HQ⟩
  subst hrs
  mcredits R
  iframe Hc HQ
  ipureintro; simp [htype]

/-- The cost of 759 without room on a nonempty buffer. -/
def costGrowS (cfg : WasmConfig) (F : Nat) (cap c : UInt32) (k : Nat) : Nat :=
  640 * cfg.regularOpCost + MemCpy.cost k * cfg.regularOpCost + cost154 cfg F cap c

/-- **`<&mut String as fmt::Write>::write_str(dd, p, k)`** (759) without room on a nonempty
`String`: the block reallocated to `growCap cap (|w| + k)`, the copy; `Ok`. -/
theorem f759_re (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 16 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s dd vec ptr cap p k : UInt32) (idx : UInt32) (maxP hl : Nat)
    (live : List (Nat × Nat)) (F : Nat) (w rest sb : List UInt8) (hs : 112 ≤ s.toNat)
    (hdd : dd.toNat + 4 ≤ 2 ^ 32)
    (hvec : vec.toNat + 12 ≤ 2 ^ 32) (hptr : ptr ≠ 0) (hcap : 0 < cap.toNat) (hcap2 : cap.toNat < 2 ^ 27)
    (hwr : w.length + rest.length = cap.toNat) (hsb : sb.length = k.toNat)
    (hgrow : cap.toNat < w.length + k.toNat) (hlk : w.length + k.toNat < 2 ^ 28)
    (hp : p.toNat + k.toNat ≤ 2 ^ 32)
    (hlive : (ptr.toNat, cap.toNat) ∈ live) (hr : roomFor hl maxP (growCap cap (UInt32.ofNat w.length + k))) :
    sinkCodeR n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f759 Cg
        (fun args => iprop(⌜args = [.i32 dd, .i32 p, .i32 k]⌝ ∗ n ↦[i32][ dd.toNat ] vec ∗
          growPreS n g gt s vec ptr cap p idx ta (A 578) maxP hl live F w rest sb))
        (fun _ => costGrowS cfg F cap (growCap cap (UInt32.ofNat w.length + k)) k.toNat)
        (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ n ↦[i32][ dd.toNat ] vec ∗
          growPostS n g gt s vec ptr cap (growCap cap (UInt32.ofNat w.length + k)) p
            idx ta (A 578) maxP hl live F w sb)) := by
  iintro #Hk
  ihave #S757 := f757_re (GF := GF) cfg lim (d + 1) types[31]! (by rfl) inst mi A n g ta hm (by omega) Cg
    gt s vec ptr cap p k idx maxP hl live F w rest sb hs hvec hptr hcap hcap2 hwr hsb hgrow hlk hp hlive hr $$ Hk
  ihave #Hi := sinkCodeR_inst n maxP inst mi A $$ Hk
  iunfold sinkCodeR, sinkCode at Hk
  icases Hk with ⟨⟨-, -, -, -, -, -, -, -, #H757⟩, -⟩
  have hn := hm.mem
  have ha757 := hm.funcs 757 (by decide)
  have t31 : types[31]!.params.length = 3 := by rfl
  unfold costGrowS
  generalize hM : MemCpy.cost k.toNat * cfg.regularOpCost = M
  generalize hK : cost154 cfg F cap (growCap cap (UInt32.ofNat w.length + k)) = K
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hdd, HP⟩
  subst hargs
  simp only [f759]
  repeat mstep
  mstep [Hdd]
  repeat mstep
  mcall S757 using [HP]
  · iframe HP
  icases HQ with ⟨%hrs, HQ⟩
  subst hrs
  repeat mstep
  mcredits R
  iframe Hc Hdd HQ
  ipureintro
  match type, htype with
  | ⟨_, [_]⟩, _ => rfl

end Spec

end WNear.Binary.FmtSinkRe
