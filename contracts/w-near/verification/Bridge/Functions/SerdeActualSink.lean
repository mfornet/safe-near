import Bridge.Functions.SerdeErrorWriters
import Bridge.Functions.ScratchGrow
namespace WNear.Binary.SerdeActualSink
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.Interface WNear.Binary.SerdeErrorWriters
variable {GF : BundledGFunctors} [WasmGS NearState GF]
set_option maxRecDepth 100000

theorem serde_string_sink_vtable : dataWord (1057784 + 12) = bytes32 130 := by
  rw [dataWord_eq _ (by decide)]
  decide +kernel

theorem serde_string_sink_table : wTable.elems[130]? = some (Ref.func 616) := rfl

/-- The actual String writer owns its descriptor, record, source bytes, stack and allocator state. -/
def stringState (n g ta : Nat) (gt : GlobalType) (s dd vec ptr cap idx : UInt32)
    (a578 maxP hl F : Nat) (live : List (Nat × Nat)) (bs : List UInt8) : IProp GF :=
  iprop(n ↦[i32][ dd.toNat ] vec ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
    VecFromElem.stk n (s.toNat - 112) 112 ∗ AllocFirstFit.vt n 1057464 idx ta a578 ∗
    n ↦[i32][ vec.toNat ] ptr ∗ n ↦[i32][ vec.toNat + 4 ] cap ∗
    n ↦[i32][ vec.toNat + 8 ] UInt32.ofNat bs.length ∗ ScratchGrow.sbuf n maxP hl live F ptr cap bs)

set_option maxHeartbeats 8000000 in
/-- The actual serde String sink appends the given bytes, including allocation and reallocation. -/
theorem f616_append (cfg : WasmConfig) (lim : ExecLimits) (d inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta)
    (hd : d + 16 < lim.maxCallDepth) (Cg : Nat) (gt : GlobalType)
    (s dd vec ptr cap src k idx : UInt32) (maxP hl F : Nat) (live : List (Nat × Nat))
    (bs sb : List UInt8) (hs : 112 ≤ s.toNat) (hdd : dd.toNat + 4 ≤ 2 ^ 32)
    (hvec : vec.toNat + 12 ≤ 2 ^ 32) (hcap : cap.toNat < 2 ^ 27)
    (hlk : bs.length + k.toNat < 2 ^ 27) (hsb : sb.length = k.toNat)
    (hsrc : src.toNat + k.toNat ≤ 2 ^ 32)
    (hr : ScratchGrow.roomRes hl maxP cap (UInt32.ofNat bs.length) k) :
    inst ↪[inst] mi ∗ ScratchGrow.sgCode n maxP inst mi A ⊢
      MFunSpec (GF := GF) cfg lim d types[15]! inst mi f616 Cg
        (fun args => iprop(⌜args = [.i32 dd, .i32 src, .i32 k]⌝ ∗
          stringState n g ta gt s dd vec ptr cap idx (A 578) maxP hl F live bs ∗
          n ↦[wms][ src.toNat ] sb))
        (fun _ => 36 * cfg.regularOpCost + ScratchGrow.costExt cfg F cap (UInt32.ofNat bs.length) k)
        (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ ∃ (p : UInt32) (hl' : Nat),
          ⌜ScratchGrow.hlAfter hl hl' cap (UInt32.ofNat bs.length) k⌝ ∗
          stringState n g ta gt s dd vec p (ScratchGrow.capAfter cap (UInt32.ofNat bs.length) k) idx
            (A 578) maxP hl' (ScratchGrow.fAfter F cap (UInt32.ofNat bs.length) k) live (bs ++ sb) ∗
          n ↦[wms][ src.toNat ] sb)) := by
  iintro ⟨#Hi, #Hk⟩
  ihave #H613 : A 613 ↪[wf] FuncInst.wasm types[31]! inst f613 $$ [Hk]
  · iunfold ScratchGrow.sgCode at Hk
    icases Hk with ⟨-, -, -, -, -, -, -, -, -, #H613, -⟩
    iexact H613
  have hn := hm.mem
  have ha613 := hm.funcs 613 (by decide)
  have t31 : types[31]!.params.length = 3 := rfl
  have key := ScratchGrow.f613_spec (GF := GF) cfg lim (d + 1) types[31]! rfl inst mi A n g ta hm
    (by omega) Cg gt s vec src k ptr cap idx maxP hl live F bs sb hs hvec hcap hlk hsb hsrc hr
  generalize hK : ScratchGrow.costExt cfg F cap (UInt32.ofNat bs.length) k = K at key ⊢
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, HS, Hsrc⟩
  iunfold stringState at HS
  icases HS with ⟨DD, Hg, Hs, Hvt, V0, V4, V8, Hbuf⟩
  subst hargs
  simp only [f616]
  mstep
  mstep [DD]
  repeat mstep
  mcall key using [Hg Hs Hvt V0 V4 V8 Hbuf Hsrc]
  · iframe Hg Hs Hvt V0 V4 V8 Hbuf Hsrc
  clear key
  icases HQ with ⟨%hrs, %p, %hl', %hhl, Hg, Hs, Hvt, V0, V4, V8, Hbuf, Hsrc⟩
  subst hrs
  repeat mstep
  mcredits R
  simp [Post.mfunc]
  isplitl [Hc]
  · iexact Hc
  isplitr
  · ipureintro; rfl
  iexists p, hl'
  isplitr
  · ipureintro; exact hhl
  iunfold stringState
  have hlen : UInt32.ofNat (bs.length + k.toNat) = UInt32.ofNat bs.length + k := by simp
  simp only [List.length_append, hsb, hlen]
  iframe DD Hg Hs Hvt V0 V4 V8 Hbuf Hsrc

set_option maxHeartbeats 8000000 in
/-- Static ErrorCode formatting reaches the actual serde String sink with no writer-contract premise. -/
theorem f591_syntax_append (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 19 < lim.maxCallDepth) (Cg : Nat) (gt : GlobalType)
    (desc e fmt tag s dd vec ptr cap idx : UInt32) (maxP hl F : Nat)
    (live : List (Nat × Nat)) (bs sb : List UInt8)
    (hdesc : desc.toNat + 4 ≤ 2 ^ 32) (he : e.toNat + 4 ≤ 2 ^ 32)
    (hlow : 2 ≤ tag.toNat) (hhigh : tag.toNat ≤ 21) (hf : fmt.toNat + 32 ≤ 2 ^ 32)
    (hs : 112 ≤ s.toNat) (hsb : sb.length = (syntaxSlice tag).2.toNat)
    (hdd : dd.toNat + 4 ≤ 2 ^ 32) (hvec : vec.toNat + 12 ≤ 2 ^ 32)
    (hcap : cap.toNat < 2 ^ 27) (hlk : bs.length + (syntaxSlice tag).2.toNat < 2 ^ 27)
    (hsrc : (syntaxSlice tag).1.toNat + (syntaxSlice tag).2.toNat ≤ 2 ^ 32)
    (hr : ScratchGrow.roomRes hl maxP cap (UInt32.ofNat bs.length) (syntaxSlice tag).2) :
    inst ↪[inst] mi ∗ A 592 ↪[wf] FuncInst.wasm types[13]! inst f592 ∗
      A 912 ↪[wf] FuncInst.wasm types[15]! inst f912 ∗
      A 616 ↪[wf] FuncInst.wasm types[15]! inst f616 ∗ ScratchGrow.sgCode n maxP inst mi A ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f591 Cg
        (fun args => iprop(⌜args = [.i32 desc, .i32 fmt]⌝ ∗
          n ↦[i32][ desc.toNat ] e ∗ n ↦[i32][ e.toNat ] tag ∗
          n ↦[i32][ fmt.toNat + 24 ] dd ∗ n ↦[i32][ fmt.toNat + 28 ] 1057784 ∗
          n ↦[i32][ 1057796 ] 130 ∗ ta ↦[wt][ 130 ] Ref.func (A 616) ∗
          stringState n g ta gt s dd vec ptr cap idx (A 578) maxP hl F live bs ∗
          n ↦[wms][ (syntaxSlice tag).1.toNat ] sb))
        (fun _ => 133 * cfg.regularOpCost + activationGas cfg.regularOpCost
          (entryLocals f616 [.i32 dd, .i32 (syntaxSlice tag).1, .i32 (syntaxSlice tag).2]) +
          (36 * cfg.regularOpCost + ScratchGrow.costExt cfg F cap (UInt32.ofNat bs.length) (syntaxSlice tag).2))
        (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗
          n ↦[i32][ desc.toNat ] e ∗ n ↦[i32][ e.toNat ] tag ∗
          n ↦[i32][ fmt.toNat + 24 ] dd ∗ n ↦[i32][ fmt.toNat + 28 ] 1057784 ∗
          n ↦[i32][ 1057796 ] 130 ∗ ta ↦[wt][ 130 ] Ref.func (A 616) ∗
          ∃ (p : UInt32) (hl' : Nat),
          ⌜ScratchGrow.hlAfter hl hl' cap (UInt32.ofNat bs.length) (syntaxSlice tag).2⌝ ∗
          stringState n g ta gt s dd vec p (ScratchGrow.capAfter cap (UInt32.ofNat bs.length) (syntaxSlice tag).2) idx
            (A 578) maxP hl' (ScratchGrow.fAfter F cap (UInt32.ofNat bs.length) (syntaxSlice tag).2) live (bs ++ sb) ∗
          n ↦[wms][ (syntaxSlice tag).1.toNat ] sb)) := by
  iintro ⟨#Hi, #F592, #F912, #F616, #Hk⟩
  ihave HS := f616_append (GF := GF) cfg lim (d + 3) inst mi A n g ta hm (by omega) Cg gt
    s dd vec ptr cap (syntaxSlice tag).1 (syntaxSlice tag).2 idx maxP hl F live bs sb
    hs hdd hvec hcap hlk hsb hsrc hr $$ [Hi Hk]
  · iframe Hi Hk
  have H := f591_syntax_sink (GF := GF) cfg lim d type htype inst mi A n g ta hm (by omega) Cg
    desc e fmt tag dd 1057784 130 (A 616) f616
    (36 * cfg.regularOpCost + ScratchGrow.costExt cfg F cap (UInt32.ofNat bs.length) (syntaxSlice tag).2)
    iprop(stringState n g ta gt s dd vec ptr cap idx (A 578) maxP hl F live bs ∗
      n ↦[wms][ (syntaxSlice tag).1.toNat ] sb)
    iprop(∃ (p : UInt32) (hl' : Nat),
      ⌜ScratchGrow.hlAfter hl hl' cap (UInt32.ofNat bs.length) (syntaxSlice tag).2⌝ ∗
      stringState n g ta gt s dd vec p (ScratchGrow.capAfter cap (UInt32.ofNat bs.length) (syntaxSlice tag).2) idx
        (A 578) maxP hl' (ScratchGrow.fAfter F cap (UInt32.ofNat bs.length) (syntaxSlice tag).2) live (bs ++ sb) ∗
      n ↦[wms][ (syntaxSlice tag).1.toNat ] sb)
    hdesc he hlow hhigh hf (by decide)
  have hv : (1057784 : UInt32).toNat + 12 = 1057796 := rfl
  have hi : (130 : UInt32).toNat = 130 := rfl
  simp only [hv, hi] at H
  iapply H
  iunfold WriteSliceCalleeSpec
  iframe Hi F592 F912 F616 HS
end WNear.Binary.SerdeActualSink
