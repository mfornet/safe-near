import Bridge.Functions.SerdeIgnMachineTrace
import Bridge.Functions.SerdeIgnStack

/-!
# Saving the pending local frame through the actual vector call

In value mode the pure stack's head is still in function 81's local. Opening
another container calls 84 to save that head. At the top level its optional
flag is zero, so the actual vector and allocator are unchanged.
-/

namespace WNear.Binary.SerdeIgnMachineStack

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.IgnoreModel
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.VecFromElem (stk)

/-- Only value mode keeps a pending frame outside the physical vector. -/
def physical : Mode → List UInt8 → List UInt8
  | .val, frames => frames.tail
  | .opened _, frames => frames
  | .cont _, frames => frames

theorem physical_length (mode : Mode) (frames : List UInt8) :
    (physical mode frames).length = SerdeIgnMachineTrace.depth mode frames := by
  cases mode <;> simp [physical, SerdeIgnMachineTrace.depth]

/-- The optional flag sent by 81 to 84. -/
def flag : List UInt8 → UInt32
  | [] => 0
  | _ :: _ => 1

/-- The byte local is irrelevant when the optional flag is zero. -/
def current (fallback : UInt32) : List UInt8 → UInt32
  | [] => fallback
  | f :: _ => f.toUInt32

def saveCap (cap : UInt32) : List UInt8 → UInt32
  | [] => cap
  | _ :: frames => ScratchGrow.capAfter cap (UInt32.ofNat frames.length) 1

def saveF (F : Nat) (cap : UInt32) : List UInt8 → Nat
  | [] => F
  | _ :: frames => ScratchGrow.fAfter F cap (UInt32.ofNat frames.length) 1

def saveHL (hl hl' : Nat) (cap : UInt32) : List UInt8 → Prop
  | [] => hl' = hl
  | _ :: frames => ScratchGrow.hlAfter hl hl' cap (UInt32.ofNat frames.length) 1

def saveCost (cfg : WasmConfig) (F : Nat) (cap : UInt32) : List UInt8 → Nat
  | [] => 120 * cfg.regularOpCost
  | _ :: frames => SerdeIgnPush.cost cfg F cap frames.length

/-- The actual call that moves the pending local frame into the vector on a nested opening. -/
theorem f84_save {GF : BundledGFunctors} [WasmGS NearState GF]
    (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType) (htype : type.results = [])
    (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta)
    (hd : d + 13 < lim.maxCallDepth) (Cg : Nat) (gt : GlobalType) (s vec p cap idx fallback : UInt32)
    (maxP hl F : Nat) (live : List (Nat × Nat)) (frames : List UInt8) (opened : UInt8)
    (hs : 80 ≤ s.toNat) (hvec : vec.toNat + 12 ≤ 2 ^ 32) (hcap : cap.toNat < 2 ^ 27)
    (hlen : (physical .val frames).length + 1 < 2 ^ 27)
    (hr : frames ≠ [] → ScratchGrow.roomRes hl maxP cap (UInt32.ofNat (physical .val frames).length) 1) :
    SerdeIgnReserve.code n maxP inst mi A ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f84 Cg
      (fun args => iprop(⌜args = [.i32 vec, .i32 (flag frames), .i32 (current fallback frames)]⌝ ∗
        g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 80) 80 ∗ AllocFirstFit.vt n 1057464 idx ta (A 578) ∗
        SerdeIgnStack.state n maxP hl live F vec p cap (physical .val frames)))
      (fun _ => saveCost cfg F cap frames)
      (fun _ rs => iprop(⌜rs = []⌝ ∗ ∃ (p' : UInt32) (hl' : Nat), ⌜saveHL hl hl' cap frames⌝ ∗
        g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 80) 80 ∗ AllocFirstFit.vt n 1057464 idx ta (A 578) ∗
        SerdeIgnStack.state n maxP hl' live (saveF F cap frames) vec p' (saveCap cap frames)
          (physical (.opened opened) frames))) := by
  cases frames with
  | nil =>
    have base := SerdeIgnStack.f84_none (GF := GF) cfg lim d type htype inst mi A n g ta hm (by omega) Cg gt
      s vec p cap idx fallback maxP hl F live [] hs hvec
    iintro #HC
    ihave #S := base $$ HC
    clear base
    iunfold MFunSpec at S
    iunfold MFunSpec
    imodintro
    iintro %args %R HP Hc
    dsimp only [saveCost]
    iapply mwpInvoke_wand
    isplitl [HP Hc]
    · iapply S $$ %args %R [HP] Hc
      simp only [flag, current, physical, List.tail_nil]
      iexact HP
    isplit
    · iintro %rs ⟨Hc, %hrs, Hg, H80, Hvt, H⟩
      dsimp only
      iframe Hc
      isplitr
      · ipureintro; exact hrs
      iexists p, hl
      simp only [saveF, saveCap, physical]
      iframe Hg H80 Hvt H
      ipureintro; rfl
    · iintro Htrap; iexact Htrap
  | cons f frames =>
    simpa only [flag, current, saveCost, saveCap, saveF, saveHL, physical, List.tail_cons] using
      (SerdeIgnStack.f84_cons (GF := GF) cfg lim d type htype inst mi A n g ta hm hd Cg gt s vec p cap idx f
        maxP hl F live frames hs hvec hcap (by simpa only [physical, List.tail_cons] using hlen)
        (hr (by simp)))

/-- Scalar completion uses the pending local head without changing the vector. -/
theorem scalar_physical (f : UInt8) (frames : List UInt8) :
    physical .val (f :: frames) = physical (.cont f) frames := rfl

/-- After a saved-frame pop, the pure continuation's physical state is the remaining tail. -/
theorem popped_physical (frames : List UInt8) :
    (SerdeIgnStack.popped frames).2.2 =
      physical (.cont (SerdeIgnStack.popped frames).2.1) frames.tail := by
  cases frames <;> rfl

/-- Actual allocator-bound updates coincide with those charged by the traced push. -/
theorem saveF_trace (F : Nat) (cap : UInt32) (f : UInt8) (frames : List UInt8) :
    saveF F cap (f :: frames) =
      if SerdeIgnTrace.grows cap frames.length true then F + 2 else F := by
  by_cases h : ScratchGrow.fits cap (UInt32.ofNat frames.length) 1 <;>
    simp only [saveF, ScratchGrow.fAfter, SerdeIgnTrace.grows, Bool.true_and, h,
      not_true_eq_false, not_false_eq_true, decide_true, decide_false, Bool.false_eq_true, ite_true, ite_false]

/-- Exactly the operation prefix emitted by `SerdeIgnMachineTrace.save`. -/
def saveOps (frames : List UInt8) (ops : List SerdeIgnTrace.Op) : List SerdeIgnTrace.Op :=
  match frames with
  | [] => ops
  | _ :: _ => true :: ops

def saveExtra (cfg : WasmConfig) (F : Nat) (cap : UInt32) : List UInt8 → Nat
  | [] => 0
  | _ :: frames => SerdeIgnReserve.growthCost cfg F cap (UInt32.ofNat frames.length) 1

/-- The growth credits split at the actual save call with its returned coordinates and free-list bound. -/
theorem save_extraCost (cfg : WasmConfig) (F : Nat) (cap : UInt32) (frames : List UInt8)
    (ops : List SerdeIgnTrace.Op) :
    SerdeIgnTrace.extraCost cfg F cap (physical .val frames).length (saveOps frames ops) =
      saveExtra cfg F cap frames + SerdeIgnTrace.extraCost cfg (saveF F cap frames) (saveCap cap frames)
        frames.length ops := by
  cases frames with
  | nil => simp only [physical, List.tail_nil, List.length_nil, saveOps, saveExtra, saveF, saveCap, Nat.zero_add]
  | cons f frames =>
    simp only [saveOps, saveExtra, physical, List.tail_cons, SerdeIgnTrace.extraCost,
      SerdeIgnTrace.nextCap, SerdeIgnTrace.nextLen, ite_true, saveCap, List.length_cons, saveF_trace]

/-- The fixed part of either optional save fits 140 regular operations. -/
theorem saveCost_le (cfg : WasmConfig) (F : Nat) (cap : UInt32) (frames : List UInt8) :
    saveCost cfg F cap frames ≤ 140 * cfg.regularOpCost + saveExtra cfg F cap frames := by
  cases frames <;> simp only [saveCost, saveExtra, SerdeIgnPush.cost] <;> omega

/-- Restoring a saved frame preserves capacity and the allocator walk bound in the remaining budget. -/
theorem pop_extraCost (cfg : WasmConfig) (F : Nat) (cap : UInt32) (f : UInt8) (frames : List UInt8)
    (ops : List SerdeIgnTrace.Op) :
    SerdeIgnTrace.extraCost cfg F cap (f :: frames).length (false :: ops) =
      SerdeIgnTrace.extraCost cfg F cap frames.length ops := by
  simp only [SerdeIgnTrace.extraCost, SerdeIgnTrace.grows, SerdeIgnTrace.nextCap,
    SerdeIgnTrace.nextLen, Bool.false_and, Bool.false_eq_true, ite_false, List.length_cons,
    Nat.add_sub_cancel, Nat.zero_add]

end WNear.Binary.SerdeIgnMachineStack
