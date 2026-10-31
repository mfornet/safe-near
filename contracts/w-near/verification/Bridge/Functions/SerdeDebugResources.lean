import Bridge.Functions.PanicDebug
import Bridge.Functions.DropVec
import Bridge.Functions.PanicExpectError
import Bridge.Functions.FormatResult
import Bridge.Functions.FmtWriteN
import Binary.Code.Part19
namespace WNear.Binary.SerdeDebug
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_addr stk_intro stk_word)
open WNear.Binary.PanicHook (stk4_word)
variable {GF : BundledGFunctors} [WasmGS NearState GF]

def args24 (n : Nat) (a : UInt32) (a0 a8 a16 : UInt64) : IProp GF :=
  iprop(n ↦[wms][ a.toNat ] (storeBytes (.i64 a0) 8) ∗ n ↦[wms][ a.toNat + 8 ] (storeBytes (.i64 a8) 8) ∗ n ↦[wms][ a.toNat + 16 ] (storeBytes (.i64 a16) 8))

/-- The owned three-word String record used by the actual Debug formatter. -/
def stringCells (n : Nat) (s ptr cap len : UInt32) : IProp GF :=
  iprop(n ↦[i32][ s.toNat ] ptr ∗ n ↦[i32][ s.toNat + 4 ] cap ∗ n ↦[i32][ s.toNat + 8 ] len)

/-- Exact ErrorCode Debug argument: a pointer to the error box and its deployed formatter tag. -/
def firstErrorArg (n : Nat) (s e : UInt32) : IProp GF :=
  iprop(n ↦[i32][ s.toNat + 16 ] (s + 52) ∗ n ↦[i32][ s.toNat + 20 ] 126 ∗
    n ↦[i32][ s.toNat + 52 ] e)

/-- Exact first Arguments record; the unused word at offset 12 remains arbitrary and owned. -/
def firstErrorArgs (n : Nat) (s pad : UInt32) : IProp GF :=
  args24 n (s + 56) (VecFromElem.pair64 1057628 1) (VecFromElem.pair64 0 pad) (VecFromElem.pair64 (s + 16) 1)

def debugFrame (inst : Nat) (mi : ModuleInst) (err fmt sp : UInt32) (x3 : UInt64) : Frame :=
  ⟨#[.i32 err, .i32 fmt, .i32 sp, .i64 x3], inst, mi⟩

/-- Exact outer Debug Arguments: four static pieces and three formatting arguments. -/
def secondErrorArgs (n : Nat) (s pad : UInt32) : IProp GF :=
  args24 n (s + 16) (VecFromElem.pair64 1061532 4) (VecFromElem.pair64 0 pad) (VecFromElem.pair64 (s + 56) 3)

/-- String, line and column descriptors written by the actual serde error Debug implementation. -/
def secondErrorValues (n : Nat) (s e : UInt32) : IProp GF :=
  args24 n (s + 56) (VecFromElem.pair64 (s + 40) 127) (VecFromElem.pair64 (e + 12) 3)
    (VecFromElem.pair64 (e + 16) 3)

/-- Owned temporary allocation that actual String drop may consume. -/
def stringHeap (n maxP len : Nat) (live : List (Nat × Nat)) (F : Nat) (p c : UInt32) : IProp GF :=
  iprop(AllocInv.heapInv n maxP len live F ∗
    (if c = 0 then emp else ⌜(p.toNat, c.toNat) ∈ live⌝ ∗ AllocInv.block n p.toNat c.toNat))

def stringHeapFreed (n maxP len : Nat) (live : List (Nat × Nat)) (F : Nat) (p c : UInt32) : IProp GF :=
  AllocInv.heapInv n maxP len (if c = 0 then live else live.erase (p.toNat, c.toNat)) (if c = 0 then F else F + 1)

/-- Exact remaining formatting engine called by the String adapter. Dispatch/setup correctness does not prove it. -/
def StringFmtEngineSpec (cfg : WasmConfig) (lim : ExecLimits) (d inst : Nat) (mi : ModuleInst)
    (n g : Nat) (gt : GlobalType) (sp self : UInt32) (a0 a8 a16 : UInt64) (ret : UInt32)
    (Kw Cg : Nat) (P Q : IProp GF) : IProp GF :=
  MFunSpec cfg lim d types[15]! inst mi f872 Cg
        (fun args => iprop(⌜args = [.i32 (sp - 32 + 4), .i32 1057784, .i32 (sp - 32 + 8)]⌝ ∗
          g ↦[wg] ⟨gt, .i32 (sp - 32)⟩ ∗ n ↦[i32][ (sp - 32).toNat + 4 ] self ∗
          args24 n (sp - 32 + 8) a0 a8 a16 ∗ P)) (fun _ => Kw)
        (fun _ rs => iprop(⌜rs = [.i32 ret]⌝ ∗ g ↦[wg] ⟨gt, .i32 (sp - 32)⟩ ∗
          n ↦[i32][ (sp - 32).toNat + 4 ] self ∗ args24 n (sp - 32 + 8) a0 a8 a16 ∗ Q))

/-- Exact remaining formatting engine called by the Formatter adapter. -/
def FormatterFmtEngineSpec (cfg : WasmConfig) (lim : ExecLimits) (d inst : Nat) (mi : ModuleInst)
    (n g : Nat) (gt : GlobalType) (sp data vtab : UInt32) (a0 a8 a16 : UInt64) (ret : UInt32)
    (Kw Cg : Nat) (P Q : IProp GF) : IProp GF :=
  MFunSpec cfg lim d types[15]! inst mi f872 Cg
        (fun args => iprop(⌜args = [.i32 data, .i32 vtab, .i32 (sp - 32 + 8)]⌝ ∗
          g ↦[wg] ⟨gt, .i32 (sp - 32)⟩ ∗
          args24 n (sp - 32 + 8) a0 a8 a16 ∗ P)) (fun _ => Kw)
        (fun _ rs => iprop(⌜rs = [.i32 ret]⌝ ∗ g ↦[wg] ⟨gt, .i32 (sp - 32)⟩ ∗
          args24 n (sp - 32 + 8) a0 a8 a16 ∗ Q))

/-- Exact ErrorCode-to-String writer family, preserving arbitrary padding and returning owned allocation choices. -/
def ErrorCodeStringWriteSpec (cfg : WasmConfig) (lim : ExecLimits) (d inst : Nat) (mi : ModuleInst)
    (n g : Nat) (gt : GlobalType) (sp e : UInt32) (S K Cg : Nat)
    (P : IProp GF) (Q : UInt32 → UInt32 → UInt32 → IProp GF) : IProp GF :=
  iprop(∀ pad : UInt32, MFunSpec cfg lim d types[13]! inst mi f598 Cg
        (fun args => iprop(⌜args = [.i32 (sp - 80 + 40), .i32 (sp - 80 + 56)]⌝ ∗
          g ↦[wg] ⟨gt, .i32 (sp - 80)⟩ ∗ stk n ((sp - 80).toNat - S) S ∗
          stringCells n (sp - 80 + 40) 1 0 0 ∗ firstErrorArg n (sp - 80) e ∗
          firstErrorArgs n (sp - 80) pad ∗ P)) (fun _ => K)
        (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 (sp - 80)⟩ ∗
          stk n ((sp - 80).toNat - S) S ∗
          ∃ p c l : UInt32, stringCells n (sp - 80 + 40) p c l ∗
          firstErrorArg n (sp - 80) e ∗ firstErrorArgs n (sp - 80) pad ∗ Q p c l)))

/-- Exact three-argument outer error writer. It remains unresolved until its actual selected writers are proved. -/
def ErrorEnvelopeWriteSpec (cfg : WasmConfig) (lim : ExecLimits) (d inst : Nat) (mi : ModuleInst)
    (n g : Nat) (gt : GlobalType) (s fmt e p c l ret : UInt32) (S K Cg : Nat) (P Q : IProp GF) : IProp GF :=
  iprop(∀ pad : UInt32, MFunSpec cfg lim d types[13]! inst mi f913 Cg
        (fun args => iprop(⌜args = [.i32 fmt, .i32 (s + 16)]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - S) S ∗ stringCells n (s + 40) p c l ∗
          secondErrorArgs n s pad ∗ secondErrorValues n s e ∗ P)) (fun _ => K)
        (fun _ rs => iprop(⌜rs = [.i32 ret]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - S) S ∗ stringCells n (s + 40) p c l ∗
          secondErrorArgs n s pad ∗ secondErrorValues n s e ∗ Q)))

/-- A full rejected receipt needs one finite formatter cost chosen before every gas ceiling.
A local per-ceiling operational composition does not supply this witness. -/
def UniformSerdeDebugSpec (cfg : WasmConfig) (lim : ExecLimits) (d inst : Nat) (mi : ModuleInst)
    (desc fmt : UInt32) (Cd P Q : IProp GF) : Prop :=
  ∃ K : Nat, ∀ Cg : Nat, ⊢ (Cd -∗ PanicDebug.SerdeErrorDebugSpec cfg lim d inst mi desc fmt K Cg P Q)

instance errorCodeStringWriteSpec_persistent (cfg : WasmConfig) (lim : ExecLimits) (d inst : Nat) (mi : ModuleInst)
    (n g : Nat) (gt : GlobalType) (sp e : UInt32) (S K Cg : Nat)
    (P : IProp GF) (Q : UInt32 → UInt32 → UInt32 → IProp GF) :
    Persistent (ErrorCodeStringWriteSpec cfg lim d inst mi n g gt sp e S K Cg P Q) := by
  unfold ErrorCodeStringWriteSpec
  infer_instance

instance errorEnvelopeWriteSpec_persistent (cfg : WasmConfig) (lim : ExecLimits) (d inst : Nat) (mi : ModuleInst)
    (n g : Nat) (gt : GlobalType) (s fmt e p c l ret : UInt32) (S K Cg : Nat) (P Q : IProp GF) :
    Persistent (ErrorEnvelopeWriteSpec cfg lim d inst mi n g gt s fmt e p c l ret S K Cg P Q) := by
  unfold ErrorEnvelopeWriteSpec
  infer_instance

/-- Reclaim the complete copied Arguments record as its original 24-byte stack region. -/
theorem args24_stack (n : Nat) (a : UInt32) (a0 a8 a16 : UInt64) :
    args24 (GF := GF) n a a0 a8 a16 ⊢ stk n a.toNat 24 := by
  iintro H
  iunfold args24 at H
  icases H with ⟨W0, W8, W16⟩
  ihave W0 := stk_intro n a.toNat (storeBytes (.i64 a0) 8) $$ W0
  ihave W8 := stk_intro n (a.toNat + 8) (storeBytes (.i64 a8) 8) $$ W8
  ihave W16 := stk_intro n (a.toNat + 16) (storeBytes (.i64 a16) 8) $$ W16
  have hb (v : UInt64) : (storeBytes (.i64 v) 8).length = 8 := by simp [storeBytes, storeRaw]
  simp only [hb]
  ihave H := stk_join n a.toNat 8 8 $$ [W0 W8]
  · iframe W0 W8
  iapply stk_join n a.toNat 16 8
  iframe H W16

theorem stringCells_stack (n : Nat) (s p c l : UInt32) :
    stringCells (GF := GF) n s p c l ⊢ stk n s.toNat 12 := by
  iintro H
  iunfold stringCells at H
  icases H with ⟨P, C, L⟩
  ihave P := stk_word n s.toNat p $$ P
  ihave C := stk_word n (s.toNat + 4) c $$ C
  ihave L := stk_word n (s.toNat + 8) l $$ L
  ihave H := stk_join n s.toNat 4 4 $$ [P C]
  · iframe P C
  iapply stk_join n s.toNat 8 4
  iframe H L

end WNear.Binary.SerdeDebug
