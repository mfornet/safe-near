import CodeLib.Attrs
import CodeLib.Basic
import CodeLib.Entry
import CodeLib.Equivalence
import CodeLib.List
import CodeLib.UInt32
import CodeLib.UInt64
import CodeLib.WordCodec
import CodeLib.WordCodec.UInt32
import CodeLib.RustStd.Frame
import CodeLib.RustStd.Region
import CodeLib.RustStd.MemArray
import CodeLib.RustStd.MemArray.SmallStep
import CodeLib.RustStd.MemFillLoop
import CodeLib.RustStd.MemCopyLoop
import CodeLib.RustStd.UInt
import CodeLib.RustStd.Option
import CodeLib.RustStd.U64.Basic
import CodeLib.RustStd.U64.AbsDiff
import CodeLib.RustStd.U64.Add
import CodeLib.RustStd.U64.Sub
import CodeLib.RustStd.U64.Mul
import CodeLib.RustStd.U64.Div
import CodeLib.RustStd.U64.Rem
import CodeLib.RustStd.U64.BitAnd
import CodeLib.RustStd.U64.BitOr
import CodeLib.RustStd.U64.BitXor
import CodeLib.RustStd.U64.Not
import CodeLib.RustStd.U64.Shl
import CodeLib.RustStd.U64.Shr
import CodeLib.RustStd.Array.Basic
import CodeLib.RustStd.Array.Len
import CodeLib.RustStd.Array.IsEmpty
import CodeLib.RustStd.Array.SmallStep
import CodeLib.RustStd.Vec.Basic
import CodeLib.RustStd.Vec.Codec
import CodeLib.RustStd.Borsh
import CodeLib.Near.State
import CodeLib.Near.Env
import CodeLib.Near.Proof
import CodeLib.SepLogic.WasmHeap
import CodeLib.SepLogic.WasmRules
import CodeLib.SepLogic.SmallStepLanguage
import CodeLib.SepLogic.SmallStepState
import CodeLib.SepLogic.SmallStepLifting
import CodeLib.SepLogic.SmallStepTotalLifting
import CodeLib.SepLogic.SmallStepOutcomeLanguage
import CodeLib.SepLogic.SmallStepOutcomeLifting
import CodeLib.SepLogic.SmallStepOutcomeExample
import CodeLib.SepLogic.SmallStepAdequacy
import CodeLib.SepLogic.SmallStepAdequacyExamples
import CodeLib.Host.UniversalStdIO
import CodeLib.SepLogic.SmallStepOutcomeAdequacy
import CodeLib.Examples.MergeSort.TotalProof
import CodeLib.Examples.Quicksort.TotalProof
import CodeLib.Examples.SelectionSort.StdIOProof
import CodeLib.Examples.MergeSort.Adequacy
import CodeLib.SepLogic.HostCallExample
import CodeLib.SepLogic.TwoModuleExample
import CodeLib.SepLogic.CrossInstanceExample
import CodeLib.SepLogic.CounterHostExample
import CodeLib.SepLogic.ImportChainExample
import CodeLib.SepLogic.SharedMemoryExample

/-!
# CodeLib — convenience umbrella for proof development

This wide import includes the separation-logic framework, Rust library
lemmas, and worked proof examples. Generated `Program.lean` files import
`CodeLib.Generated`, which provides AST tooling without this proof surface.
Specifications and proofs may import this umbrella for convenience, or name
their required supporting modules explicitly. The upstream Talos verifier and
extractor are not part of this repository.
-/
