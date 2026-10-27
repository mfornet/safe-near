import Proofs.PanicHookState
import Proofs.PanicAllocatePointerNative

/-! The panic setup's computed-memory conditions follow from original static words. -/
namespace WNear.Proofs.PanicHookNative
open Wasm Wasm.Near MeteredLogic PanicHookState
set_option maxRecDepth 16384

/-- A stack below the panic globals preserves all three initial guard words.
Every hypothesis concerns the original store or original memory. -/
theorem ready (s : Store NearState) (limits : ExecLimits) (inst : Nat)
    (callers : List CallFrame) (p : Layout)
    (hr : PanicAllocatePointerState.Ready s limits (pointerFrame inst 0) callers p)
    (hai : p.mi.funcAddrs[503]? = some 503)
    (ha : s.funcs[503]? = some (.wasm WNear.Binary.PanicAllocate.signature503 inst WNear.Binary.PanicAllocate.function503))
    (hhi : p.mi.funcAddrs[822]? = some 822)
    (hh : s.funcs[822]? = some (.wasm WNear.Binary.PanicHookSet.signature inst WNear.Binary.PanicHookSet.function))
    (hstack : p.sp.toNat ≤ 1074920) (hspan : 1074936 ≤ p.memory.byteSize)
    (hinit : readI32 p.memory 1074932 = 0)
    (hlock : readI32 p.memory 1074920 = 0)
    (hold : readI32 p.memory 1074928 = 0) :
    Ready s limits inst callers.length p := by
  have final := PanicAllocatePointerNative.final_spec p hr.wf hr.width hr.spLower hr.stackBound
  have init := PanicAllocatePointerNative.final_read_above_stack p hr.wf hr.width hr.spLower hr.stackBound 1074932 (by omega)
  have lock := PanicAllocatePointerNative.final_read_above_stack p hr.wf hr.width hr.spLower hr.stackBound 1074920 hstack
  have old := PanicAllocatePointerNative.final_read_above_stack p hr.wf hr.width hr.spLower hr.stackBound 1074928 (by omega)
  exact {
    module := hr.module
    globalIndex := hr.globalIndex
    global := hr.global
    sp := hr.sp
    memoryIndex := hr.memoryIndex
    memory := hr.memory
    function508Index := hr.function508Index
    function508 := hr.function508
    function509Index := hr.function509Index
    function509 := hr.function509
    allocatorIndex := hai
    allocator := ha
    hookIndex := hhi
    hook := hh
    wf := hr.wf
    width := hr.width
    spLower := hr.spLower
    stackBound := hr.stackBound
    depth := hr.depth
    hookSpan := by rw [final.2.1]; exact hspan
    initial := init.trans hinit
    unlocked := lock.trans hlock
    oldVtable := old.trans hold }

end WNear.Proofs.PanicHookNative
