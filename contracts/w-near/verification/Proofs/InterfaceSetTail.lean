import Proofs.InterfaceSetInstallTail
import Proofs.InterfaceSetReleaseTail

/-! Sequential composition of the actual setter installation and release suffixes. -/
namespace WNear.Proofs.InterfaceSetTail
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.StorePairCaller (paid paid_credits)
open WNear.Proofs.InterfaceSetState
set_option maxRecDepth 16384
set_option maxHeartbeats 300000

def installed (s : Store NearState) (op : Nat) (p : Layout) (m0 m1 m2 : Memory) :=
  InterfaceSetInstallTail.after s op p.memoryIndex (scratch p) p.receiver p.vtable m0 m1 m2

def pointerFrame (frame : CallFrame) (p : Layout) (m1 : Memory) :=
  InterfaceSetInstallTail.afterFrame frame (scratch p) m1

def after (s : Store NearState) (op : Nat) (p : Layout) (counter : UInt32) (m0 m1 m2 m3 : Memory) :=
  InterfaceSetReleaseTail.after (installed s op p m0 m1 m2) op p.globalIndex p.memoryIndex (scratch p) counter m3

def finalFrame (frame : CallFrame) (p : Layout) (m1 : Memory) :=
  InterfaceSetReleaseTail.finalFrame (pointerFrame frame p m1)

theorem installed_credits (s : Store NearState) (op rest : Nat) (p : Layout) (m0 m1 m2 : Memory)
    (hc : s.host.gas.Credits (30 * op + rest)) :
    (installed s op p m0 m1 m2).host.gas.Credits rest := by
  have c4 := InterfaceSetBody.copiedWord_credits s op p.memoryIndex 12 28 (26 * op + rest) (scratch p) m0
    (hc.mono (by omega))
  have c9 := InterfaceSetBody.copiedTeeWord_credits (InterfaceSetInstallTail.highStore s op p.memoryIndex (scratch p) m0)
    op p.memoryIndex 8 24 (21 * op + rest) (scratch p) m1 (c4.mono (by omega))
  have c10 := paid_credits (InterfaceSetInstallTail.lowStore s op p.memoryIndex (scratch p) m0 m1)
    op 1 (14 * op + (6 * op + rest)) (c9.mono (by omega))
  have cg := InterfaceInstall.guardAfter_credits _ op (6 * op + rest) c10
  exact InterfaceSetBody.twoWordsStore_credits _ op p.memoryIndex 4 0 rest
    (readI32 m1 ((scratch p).toNat + 8)) p.vtable p.receiver m2 cg

/-- The actual70-step suffix. Snapshot and array lookup premises describe only
sequential memory and linked code; neither suffix is assumed to execute. -/
theorem wp_tail (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (p : Layout) (counter : UInt32) (m0 m1 m2 m3 : Memory) (global : GlobalInst) (post : Post)
    (hs : frame.locals[3]? = some (.i32 (scratch p)))
    (hr : frame.locals[1]? = some (.i32 p.receiver)) (hv : frame.locals[2]? = some (.i32 p.vtable))
    (hsize : 4 ≤ frame.locals.size) (hcode : Code s p frame.inst)
    (hmem : s.mems[p.memoryIndex]? = some m0)
    (hmem1 : (InterfaceSetInstallTail.highStore s cfg.regularOpCost p.memoryIndex (scratch p) m0).mems[p.memoryIndex]? = some m1)
    (hmem2 : (InterfaceSetInstallTail.lowStore s cfg.regularOpCost p.memoryIndex (scratch p) m0 m1).mems[p.memoryIndex]? = some m2)
    (hhighRead : (scratch p).toNat + 12 + 4 ≤ m0.byteSize) (hhighWrite : (scratch p).toNat + 28 + 4 ≤ m0.byteSize)
    (hlowRead : (scratch p).toNat + 8 + 4 ≤ m1.byteSize) (hlowWrite : (scratch p).toNat + 24 + 4 ≤ m1.byteSize)
    (hwf : m2.wf) (hpointer : (readI32 m1 ((scratch p).toNat + 8)).toNat + 8 ≤ m2.byteSize)
    (hempty : readI32 m2 (readI32 m1 ((scratch p).toNat + 8)).toNat = 0)
    (hcodeInstalled : Code (installed s cfg.regularOpCost p m0 m1 m2) p frame.inst)
    (hg : (installed s cfg.regularOpCost p m0 m1 m2).globals[p.globalIndex]? = some global)
    (hglobal : global.value = .i32 (scratch p))
    (hmemory : (installed s cfg.regularOpCost p m0 m1 m2).mems[p.memoryIndex]? = some m3)
    (hcounter : readI32 m3 (((scratch p + 24) ||| 4).toNat) = counter)
    (hrb : ((scratch p + 24) ||| 4).toNat + 4 ≤ m3.byteSize)
    (hcb : counter.toNat + 4 ≤ m3.byteSize) (hd : callers.length + 2 < limits.maxCallDepth)
    (hc : s.host.gas.Credits (101 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (after s cfg.regularOpCost p counter m0 m1 m2 m3) limits base.toArray
      (finalFrame frame p m1) callers code)) rest post) :
    WP cfg (fuel + 70) (.next (atCode s limits base.toArray
      (nested frame base.toArray.size code) callers
      (WNear.Binary.InterfaceSet.copyBorrow ++ WNear.Binary.InterfaceSet.guard ++
        WNear.Binary.InterfaceSet.install ++ WNear.Binary.InterfaceSet.release)))
      (101 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let pf := pointerFrame frame p m1
  let nf := nested frame base.toArray.size code
  have hs' : pf.locals[3]? = some (.i32 (scratch p)) := by
    simpa [pf, pointerFrame, InterfaceSetInstallTail.afterFrame] using hs
  have ci : (installed s op p m0 m1 m2).host.gas.Credits (71 * op + rest) :=
    installed_credits s op (71 * op + rest) p m0 m1 m2 (hc.mono (by dsimp [op]; omega))
  have releaseNext : WP cfg fuel (.next (atCode
      (InterfaceSetReleaseTail.after (installed s op p m0 m1 m2) op p.globalIndex p.memoryIndex (scratch p) counter m3)
      limits base.toArray (InterfaceSetReleaseTail.finalFrame pf) callers code)) rest post := hnext
  have releaseRule := InterfaceSetReleaseTail.wp_release_tail cfg fuel rest (installed s op p m0 m1 m2)
    limits base pf callers code p counter m3 global post hs' hcodeInstalled hg hglobal hmemory hcounter hrb hcb hd ci releaseNext
  have releaseStart : WP cfg (fuel + 47) (.next (atCode (installed s op p m0 m1 m2) limits base.toArray
      (InterfaceSetInstallTail.afterFrame nf (scratch p) m1) callers WNear.Binary.InterfaceSet.release)) (71 * op + rest) post := by
    simpa only [pf, pointerFrame, nf, nested, emptyBlockFrame, InterfaceSetInstallTail.afterFrame] using releaseRule
  have hsN : nf.locals[3]? = some (.i32 (scratch p)) := hs
  have hrN : nf.locals[1]? = some (.i32 p.receiver) := hr
  have hvN : nf.locals[2]? = some (.i32 p.vtable) := hv
  have result := InterfaceSetInstallTail.wp_tail cfg (fuel + 47) (71 * op + rest) s limits base nf callers
    WNear.Binary.InterfaceSet.release (scratch p) p.receiver p.vtable p.mi p.memoryIndex 464 m0 m1 m2 post
    hsN hrN hvN hsize hcode.module hcode.memoryIndex hmem hmem1 hmem2 hhighRead hhighWrite hlowRead hlowWrite
    hwf hpointer hempty hcode.guardIndex hcode.guardFunction (by omega) (hc.mono (by dsimp [op]; omega)) releaseStart
  have fe : (fuel + 47) + 23 = fuel + 70 := by omega
  have ge : 30 * cfg.regularOpCost + (71 * op + rest) = 101 * cfg.regularOpCost + rest := by dsimp [op]; omega
  have ce : WNear.Binary.InterfaceSet.copyBorrow ++ WNear.Binary.InterfaceSet.guard ++
      WNear.Binary.InterfaceSet.install ++ WNear.Binary.InterfaceSet.release =
      WNear.Binary.InterfaceSet.copyBorrow ++ WNear.Binary.InterfaceSet.guard ++
      WNear.Binary.InterfaceSet.install ++ WNear.Binary.InterfaceSet.release := rfl
  exact ValueReturnOuterBody.cast_phase cfg _ _ _ _ s limits base.toArray nf callers _ _ post fe ge ce result

end WNear.Proofs.InterfaceSetTail
