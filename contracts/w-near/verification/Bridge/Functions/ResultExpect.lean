import Binary.Code.Part01
import NearLogic.Tactic.Control
import Bridge.Functions.FtTotalSupplyGetter
import Bridge.Functions.VecDeref

/-!
# `Result::expect` (function 158), the `Ok` path, in the metered logic

`expect(out, res, loc)` on the `Result` whose tag is the word at `res`: when
the tag is not 1 (`Ok`) the 12 payload bytes at `res + 4` are copied to `out`
(an `i64` and an `i32` load/store); the 16-byte frame it reserves on the
shadow stack is not touched on this path. The `Err` path (`unwrap_failed`,
881) is not covered.

`f158_spec` is its `MFunSpec` for `Ok`: 26 `regular_op_cost`s (with the
activation 10, paid by the caller, the harness's 36, `resultExpect`). The
precondition owns `out` and the payload separately, so it is stronger than
the harness's (which only excludes `out` overlapping the payload's last word).
-/

namespace WNear.Binary.ResultExpect

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary.U128From (memBytes_split memBytes_join)

theorem decodeLE_lt (bs : List UInt8) : Memory.decodeLE bs < 256 ^ bs.length := by
  induction bs with
  | nil => simp [Memory.decodeLE]
  | cons b bs ih =>
    simp only [Memory.decodeLE, List.foldr_cons, List.length_cons] at *
    have := b.toNat_lt
    rw [Nat.pow_succ]
    omega

theorem ofNat_ne_one {bs : List UInt8} (h4 : bs.length = 4) (h : Memory.decodeLE bs ≠ 1) :
    UInt32.ofNat (Memory.decodeLE bs) ≠ 1 := by
  have hl := decodeLE_lt bs
  rw [h4] at hl
  intro e
  apply h
  have := congrArg UInt32.toNat e
  simp at this hl
  omega

theorem bytes32_decode (bs : List UInt8) (h : bs.length = 4) :
    bytes32 (UInt32.ofNat (Memory.decodeLE bs)) = bs :=
  WNear.Binary.VecDeref.storeBytes_load_i32 bs h

theorem bytes64_decode (bs : List UInt8) (h : bs.length = 8) :
    storeBytes (.i64 (UInt64.ofNat (Memory.decodeLE bs))) 8 = bs := by
  simpa [loadValue] using WNear.Binary.FtTotalSupplyGetter.storeBytes_load_i64 bs h

section Spec

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The precondition: the arguments, the stack pointer's global `g`, the tag
word at `res`, the 12 payload bytes after it, and the 12 bytes at `out`. -/
def pre (n g : Nat) (gi : GlobalInst) (out res loc : UInt32) (tag pl ob : List UInt8)
    (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 out, .i32 res, .i32 loc]⌝ ∗ g ↦[wg] gi ∗ n ↦[wms][ res.toNat ] tag ∗
    n ↦[wms][ res.toNat + 4 ] pl ∗ n ↦[wms][ out.toNat ] ob)

/-- The postcondition: no results, the global restored, the payload at `out`. -/
def post (n g : Nat) (gi : GlobalInst) (out res : UInt32) (tag pl : List UInt8)
    (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = []⌝ ∗ g ↦[wg] gi ∗ n ↦[wms][ res.toNat ] tag ∗
    n ↦[wms][ res.toNat + 4 ] pl ∗ n ↦[wms][ out.toNat ] pl)

/-- `Result::expect` (function 158 of `contract.wasm`) on an `Ok` (tag not 1):
26 `regular_op_cost`s. -/
theorem f158_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (n g : Nat)
    (hn : mi.memAddrs[0]? = some n) (hg : mi.globalAddrs[0]? = some g) (Cg : Nat)
    (gi : GlobalInst) (sp out res loc : UInt32) (hgi : gi.value = .i32 sp)
    (hres : res.toNat + 16 ≤ 2 ^ 32) (hout : out.toNat + 12 ≤ 2 ^ 32)
    (tag pl ob : List UInt8) (htag : tag.length = 4) (hpl : pl.length = 12)
    (hob : ob.length = 12) (hok : Memory.decodeLE tag ≠ 1) :
    ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f158 Cg (pre n g gi out res loc tag pl ob)
        (fun _ => 26 * cfg.regularOpCost) (post n g gi out res tag pl) := by
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold pre at HP
  icases HP with ⟨%hargs, Hg, Ht, Hp, Ho⟩
  subst hargs
  obtain ⟨gt, gv⟩ := gi
  simp only at hgi
  subst hgi
  simp only [f158]
  mstep [Hg]
  mstep
  mstep
  mstep
  mstep [Hg]
  mstep
  mstep
  mstep [Ht]
  mstep
  have hne := ofNat_ne_one htag hok
  mstep
  mstep_taken with (simp [Numeric.bool, Numeric.irelop32, hne])
  icases memBytes_split n (res.toNat + 4) 8 pl (by omega) $$ Hp with ⟨Hp1, Hp2⟩
  icases memBytes_split n out.toNat 8 ob (by omega) $$ Ho with ⟨Ho1, Ho2⟩
  mstep
  mstep
  mstep [Hp1]
  mstep [Ho1]
  mstep
  mstep
  mstep
  mstep
  mstep
  mstep
  mstep [Hp2]
  mstep [Ho2]
  mstep
  mstep
  mstep
  mstep [Hg]
  have e : sp - 16 + 16 = sp := by simp
  rw [e, bytes64_decode _ (by simp; omega), bytes32_decode _ (by simp; omega)]
  ihave Hp := memBytes_join n (res.toNat + 4) 8 (pl.take 8) (pl.drop 8) (by simp; omega) $$ [Hp1 Hp2]
  · isplitl [Hp1] <;> iassumption
  ihave Ho := memBytes_join n out.toNat 8 (pl.take 8) (pl.drop 8) (by simp; omega) $$ [Ho1 Ho2]
  · isplitl [Ho1] <;> iassumption
  rw [List.take_append_drop]
  iframe Hc
  iunfold post
  iframe Hg Ht Hp Ho
  ipureintro; rfl

end Spec

end WNear.Binary.ResultExpect
