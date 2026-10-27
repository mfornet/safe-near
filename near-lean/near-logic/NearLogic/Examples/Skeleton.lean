import NearLogic.Rules.Pure
import NearLogic.Call
import NearLogic.Hosts.ValueReturn
import NearLogic.Method

/-!
# Walking skeleton: a method that returns a constant

The smallest method that goes through every layer (milestone M2): `get`
returns the four bytes `"ok"` (quotes included) from the data segment at
address 0, through `value_return`:

```wat
(module
  (import "env" "value_return" (func $value_return (param i64 i64)))
  (memory 1)
  (data (i32.const 0) "\"ok\"")
  (func (export "get") (call $value_return (i64.const 4) (i64.const 0))))
```

This file proves its body, from the bytes in memory and credits for its
three instructions and the host call, to falling through with the return
data selected.
-/

namespace NearLogic.Skeleton

open Wasm Wasm.Near WasmLogic Iris Iris.BI Iris.ProgramLogic

/-- The returned bytes: `"ok"`, quotes included. -/
def okBytes : List UInt8 := [34, 111, 107, 34]

/-- The body of `get`. -/
def body : List Instr := [.i64_const 4, .i64_const 0, .call 0]

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The body of `get`: from the host `h`, the four bytes at address 0 and
credits for three instructions and `value_return`, it falls through with
nothing on the stack and `"ok"` as the return data. -/
theorem body_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (f : Frame) (extra : Nat)
    (h : NearState) (a n : Nat) (mx : Option Nat) {Cg R : Nat} {Φ : Post NearState GF}
    (ha : f.mi.funcAddrs[0]? = some a) (hn : f.mi.memAddrs[0]? = some n)
    (hlim : withinLimit h.config.maxReturnLen 4 = true) :
    credits Cg (3 * cfg.regularOpCost + valueReturnUse h 4 + R) ∗
      a ↪[wf] FuncInst.host (metered extra "value_return" valueReturnFn).toHostFn ∗
      n ↪[wmlimit] mx ∗ mhostPt h ∗ n ↦[wms][ 0 ] okBytes ∗
      ▷ ▷ ▷ (mhostPt (h.selectReturnValue okBytes) -∗ n ↦[wms][ 0 ] okBytes -∗ credits Cg R -∗
        Φ.normal [] f)
      ⊢ mwpi cfg lim d f [] body Φ := by
  iintro ⟨Hc, #Hf, #Hm, Hh, Hb, HΦ⟩
  unfold body
  iapply mwpi_cons
  iapply mwpi_i64_const (R := cfg.regularOpCost + (cfg.regularOpCost + valueReturnUse h 4 + R))
  isplitl [Hc]
  · rw [show 3 * cfg.regularOpCost + valueReturnUse h 4 + R =
      cfg.regularOpCost + (cfg.regularOpCost + (cfg.regularOpCost + valueReturnUse h 4 + R)) by omega]
    iexact Hc
  inext
  iintro Hc
  simp only [Post.mseq_normal, List.nil_append]
  iapply mwpi_cons
  iapply mwpi_i64_const (R := cfg.regularOpCost + valueReturnUse h 4 + R)
  isplitl [Hc]
  · iexact Hc
  inext
  iintro Hc
  simp only [Post.mseq_normal]
  have hc : ReadContract (metered extra "value_return" valueReturnFn).toHostFn h (h.selectReturnValue okBytes)
      [.i64 4, .i64 0] [] 0 okBytes (valueReturnUse h 4) Cg :=
    valueReturn_readContract (C := Cg) extra h 4 0 okBytes (by decide) rfl hlim (by decide)
  rw [show ([Value.i64 4] ++ [Value.i64 0]) = ([] : List Value) ++ [.i64 4, .i64 0] from rfl]
  iapply mwpi_call_host_ro 0 a n 0 _ h _ mx okBytes [] [.i64 4, .i64 0] [] ha hn rfl hc
  isplitl [Hc]
  · iexact Hc
  isplitr
  · iexact Hf
  isplitr
  · iexact Hm
  isplitl [Hh]
  · iexact Hh
  isplitl [Hb]
  · iexact Hb
  inext
  iintro Hh Hb Hc
  simp only [List.nil_append]
  iapply HΦ $$ Hh Hb Hc

end NearLogic.Skeleton
