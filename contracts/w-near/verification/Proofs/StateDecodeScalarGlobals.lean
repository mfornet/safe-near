import Proofs.StateDecodeScalarCode

/-! The accepted child calls retain the scalar reader's reserved stack pointer. -/
namespace WNear.Proofs.StateDecodeScalar
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
private theorem globals_paid (s : Store NearState) (op n : Nat) : (paid s op n).globals=s.globals := by
  induction n with |zero=>rfl|succ n ih=>exact ih

theorem reserved_global (s : Store NearState) (op : Nat) (p : Layout)
    (hg : s.globals[p.globalIndex]?=some p.global) :
    (reserved s op p).globals[p.globalIndex]?=some {p.global with value:=.i32 (scratch p)} := by
  simp only [reserved,setGlobal,globals_paid,Array.getElem?_modify,hg,Option.map_some,ite_true]

theorem taken_global (wide : Bool) (s : Store NearState) (op : Nat) (p : Layout)
    (hg : s.globals[p.globalIndex]?=some p.global) :
    (taken wide s op p).globals[p.globalIndex]?=some {p.global with value:=.i32 (scratch p)} := by
  rw [(taken_fields wide s op p).2.2.2]
  exact reserved_global s op p hg

theorem readWords_global (wide : Bool) (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (hg : s.globals[p.globalIndex]?=some p.global) :
    (readWords wide cfg s p).globals[p.globalIndex]?=some {p.global with value:=.i32 (scratch p)} := by
  rw [(readWords_fields wide cfg s p).2.2.2]
  exact reserved_global s cfg.regularOpCost p hg

theorem dropped_global (wide : Bool) (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (hg : s.globals[p.globalIndex]?=some p.global) :
    (dropped wide cfg s p).globals[p.globalIndex]?=some {p.global with value:=.i32 (scratch p)} := by
  rw [(dropped_fields wide cfg s p).2.2.2]
  exact reserved_global s cfg.regularOpCost p hg
end WNear.Proofs.StateDecodeScalar
