import NearCrypto
import CryptoTests.Fixtures

/-!
The vectors of `bls12381.jsonl` (oracle: `near-vm-runner` 0.37.4 `VMLogic::bls12381_*`, over `blst`
0.3.11) against the `Spec` and the `Impl` of `NearCrypto.Bls12381`. A line is
`{kind, name, input, v0, v1}` where `v0` and `v1` are the host's answer without and with the NEP-488
fix: `{trap}`, `{ret}` or `{ret, output}`.
-/

namespace CryptoTests.Bls

open Lean NearCrypto Bls12381

/-- The reference pairing costs about 0.5 s a pair; it runs on the lines with few pairs. -/
def specPairs : Nat :=
  3

/-- The answer of the host: `none` for a trap, else the return value and the register. -/
def answer (j : Json) : Except String (Option (Nat × Option ByteArray)) := do
  if (j.getObjValAs? Bool "trap").toOption == some true then
    return none
  let ret ← j.getObjValAs? Nat "ret"
  let out ←
    match bytes j "output" with
    | .ok b =>
      pure (some b)
    | .error _ =>
      pure none
  return some (ret, out)

def render : Except String (Option ByteArray) → String
  | .error e => s!"trap ({e})"
  | .ok none => "ret 1"
  | .ok (some b) => s!"ret 0 {toHex b}"

def renderWant : Option (Nat × Option ByteArray) → String
  | none => "trap"
  | some (c, none) => s!"ret {c}"
  | some (c, some b) => s!"ret {c} {toHex b}"

def same (got : Except String (Option ByteArray)) (want : Option (Nat × Option ByteArray)) : Bool :=
  match got, want with
  | .error _, none => true
  | .ok none, some (1, none) => true
  | .ok (some b), some (0, some o) => b == o
  | .ok (some b), some (0, none) => b.isEmpty
  | _, _ => false

def firstError (rs : List (Option String)) : Option String :=
  rs.findSome? id

def sameCode (got : Except String Nat) (want : Option (Nat × Option ByteArray)) : Bool :=
  match got, want with
  | .error _, none => true
  | .ok c, some (w, _) => c == w
  | _, _ => false

def check (j : Json) : Except String (Option String) := do
  let kind ← str j "kind"
  let input ← bytes j "input"
  let mut errs : List (Option String) := []
  for (version, key) in [(0, "v0"), (1, "v1")] do
    let want ← answer (← j.getObjVal? key)
    if kind == "pairing_check" then
      let impl := pairingCheck Impl.ops input
      errs :=
        errs ++
          [if sameCode impl want then none
            else some s!"Impl {key}: got {repr (impl.toOption)}, want {renderWant want}"]
      if input.size / 288 ≤ specPairs then
        let spec := pairingCheck Spec.ops input
        errs :=
          errs ++
            [if sameCode spec want then none
              else some s!"Spec {key}: got {repr (spec.toOption)}, want {renderWant want}"]
    else
      let run (ops : Ops) : Except String (Option ByteArray) :=
        match kind with
        | "p1_sum" => p1Sum ops version input
        | "p2_sum" => p2Sum ops version input
        | "g1_multiexp" => g1Multiexp ops version input
        | "g2_multiexp" => g2Multiexp ops version input
        | "p1_decompress" => p1Decompress ops version input
        | "p2_decompress" => p2Decompress ops version input
        | "map_fp_to_g1" => mapFpToG1 ops input
        | "map_fp2_to_g2" => mapFp2ToG2 ops input
        | _ => .error "unknown kind"
      errs :=
        errs ++
          [if same (run Impl.ops) want then none
            else some s!"Impl {key}: got {render (run Impl.ops)}, want {renderWant want}",
            if same (run Spec.ops) want then none
            else some s!"Spec {key}: got {render (run Spec.ops)}, want {renderWant want}"]
  pure (firstError errs)

end CryptoTests.Bls
