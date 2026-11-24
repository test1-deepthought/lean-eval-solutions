# Incomplete Lean-Eval attempt: sturm

## Failed Lean Error

Hole LeanEval.Algebra.sturm unresolved after 8 attempt rounds. Latest stage=check (candidate sha ec5c5ae8…, pin bcc142463a0530038f12e8f1c1e9cce78e129f0a): "Submission.lean still use sorry. Holes: LeanEval.Algebra.sturm: missing". Last probe error: `rfl` failed, `0 + if x = y then 0 else 1` not definitionally equal to `if x = y then 0 else 1`. Latest verified auxiliary facts: Aux.scAux_cons_cons, Aux.falseEq. Nothing about the polynomial chain has been formalized, so write_verified/ci_verify remain unreachable.

## Agent Response Context

Not solved. Attempt 3 ended with the `sturm` hole still open: stage=check reports `LeanEval.Algebra.sturm: missing`, so stage=write_verified and stage=ci_verify were unreachable and no CI run is bound to any commit. Verified work this session is limited to two definitional Bool-list accumulator facts (scAux_cons_cons, falseEq). The residual obligations — sturm-chain invariants, signChanges calculus, sigma invariance between roots, the one-step drop at a simple root, and the telescoping/cardinality bridge — are enumerated exactly in the saved report.

## Lean 4 Code From This Attempt

```lean4
```lean
import Mathlib

namespace Aux

def scLast : List Bool → Bool
  | [] => false
  | [a] => a
  | _ :: b :: rest => scLast (b :: rest)

def scAux : List Bool → ℕ
  | [] => 0
  | [_] => 0
  | a :: b :: rest => scAux (b :: rest) + (if a = b then 0 else 1)

theorem scAux_cons_cons : ∀ (l : List Bool) (x y : Bool),
    scAux (x :: y :: l) = scAux (y :: l) + (if x = y then 0 else 1) :=
  fun l x y => rfl

theorem falseEq (b : Bool) : (if false = b then (0 : ℕ) else 1) = (if b then 1 else 0) := by
  cases b <;> rfl

end Aux
```
```

## Evidence scope

Saved source and prose are attempt artifacts, not verification evidence. Only matching successful Lean evidence establishes verification. Missing source is not reconstructed from the report.