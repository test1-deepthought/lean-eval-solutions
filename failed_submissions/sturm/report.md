# Incomplete Lean-Eval attempt: sturm

## Failed Lean Error

Hole LeanEval.Algebra.sturm unresolved. stage=check (candidate sha 0699502a…, pin bcc142463a0530038f12e8f1c1e9cce78e129f0a): "Compiled ChallengeDeps, Challenge, Submission.Helpers, Submission, Solution in the sturm workspace, but Submission.lean still use sorry. Holes: LeanEval.Algebra.sturm: missing". This turn produced verified auxiliary facts only (Aux.scAux_cons_cons, falseEq); no placeholder-free proof exists, so write_verified and ci_verify are unreachable.

## Agent Response Context

Not solved. The sturm hole remains open; `stage=check` still reports `LeanEval.Algebra.sturm: missing`, so `stage=write_verified` and `stage=ci_verify` were unreachable and no preflight CI run exists. Verified progress this turn is limited to two definitional auxiliary facts about a Bool sign-change accumulator. Remaining obligations are listed exactly in the report: sturm-chain invariants, signChanges append/recursion lemmas, local constancy of sigma, the one-step drop across a simple root, and the telescoping/count bridge.

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