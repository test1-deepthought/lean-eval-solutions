# Incomplete Lean-Eval attempt: sturm

## Failed Lean Error

Hole LeanEval.Algebra.sturm unresolved: candidate contains `sorry`. stage=check reported "Submission.lean still use sorry / Holes: LeanEval.Algebra.sturm: missing". No placeholder-free proof of Sturm's theorem for the challenge's own `sturmChain`/`signChanges`/`sigma` definitions was produced this turn.

## Agent Response Context

Not solved. The `sturm` hole remains open: no placeholder-free candidate was produced, `stage=check` still reports the hole missing, and therefore `stage=write_verified` and `stage=ci_verify` were never reached. Verified partial work is limited to isolated list/state-machine evaluaton facts; the substantive obligations (chain invariants, local constancy, sign flip at a simple root, telescoping) are unproved. No repository write occurred.

## Lean 4 Code From This Attempt

```lean4
Verified this turn (isolated auxiliary facts only, not the target):

```lean
import Mathlib

namespace Aux

inductive St where
  | none : St
  | some (b : Bool) : St
  deriving DecidableEq

def scAux : List Bool → ℕ
  | [] => 0
  | [_] => 0
  | a :: b :: rest => scAux (b :: rest) + (if a = b then 0 else 1)

example (x y : Bool) : scAux [x, y] = (if x = y then 0 else 1) := by
  show scAux [y] + (if x = y then 0 else 1) = (if x = y then 0 else 1)
  show 0 + (if x = y then 0 else 1) = (if x = y then 0 else 1)
  simp

theorem falseEq (b : Bool) : (if false = b then (0 : ℕ) else 1) = (if b then 1 else 0) := by
  cases b <;> rfl

end Aux
```
```

## Evidence scope

Saved source and prose are attempt artifacts, not verification evidence. Only matching successful Lean evidence establishes verification. Missing source is not reconstructed from the report.