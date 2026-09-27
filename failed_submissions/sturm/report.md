# Incomplete Lean-Eval attempt: sturm

## Failed Lean Error

The frozen theorem `sturm` (Challenge.lean line 11) remains unproved this session. Its proof body requires the full Sturm-sequence theory over the challenge's custom noncomputable definitions: (1) chain sign alternation at common zeros, (2) local constancy of the evaluation-based `sigma` off roots, (3) unit drop at simple roots, then telescoping. `Polynomial.sturmSeq` and `List.signVariations` are local_missing in this environment (confirmed via mathlib_check and direct #check); `Polynomial.signVariations` exists but is lead-coefficient-based with no root-counting theorem. The custom `signChanges` filter/zip/decide layer offers no simplification API.

## Lean 4 Code From This Attempt

```lean4
import Mathlib

open Polynomial
open scoped Classical

namespace Probe

noncomputable def sturmAux : ℝ[X] → ℝ[X] → ℕ → List ℝ[X]
  | a, _, 0       => [a]
  | a, b, (n + 1) =>
    if b = 0 then [a] else a :: sturmAux b (-(a % b)) n

noncomputable def sturmChain (p : ℝ[X]) : List ℝ[X] :=
  sturmAux p (derivative p) (p.natDegree + 2)

noncomputable def signChanges (xs : List ℝ) : ℕ :=
  let ys := xs.filter (· ≠ 0)
  ((ys.zip ys.tail).filter (fun q => q.1 * q.2 < 0)).length

noncomputable def sigma (p : ℝ[X]) (x : ℝ) : ℕ :=
  signChanges ((sturmChain p).map fun q => q.eval x)

theorem sturmChain_C (c : ℝ) : sturmChain (C c) = [C c] := by
  unfold sturmChain sturmAux
  simp [derivative_C]

theorem signChanges_singleton (y : ℝ) : signChanges [y] = 0 := by
  unfold signChanges
  by_cases hy : y = 0
  · simp [hy]
  · simp [hy, List.filter_cons_of_pos]

theorem sigma_C (c x : ℝ) : sigma (C c) x = 0 := by
  unfold sigma
  rw [sturmChain_C]
  simp [signChanges_singleton]

theorem mod_eval_at_root (a b : ℝ[X]) (hb : b ≠ 0) (β : ℝ) (hβ : b.eval β = 0) :
    (a % b).eval β = a.eval β := by
  have h := EuclideanDomain.mod_add_div a b
  have hval := congrArg (fun q : ℝ[X] => q.eval β) h
  simp [eval_add, eval_mul, hβ] at hval
  linarith

end Probe
```

## Evidence scope

Saved source and prose are attempt artifacts, not verification evidence. Only matching successful Lean evidence establishes verification. Missing source is not reconstructed from the report.

No candidate_submission was supplied; no Submission.lean artifact was saved.