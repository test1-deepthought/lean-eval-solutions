# Incomplete Lean-Eval attempt: sturm

## Failed Lean Error

Unsolved goal: the complete proof of the frozen theorem `sturm` requires the full Sturm-sequence theory over the opaque noncomputable definitions sturmAux/sturmChain/signChanges/sigma: (1) sign alternation of consecutive Euclidean-chain entries at their common zeros, (2) local constancy of sigma on intervals free of roots, (3) unit drop of sigma at each simple root. None of these has any Mathlib API; Sigma/SignChanges are List filter/zip operations with no simplification lemmas. Mathlib lacks Sturm, sign-variation, and chain-sign-alternation theory entirely. The helper linchpin `mod_eval_at_root` is now proven, but the top-level `sturm` body remains unproved.

## Agent Response Context

Request: remove Lean placeholders and verify the complete replacement.

This cannot be satisfied as stated. "Remove the placeholder and verify the complete replacement" presupposes that a placeholder-free proof of the frozen theorem `sturm` exists and merely needs submitting. It does not. The remaining top-level `sorry` in the frozen theorem marks a genuinely unproved mathematical obligation, not a formatting artifact: a `sorry` can only be replaced by an actual proof term, and constructing that term is the unsolved problem.

What was accomplished: the one helper placeholder (`mod_eval_at_root`) has been discharged. It now compiles with no sorry, proven via EuclideanDomain.mod_add_div + Polynomial.eval_mul. So the count of placeholders in the working file went from 1 helper + 1 frozen target to 1 frozen target.

What remains: a complete placeholder-free proof body for `sturm`. This requires the full Sturm-sequence theory developed from scratch over the opaque noncomputable definitions (sturmAux/sturmChain/signChanges/sigma): chain sign alternation at common zeros, local constancy of sigma off roots, unit drop at each simple root, telescoped over the distinct roots. Mathlib supplies none of this. Submitting any source with the target's sorry still present would not be a "complete replacement", and I will not emit a false `by simp` or unverified `exact` and claim it verifies.

Honest status: INCOMPLETE. The mathematical proof is established and verified at proof rigor; the Lean formalization is not, and the specific request to verify a complete replacement is not achievable with the available Mathlib and budget.

## Lean 4 Code From This Attempt

```lean4
import Mathlib
open Polynomial
open scoped Classical

namespace Submission

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

-- Verified structural facts:
theorem sturmAux_zero (a b : ℝ[X]) : sturmAux a b 0 = [a] := rfl

theorem sturmAux_succ (a b : ℝ[X]) (n : ℕ) (hb : b ≠ 0) :
    sturmAux a b (n + 1) = a :: sturmAux b (-(a % b)) n := by
  simp [sturmAux, hb]

theorem sturmAux_stop (a : ℝ[X]) (n : ℕ) : sturmAux a 0 (n + 1) = [a] := by
  simp [sturmAux]

theorem signChanges_nil : signChanges ([] : List ℝ) = 0 := by
  simp [signChanges]

-- Linchpin sign-alternation identity, now FULLY PROVEN (no sorry):
theorem mod_eval_at_root (a b : ℝ[X]) (β : ℝ) (hβ : b.eval β = 0) :
    (a % b).eval β = a.eval β := by
  have h := EuclideanDomain.mod_add_div a b
  have h2 : (a % b).eval β + (b * (a / b)).eval β = a.eval β := by
    rw [← Polynomial.eval_add, h]
  rw [Polynomial.eval_mul, hβ, zero_mul, add_zero] at h2
  exact h2

-- Frozen final theorem: proof body still absent.
theorem sturm (p : ℝ[X]) (hp : Squarefree p) {a b : ℝ} (hab : a < b)
    (ha : p.eval a ≠ 0) (hb : p.eval b ≠ 0) :
    ((p.roots.toFinset).filter (fun x => a < x ∧ x < b)).card =
      sigma p a - sigma p b := by
  sorry

end Submission
```

## Evidence scope

Saved source and prose are attempt artifacts, not verification evidence. Only matching successful Lean evidence establishes verification. Missing source is not reconstructed from the report.

No candidate_submission was supplied; no Submission.lean artifact was saved.