# Incomplete Lean-Eval attempt: sturm

## Failed Lean Error

The frozen theorem `sturm` (Challenge.lean line 11) still carries its top-level `sorry`. The proof body requires the full Sturm-sequence theory (chain sign alternation, local constancy of the evaluation-based `sigma`, unit drop at simple roots) which has no Mathlib API: `Polynomial.sturmSeq` and `List.signVariations` are unknown constants in this environment (confirmed via direct #check), and the challenge's `signChanges`/`sturmChain` list definitions offer no simplification API.

## Agent Response Context

Continuing the Lean-Eval `sturm` problem: re-established the Phase-1 certificate, froze the formal target, and made genuine Lean progress on the structural layer. The full theorem remains unproved: its body requires the complete Sturm-sequence theory over the challenge's custom opaque definitions, with no available Mathlib API.

## Lean 4 Code From This Attempt

```lean4
import Mathlib

open Polynomial
open scoped Classical

namespace SturmBricks

noncomputable def sturmAux : ℝ[X] → ℝ[X] → ℕ → List ℝ[X]
  | a, _, 0       => [a]
  | a, b, (n + 1) => if b = 0 then [a] else a :: sturmAux b (-(a % b)) n

noncomputable def sturmChain (p : ℝ[X]) : List ℝ[X] :=
  sturmAux p (derivative p) (p.natDegree + 2)

noncomputable def signChanges (xs : List ℝ) : ℕ :=
  let ys := xs.filter (· ≠ 0)
  ((ys.zip ys.tail).filter (fun q => q.1 * q.2 < 0)).length

noncomputable def sigma (p : ℝ[X]) (x : ℝ) : ℕ :=
  signChanges ((sturmChain p).map fun q => q.eval x)

theorem signChanges_nil : signChanges [] = 0 := by
  unfold signChanges; simp

theorem signChanges_singleton (y : ℝ) : signChanges [y] = 0 := by
  unfold signChanges
  simp only [List.filter_cons]
  split
  · simp
  · simp

-- linchpin Euclidean identity: evaluation of the remainder at a root of the divisor
theorem mod_eval_at_root (a b : ℝ[X]) (hb : b ≠ 0) (β : ℝ) (hβ : b.eval β = 0) :
    (a % b).eval β = a.eval β := by
  have h := EuclideanDomain.mod_add_div a b
  have hev : ((a % b) + b * (a / b)).eval β = a.eval β := by rw [h]
  rw [Polynomial.eval_add, Polynomial.eval_mul, hβ, zero_mul, add_zero] at hev
  exact hev

-- sign alternation step at a common zero
theorem neg_mod_eval_at_root (a b : ℝ[X]) (hb : b ≠ 0) (β : ℝ) (hβ : b.eval β = 0) :
    (-(a % b)).eval β = - a.eval β := by
  rw [Polynomial.eval_neg, mod_eval_at_root a b hb β hβ]

theorem sturmChain_C (c : ℝ) : sturmChain (C c) = [C c] := by
  unfold sturmChain
  rw [Polynomial.derivative_C]
  cases h : (C c : ℝ[X]).natDegree + 2 with
  | zero => omega
  | succ n => simp [sturmAux]

theorem sigma_C (c : ℝ) (x : ℝ) : sigma (C c) x = 0 := by
  unfold sigma
  rw [sturmChain_C]
  simp only [List.map_cons, List.map_nil, Polynomial.eval_C]
  exact signChanges_singleton c

-- full constant base case of the theorem
theorem sturm_const (c : ℝ) {a b : ℝ} (hab : a < b) :
    ((C c : ℝ[X]).roots.toFinset.filter (fun x => a < x ∧ x < b)).card =
      sigma (C c) a - sigma (C c) b := by
  rw [Polynomial.roots_C, sigma_C, sigma_C]
  simp

end SturmBricks
```

## Evidence scope

Saved source and prose are attempt artifacts, not verification evidence. Only matching successful Lean evidence establishes verification. Missing source is not reconstructed from the report.

No candidate_submission was supplied; no Submission.lean artifact was saved.