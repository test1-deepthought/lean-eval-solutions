# Incomplete Lean-Eval attempt: sturm

## Failed Lean Error

Unsolved goal: the full Sturm-sequence theory (sign alternation of the Euclidean chain at common zeros, local constancy of sigma off roots, and the unit variation-drop at simple roots) must be built from scratch over the opaque noncomputable definitions sturmAux/sturmChain/signChanges/sigma. Mathlib provides no Sturm API; Polynomial.Squarefree, Polynomial.mod_add_div, Polynomial.div_add_mod, Polynomial.mod_eq_zero are all absent under those names.

## Agent Response Context

Sturm's theorem for ℝ[X] with the challenge's custom Sturm chain and sign-variation function. The mathematical proof is established (verified at proof rigor in the MATHS pipeline): the Sturm chain terminates at a nonzero constant for squarefree p (fuel natDegree+2 is adequate, confirmed computationally); at any common zero of consecutive chain entries the neighbors have opposite signs (from the Euclidean division identity g_{k+2} = -(g_k mod g_{k+1})); sigma is locally constant away from roots of p; and across each simple root sigma drops by exactly 1, so telescoping sigma p a - sigma p b counts the distinct roots in (a,b).

Lean formalization is INCOMPLETE. The decisive remaining obligation is the full Sturm-sequence theory over the opaque noncomputable definitions. Verified partial results: sturmAux definitional unfolding (zero, succ, stop), signChanges of the empty list, and the identification of the linchpin identity (a % b).eval β = a.eval β at a root of b, which reduces to the general Euclidean division identity (available only as EuclideanDomain.mod_add_div / Polynomial.mod_def, not as Polynomial.mod_add_div). Mathlib has no Sturm, sign-variation, or chain-sign-alternation theory, and Polynomial.Squarefree / Polynomial.mod_eq_zero are absent under those names — so the remaining ~hundreds of lines mirroring Isabelle's AFP Sturm_Sequences are outside the current budget.

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

theorem sturmAux_zero (a b : ℝ[X]) : sturmAux a b 0 = [a] := rfl

theorem sturmAux_succ (a b : ℝ[X]) (n : ℕ) (hb : b ≠ 0) :
    sturmAux a b (n + 1) = a :: sturmAux b (-(a % b)) n := by
  simp [sturmAux, hb]

theorem sturmAux_stop (a : ℝ[X]) (n : ℕ) : sturmAux a 0 (n + 1) = [a] := by
  simp [sturmAux]

theorem signChanges_nil : signChanges ([] : List ℝ) = 0 := by
  simp [signChanges]

theorem mod_eval_at_root (a b : ℝ[X]) (hb : b ≠ 0) (β : ℝ) (hβ : b.eval β = 0) :
    (a % b).eval β = a.eval β := by
  sorry

end Submission
```

## Evidence scope

Saved source and prose are attempt artifacts, not verification evidence. Only matching successful Lean evidence establishes verification. Missing source is not reconstructed from the report.

No candidate_submission was supplied; no Submission.lean artifact was saved.