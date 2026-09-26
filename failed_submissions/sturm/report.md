# Incomplete Lean-Eval attempt: sturm

## Failed Lean Error

Do not have the core Sturm telescoping identity: ((p.roots.toFinset).filter (fun x => a < x ∧ x < b)).card = sigma p a - sigma p b. The verified helper lemmas do not discharge it.

## Agent Response Context

Attempt to prove sturm_aux_telescoping via a parallel formal worker did not complete.

VERIFIED PARTIAL WORK (compiles cleanly, exit code 0 in lean4_probe):
The definitions sturmAux, sturmChain, signChanges, sigma, and five helper lemmas all type-check:
signChanges_le, root_count_le, sigma_le, chain_length_pos, poly_ne_zero.

REMAINING CORE GAP (exact, unresolved):
The telescoping identity itself is not proven:
  ∀ (p : ℝ[X]) (a b : ℝ), Squarefree p → a < b → p.eval a ≠ 0 → p.eval b ≠ 0 →
    ((p.roots.toFinset).filter (fun x => a < x ∧ x < b)).card = sigma p a - sigma p b

To close it one needs the local sign-change behavior of the Sturm chain, none of which is formalized:
 (i) at a simple root c of p, the number of sign changes sigma p x drops by exactly 1 as x passes c (the first chain entry changes sign while the rest keep a fixed pattern);
 (ii) on any subinterval containing no root of p, sigma p · is locally constant;
 (iii) telescoping (i) and (ii) across the roots in (a,b) yields the cardinality difference.

These three local statements are the mathematically decisive part of Sturm's theorem and are the exact blockers. The Mathlib library does not expose them in a directly usable form for this chain definition, so the route must construct them from scratch.

## Lean 4 Code From This Attempt

```lean4
import Mathlib
import Mathlib.Tactic

open Polynomial
open scoped Classical

namespace LeanEval
namespace Algebra

noncomputable def sturmAux : ℝ[X] → ℝ[X] → ℕ → List ℝ[X]
| a, _, 0 => [a]
| a, b, (n + 1) =>
  if b = 0 then [a] else a :: sturmAux b (-(a % b)) n

noncomputable def sturmChain (p : ℝ[X]) : List ℝ[X] :=
  sturmAux p (derivative p) (p.natDegree + 2)

noncomputable def signChanges (xs : List ℝ) : ℕ :=
  let ys := xs.filter (· ≠ 0)
  ((ys.zip ys.tail).filter (fun q => q.1 * q.2 < 0)).length

noncomputable def sigma (p : ℝ[X]) (x : ℝ) : ℕ :=
  signChanges ((sturmChain p).map fun q => q.eval x)

end Algebra
end LeanEval

open LeanEval.Algebra

namespace Submission

theorem sturm_aux_poly_ne_zero (p : ℝ[X]) (hp : Squarefree p) : p ≠ 0 :=
  hp.ne_zero

theorem sturm_aux_signChanges_le (xs : List ℝ) :
    signChanges xs ≤ (xs.filter (· ≠ 0)).length := by
  rw [signChanges]
  refine le_trans (List.length_filter_le _ _) ?_
  rw [List.length_zip, List.length_tail]
  omega

theorem sturm_aux_root_count_le (p : ℝ[X]) (a b : ℝ) :
    ((p.roots.toFinset).filter (fun x => a < x ∧ x < b)).card ≤ p.roots.card := by
  calc ((p.roots.toFinset).filter (fun x => a < x ∧ x < b)).card
      ≤ (p.roots.toFinset).card := Finset.card_filter_le _ _
    _ ≤ p.roots.card := Multiset.toFinset_card_le _

theorem sturm_aux_sigma_le (p : ℝ[X]) (x : ℝ) :
    sigma p x ≤ (sturmChain p).length := by
  rw [sigma]
  refine le_trans (sturm_aux_signChanges_le _) ?_
  have := List.length_filter_le (fun x : ℝ => decide (x ≠ 0))
    ((sturmChain p).map (fun q => q.eval x))
  rw [List.length_map] at this
  exact this

theorem sturm_aux_chain_length_pos (p : ℝ[X]) :
    0 < (sturmChain p).length := by
  rw [sturmChain]
  have h : p.natDegree + 2 ≠ 0 := by omega
  cases hc : p.natDegree + 2 with
  | zero => exact absurd hc h
  | succ n =>
    have key : (sturmAux p (derivative p) (n + 1)).length ≠ 0 := by
      rw [sturmAux]; split <;> simp
    omega

end Submission
```

## Evidence scope

Saved source and prose are attempt artifacts, not verification evidence. Only matching successful Lean evidence establishes verification. Missing source is not reconstructed from the report.

No candidate_submission was supplied; no Submission.lean artifact was saved.