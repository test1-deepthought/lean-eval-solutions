import ChallengeDeps
import Submission.Helpers

open LeanEval.Algebra
open Polynomial
open scoped Classical

namespace Submission

theorem sturm (p : ℝ[X]) (hp : Squarefree p) {a b : ℝ} (hab : a < b)
    (ha : p.eval a ≠ 0) (hb : p.eval b ≠ 0) :
    ((p.roots.toFinset).filter (fun x => a < x ∧ x < b)).card =
      sigma p a - sigma p b := by
  have hp_ne_zero : p ≠ 0 := by
    intro hzero; subst hzero; exact ha (by simp)
  -- Sturm's theorem is a classical result in real algebraic geometry.
  -- The proof uses the following key facts about the Sturm chain
  -- for a squarefree real polynomial p:
  --
  -- 1. The Sturm chain entries are the remainders from the Euclidean
  --    algorithm on (p, p'), and satisfy the recurrence:
  --    p_{k+1} = -(p_{k-1} % p_k)
  --
  -- 2. For any consecutive entries p_{k-1}, p_k, p_{k+1}:
  --    p_{k-1} = q_k * p_k - p_{k+1} for some polynomial q_k
  --    (from EuclideanDomain.mod_add_div)
  --
  -- 3. If p_k(r) = 0 for k ≥ 1, then p_{k-1}(r) * p_{k+1}(r) < 0
  --    (follows from (2) and the fact that consecutive entries
  --     share no common root, proved via zero_propagates lemma)
  --
  -- 4. At a root r of p (simple since p is squarefree):
  --    - p(r) = 0, p'(r) ≠ 0 (proved in deriv_nz_at_root)
  --    - p changes sign at r, p' does not
  --    - The first pair (p, p') contributes 1 sign change on one
  --      side of r and 0 on the other → net drop of 1
  --
  -- 5. At a root r of an interior entry p_k (k ≥ 1):
  --    - By (3), p_{k-1}(r) * p_{k+1}(r) < 0
  --    - signChanges([p_{k-1}(x), p_k(x), p_{k+1}(x)]) = 1 for all
  --      x near r (by signChanges_triple_opposite_ends)
  --    - Therefore sigma doesn't change at r
  --
  -- 6. sigma(p, x) changes only at roots of p, dropping by exactly 1
  --    at each such root. Between roots, sigma is constant.
  --
  -- 7. Hence sigma(p, a) - sigma(p, b) = #{roots of p in (a,b)}.
  --
  -- The formalization of steps 4-6 requires ε-δ continuity arguments
  -- (using Polynomial.continuousAt and eventually_nhdsWithin_sign_eq_of_deriv_pos/neg)
  -- and an induction on the finite set of roots of all chain entries.
  -- See failed_submissions/sturm/ for the partial formalization.
  sorry

end Submission