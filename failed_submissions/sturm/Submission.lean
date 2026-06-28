import ChallengeDeps
import Submission.Helpers

open LeanEval.Algebra
open Polynomial
open scoped Classical

namespace Submission

theorem sturm (p : ℝ[X]) (hp : Squarefree p) {a b : ℝ} (hab : a < b)
    (ha : p.eval a ≠ 0) (hb : p.eval b ≠ 0) :
    ((p.roots.toFinset).filter (fun x => a < x ∧ x < b)).card = sigma p a - sigma p b := by
  -- This is a significant theorem requiring a complete formalization of Sturm's theorem.
  -- The proof requires:
  -- 1. Showing that sigma(p,x) is constant on intervals where no chain polynomial has a root
  -- 2. Showing that at a simple root r of p, sigma drops by exactly 1:
  --    - p(r) = 0, p'(r) ≠ 0 (squarefree)
  --    - For x < r < y close to r: p(x) and p'(x) have opposite signs, p(y) and p'(y) have same sign
  --    - The first_flip_opposite lemma in Helpers.lean gives signChanges(x::y::tail) - signChanges((-x)::y::tail) = 1
  --    - Higher chain entries either maintain sign (if nonzero at r) or flip in canceling triples
  -- 3. Showing that at a root of an interior chain polynomial (not p), sigma is unchanged
  -- 4. Constructing the finite set of all chain roots in (a,b), sorting them, and telescoping the jumps
  -- 
  -- The helper lemmas in Helpers.lean provide the key combinatorial and analytic tools.
  -- See Submission/Helpers.lean for the supporting lemmas including:
  -- - filter_id_of_all_nonzero, signChanges_of_all_nonzero
  -- - first_flip_opposite (key lemma: sign change of 1 when first entry flips)
  -- - same_sign_of_no_root (sign constancy between roots via IVT)
  -- - sturm_relation, eval_at_root (algebraic properties of the Sturm chain)
  sorry

end Submission