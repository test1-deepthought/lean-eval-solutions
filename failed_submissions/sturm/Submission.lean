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
  -- The proof of Sturm's theorem requires analyzing the sign changes of the
  -- Sturm chain at points a and b, using the fact that for a squarefree polynomial:
  -- 1. The Sturm chain terminates with a nonzero constant (gcd(p,p') = 1)
  -- 2. Consecutive entries share no common root
  -- 3. At a root of p, sigma drops by exactly 1
  -- 4. At a root of any other chain entry, sigma is unchanged
  -- The result follows by summing contributions across all roots in (a,b).
  -- 
  -- Key lemmas proved in Submission/Helpers.lean:
  -- - signChanges_nil, signChanges_singleton, signChanges_pair
  -- - signChanges_triple_opposite_ends
  -- - sturmAux_recurse, sturmAux_ne_nil, sturmChain_ne_nil
  -- - deriv_nz_at_root (derivative nonzero at roots of squarefree p)
  sorry

end Submission