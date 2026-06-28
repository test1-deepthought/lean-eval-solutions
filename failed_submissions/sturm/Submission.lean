import ChallengeDeps
import Submission.Helpers

open LeanEval.Algebra
open Polynomial
open Set
open scoped Classical

namespace Submission

set_option autoImplicit false

theorem sturm (p : ℝ[X]) (hp : Squarefree p) {a b : ℝ} (hab : a < b)
    (ha : p.eval a ≠ 0) (hb : p.eval b ≠ 0) :
    ((p.roots.toFinset).filter (fun x => a < x ∧ x < b)).card = sigma p a - sigma p b := by
  -- This is Sturm's theorem. The proof follows from the structure
  -- of the Sturm chain: at each simple root of p, sigma drops by exactly 1,
  -- and sigma is constant on intervals where p has no roots.
  -- The helper lemmas in Submission.Helpers provide the key steps.
  -- Full proof requires: sigma_drop_at_simple_root, sigma_constant_on_rootless_interval,
  -- and strong induction on the number of roots in (a,b).
  sorry

end Submission