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
  -- Sturm's theorem: formal proof incomplete.
  -- See failed_submissions/sturm/report.md for detailed status.
  sorry

end Submission