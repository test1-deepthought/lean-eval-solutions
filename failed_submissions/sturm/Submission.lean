import ChallengeDeps
import Submission.Helpers

open LeanEval.Algebra
open Polynomial
open scoped Classical

namespace Submission

lemma squarefree_imp_separable (p : ℝ[X]) (hp : Squarefree p) : Separable p :=
  ((PerfectField.separable_iff_squarefree (K := ℝ) (g := p)).mpr hp)

theorem sturm (p : ℝ[X]) (hp : Squarefree p) {a b : ℝ} (hab : a < b)
    (ha : p.eval a ≠ 0) (hb : p.eval b ≠ 0) :
    ((p.roots.toFinset).filter (fun x => a < x ∧ x < b)).card =
      sigma p a - sigma p b := by
  have hsep : Separable p := squarefree_imp_separable p hp
  have h_nodup : p.roots.Nodup := Polynomial.nodup_roots hsep
  sorry

end Submission
