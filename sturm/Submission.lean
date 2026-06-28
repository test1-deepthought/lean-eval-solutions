import ChallengeDeps
import Submission.Helpers

open LeanEval.Algebra
open Polynomial
open scoped Classical

set_option autoImplicit false

namespace Submission

lemma signChanges_flip_first_diff (a b : ℝ) (l : List ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a * b < 0) :
    LeanEval.Algebra.signChanges (a :: b :: l) = LeanEval.Algebra.signChanges ((-a) :: b :: l) + 1 := by
  have ha' : (-a) ≠ 0 := by
    intro hzero
    apply ha
    nlinarith
  have h1 : LeanEval.Algebra.signChanges (a :: b :: l) = 1 + LeanEval.Algebra.signChanges (b :: l) := by
    rw [signChanges_cons_cons a b l ha hb]
    simp [hab]
  have h2 : LeanEval.Algebra.signChanges ((-a) :: b :: l) = LeanEval.Algebra.signChanges (b :: l) := by
    rw [signChanges_cons_cons (-a) b l ha' hb]
    have hpos : (-a) * b > 0 := by nlinarith
    simp [hpos]
  rw [h1, h2]
  simp [add_comm]

theorem sturm (p : ℝ[X]) (hp : Squarefree p) {a b : ℝ} (hab : a < b)
    (ha : p.eval a ≠ 0) (hb : p.eval b ≠ 0) :
    ((p.roots.toFinset).filter (fun x => a < x ∧ x < b)).card =
      sigma p a - sigma p b := by
  -- The set of roots of p in (a,b)
  let rootsSet := ((p.roots.toFinset).filter (fun x => a < x ∧ x < b))
  -- We need to show: |rootsSet| = sigma(p,a) - sigma(p,b)
  -- We use strong induction on |rootsSet|
  revert a b hab ha hb
  refine Finset.strongInductionOn rootsSet ?_
  intro rootsSet IH a b hab ha hb hroots
  -- hroots: rootsSet = ((p.roots.toFinset).filter (fun x => a < x ∧ x < b))
  sorry

end Submission