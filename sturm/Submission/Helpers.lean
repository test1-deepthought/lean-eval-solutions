import Mathlib
open Polynomial
open scoped Classical

set_option autoImplicit false

namespace Submission.Helpers

lemma eval_mod_eq_eval_of_root (f g : ℝ[X]) (r : ℝ) (hg : g.eval r = 0) : (f % g).eval r = f.eval r := by
  have h := EuclideanDomain.mod_add_div f g
  calc
    (f % g).eval r = ((f % g) + g * (f / g) - g * (f / g)).eval r := by simp
    _ = (f - g * (f / g)).eval r := by rw [h]
    _ = f.eval r - (g * (f / g)).eval r := by simp
    _ = f.eval r - (g.eval r * ((f / g).eval r)) := by simp
    _ = f.eval r := by simp [hg]

lemma sturm_adjacent_opposite (f g : ℝ[X]) (r : ℝ) (hg : g.eval r = 0) (hf : f.eval r ≠ 0) :
    f.eval r * (-(f % g)).eval r < 0 := by
  have h := eval_mod_eq_eval_of_root f g r hg
  have hneg : (-(f % g)).eval r = -(f.eval r) := by
    calc
      (-(f % g)).eval r = -((f % g).eval r) := by simp
      _ = -(f.eval r) := by rw [h]
  rw [hneg]
  have hsq : (f.eval r)^2 > 0 := sq_pos_iff.mpr hf
  nlinarith

end Submission.Helpers