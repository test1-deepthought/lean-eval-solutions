import ChallengeDeps
open LeanEval.Algebra
open Polynomial
open scoped Classical

set_option autoImplicit false

namespace Submission.Helpers

lemma filter_len_one_case1 (a b : ℝ) (h_ab : a * b < 0) (h_not : ¬(b * (-a) < 0)) :
    (List.filter (fun q : ℝ × ℝ => q.1 * q.2 < 0) [(a, b), (b, -a)]).length = 1 := by
  simp only [List.filter_cons, List.filter_nil]
  by_cases h1 : a * b < 0
  · rw [decide_eq_true h1]; simp; nlinarith
  · exfalso; exact h1 h_ab

lemma filter_len_one_case2 (a b : ℝ) (h_not_ab : ¬(a * b < 0)) (h_kept : (b * (-a) < 0)) :
    (List.filter (fun q : ℝ × ℝ => q.1 * q.2 < 0) [(a, b), (b, -a)]).length = 1 := by
  simp only [List.filter_cons, List.filter_nil]
  by_cases h1 : a * b < 0
  · exfalso; exact h_not_ab h1
  · rw [decide_eq_false h1]; simp
    have h_pos : 0 < b * a := by nlinarith
    simp [h_pos]

/-- For any real a ≠ 0 and any b, the triple [a, b, -a] has exactly 1 sign change.
This is the key combinatorial lemma for Sturm's theorem. -/
lemma triple_signChanges_one (a b : ℝ) (ha : a ≠ 0) : signChanges [a, b, -a] = 1 := by
  unfold signChanges
  dsimp
  by_cases hb : b = 0
  · subst hb; simp [ha]
  · simp [ha, hb]
    have h_ab_cases : a * b < 0 ∨ 0 < a * b := by
      have h_ne : a * b ≠ 0 := mul_ne_zero ha hb
      exact lt_or_gt_of_ne h_ne
    rcases h_ab_cases with (h_ab | h_ab)
    · have h_not : ¬(b * (-a) < 0) := by
        have : b * (-a) = -(a * b) := by ring
        rw [this]; nlinarith
      exact filter_len_one_case1 a b h_ab h_not
    · have h_kept : b * (-a) < 0 := by
        have : b * (-a) = -(a * b) := by ring
        rw [this]; nlinarith
      have h_not_ab : ¬(a * b < 0) := by nlinarith
      exact filter_len_one_case2 a b h_not_ab h_kept

end Submission.Helpers