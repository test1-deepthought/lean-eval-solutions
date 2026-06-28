import ChallengeDeps
open LeanEval.Algebra
open Polynomial
open scoped Classical

set_option autoImplicit false

namespace Submission.Helpers

lemma filter_id_of_all_nonzero (xs : List ℝ) (h : ∀ a ∈ xs, a ≠ 0) : xs.filter (· ≠ 0) = xs := by
  induction' xs with a as IH
  · rfl
  · have ha : a ≠ 0 := h a (by simp)
    have has : ∀ b ∈ as, b ≠ 0 := fun b hb => h b (by simp [hb])
    have IH_as : as.filter (· ≠ 0) = as := IH has
    rw [List.filter_cons]
    have hdec : decide (a ≠ 0) = true := by simp [ha]
    rw [hdec, IH_as]
    simp

lemma signChanges_of_all_nonzero (xs : List ℝ) (h : ∀ a ∈ xs, a ≠ 0) : 
    signChanges xs = ((xs.zip xs.tail).filter (fun q : ℝ × ℝ => q.1 * q.2 < 0)).length := by
  unfold signChanges
  rw [filter_id_of_all_nonzero xs h]

lemma length_filter_cons_pair (x : ℝ × ℝ) (xs : List (ℝ × ℝ)) : 
    ((x :: xs).filter (fun q : ℝ × ℝ => q.1 * q.2 < 0)).length = 
    (if x.1 * x.2 < 0 then 1 else 0) + (xs.filter (fun q : ℝ × ℝ => q.1 * q.2 < 0)).length := by
  by_cases h : x.1 * x.2 < 0
  · simp [h]
    omega
  · simp [h]

/-- Key lemma: When the first entry of a sign list flips sign and was opposite to the second entry,
the number of sign changes changes by exactly 1. All entries must be nonzero (i.e., no chain roots at the evaluation point). -/
lemma first_flip_opposite (x y : ℝ) (tail : List ℝ) 
    (hx : x ≠ 0) (hy : y ≠ 0) (h_tail : ∀ a ∈ tail, a ≠ 0) (h_opp : x * y < 0) :
    signChanges (x :: y :: tail) - signChanges ((-x) :: y :: tail) = 1 := by
  have hall1 : ∀ a ∈ x :: y :: tail, a ≠ 0 := by
    intro a h; simp at h; rcases h with (rfl|rfl|h'); exact hx; exact hy; exact h_tail a h'
  have hall2 : ∀ a ∈ (-x) :: y :: tail, a ≠ 0 := by
    intro a h; simp at h; rcases h with (rfl|rfl|h')
    · intro hx0; apply hx; nlinarith
    · exact hy
    · exact h_tail a h'
  rw [signChanges_of_all_nonzero (x :: y :: tail) hall1,
    signChanges_of_all_nonzero ((-x) :: y :: tail) hall2]
  have hA : ((x :: y :: tail).zip (x :: y :: tail).tail) = (x, y) :: ((y :: tail).zip tail) := by simp
  have hB : (((-x) :: y :: tail).zip ((-x) :: y :: tail).tail) = ((-x), y) :: ((y :: tail).zip tail) := by simp
  rw [hA, hB]
  let Z := ((y :: tail).zip tail)
  have h1 : (((x, y) :: Z).filter (fun q : ℝ × ℝ => q.1 * q.2 < 0)).length = 
    (if x * y < 0 then 1 else 0) + (Z.filter (fun q : ℝ × ℝ => q.1 * q.2 < 0)).length := by
    apply length_filter_cons_pair (x, y) Z
  have h2 : (((-x, y) :: Z).filter (fun q : ℝ × ℝ => q.1 * q.2 < 0)).length = 
    (if (-x) * y < 0 then 1 else 0) + (Z.filter (fun q : ℝ × ℝ => q.1 * q.2 < 0)).length := by
    apply length_filter_cons_pair ((-x), y) Z
  rw [h1, h2]
  have h_not_opp : ¬((-x) * y < 0) := by nlinarith
  rw [if_pos h_opp, if_neg h_not_opp]
  omega

/-- If a polynomial has no root in (x,y) and is nonzero at x and y, then it has the same sign at x and y.
Uses the Intermediate Value Theorem. -/
lemma same_sign_of_no_root (q : ℝ[X]) {x y : ℝ} (hxy : x < y) (h : ∀ z ∈ Ioo x y, q.eval z ≠ 0) 
    (hx : q.eval x ≠ 0) (hy : q.eval y ≠ 0) : (q.eval x) * (q.eval y) > 0 := by
  by_cases hxpos : q.eval x > 0
  · by_cases hypos : q.eval y > 0
    · exact mul_pos hxpos hypos
    · have hyneg : q.eval y < 0 := by
        by_contra! hy_nonneg; exact hy (by linarith)
      have h_cont : ContinuousOn (fun t : ℝ => q.eval t) (Icc x y) :=
        (Polynomial.continuous q).continuousOn
      have h_ivt : (0 : ℝ) ∈ Ioo (q.eval y) (q.eval x) := by
        constructor <;> linarith
      have h_image := intermediate_value_Ioo' (by linarith : x ≤ y) h_cont
      have : (0 : ℝ) ∈ (fun t : ℝ => q.eval t) '' Ioo x y := h_image h_ivt
      rcases this with ⟨z, hz, hz0⟩
      exact absurd hz0 (h z hz)
  · have hxneg : q.eval x < 0 := by
      by_contra! hx_nonneg; exact hx (by linarith)
    by_cases hypos : q.eval y > 0
    · have h_cont : ContinuousOn (fun t : ℝ => q.eval t) (Icc x y) :=
        (Polynomial.continuous q).continuousOn
      have h_ivt : (0 : ℝ) ∈ Ioo (q.eval x) (q.eval y) := by
        constructor <;> linarith
      have h_image := intermediate_value_Ioo (by linarith : x ≤ y) h_cont
      have : (0 : ℝ) ∈ (fun t : ℝ => q.eval t) '' Ioo x y := h_image h_ivt
      rcases this with ⟨z, hz, hz0⟩
      exact absurd hz0 (h z hz)
    · have hyneg : q.eval y < 0 := by
        by_contra! hy_nonneg; exact hy (by linarith)
      exact mul_pos_of_neg_of_neg hxneg hyneg

/-- The Sturm chain recurrence relation: if c = -(a % b), then a = (a / b) * b - c. -/
lemma sturm_relation (a b c : ℝ[X]) (hc : c = -(a % b)) : a = (a / b) * b - c := by
  have h := EuclideanDomain.div_add_mod a b
  rw [mul_comm b (a / b)] at h
  have h_mod_eq : a % b = -c := by rw [hc, neg_neg]
  rw [h_mod_eq] at h
  calc
    a = (a / b) * b + (-c) := by symm; exact h
    _ = (a / b) * b - c := by ring

/-- At a root of p_i, the previous and next entries have opposite signs. -/
lemma eval_at_root (p_prev p_curr p_next : ℝ[X]) (r : ℝ) 
    (hrec : p_next = -(p_prev % p_curr)) (hp_curr_root : p_curr.eval r = 0) :
    p_prev.eval r = -(p_next.eval r) := by
  have h := sturm_relation p_prev p_curr p_next hrec
  have h_eval := congrArg (fun q => q.eval r) h
  simpa [eval_mul, eval_sub, hp_curr_root] using h_eval

end Submission.Helpers