import ChallengeDeps

open LeanEval.Algebra
open Polynomial
open Set
open scoped Classical

set_option autoImplicit false

namespace Submission.Helpers

lemma signChanges_nil : signChanges ([] : List ℝ) = 0 := by
  unfold signChanges; simp

lemma signChanges_singleton (a : ℝ) : signChanges [a] = 0 := by
  unfold signChanges
  by_cases ha : a = 0
  · subst a; simp
  · simp [ha]

lemma signChanges_cons_cons_nonzero (a b : ℝ) (rest : List ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    signChanges (a :: b :: rest) = (if a * b < 0 then 1 else 0) + signChanges (b :: rest) := by
  unfold signChanges; simp [ha, hb]
  by_cases h : a * b < 0
  · simp [h, add_comm]
  · simp [h]

lemma signChanges_splice_zero (xs ys : List ℝ) : signChanges (xs ++ [0] ++ ys) = signChanges (xs ++ ys) := by
  unfold signChanges; simp

lemma signChanges_pair (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) : signChanges [a, b] = if a * b < 0 then 1 else 0 := by
  calc
    signChanges [a, b] = (if a * b < 0 then 1 else 0) + signChanges [b] := by
      simpa using signChanges_cons_cons_nonzero a b [] ha hb
    _ = (if a * b < 0 then 1 else 0) + 0 := by simp [signChanges_singleton]
    _ = if a * b < 0 then 1 else 0 := by simp

lemma triple_sign_lemma (a b c : ℝ) (hac : a * c < 0) (hb : b ≠ 0) :
    ((if a * b < 0 then 1 else 0 : ℕ) + (if b * c < 0 then 1 else 0 : ℕ)) = 1 := by
  by_cases ha0 : a = 0
  · subst ha0; simp at hac
  by_cases hc0 : c = 0
  · subst hc0; simp at hac
  have ha0' : 0 ≠ a := Ne.symm ha0
  have hc0' : 0 ≠ c := Ne.symm hc0
  have hb_symm : 0 ≠ b := Ne.symm hb
  have ha_sign : a > 0 ∨ a < 0 := lt_or_gt_of_ne ha0'
  have hb_sign : b > 0 ∨ b < 0 := lt_or_gt_of_ne hb_symm
  have hc_sign : c > 0 ∨ c < 0 := lt_or_gt_of_ne hc0'
  rcases ha_sign with (ha_pos | ha_neg)
  · rcases hc_sign with (hc_pos | hc_neg)
    · nlinarith
    · rcases hb_sign with (hb_pos | hb_neg)
      · have h_ab : ¬(a * b < 0) := by nlinarith
        have h_bc : b * c < 0 := by nlinarith
        have h1 : (if a * b < 0 then (1 : ℕ) else 0) = 0 := by simp [h_ab]
        have h2 : (if b * c < 0 then (1 : ℕ) else 0) = 1 := by simp [h_bc]
        calc ((if a * b < 0 then 1 else 0 : ℕ) + (if b * c < 0 then 1 else 0 : ℕ)) = (0 : ℕ) + (1 : ℕ) := by simp [h1, h2]
          _ = 1 := by simp
      · have h_ab : a * b < 0 := by nlinarith
        have h_bc : ¬(b * c < 0) := by nlinarith
        have h1 : (if a * b < 0 then (1 : ℕ) else 0) = 1 := by simp [h_ab]
        have h2 : (if b * c < 0 then (1 : ℕ) else 0) = 0 := by simp [h_bc]
        calc ((if a * b < 0 then 1 else 0 : ℕ) + (if b * c < 0 then 1 else 0 : ℕ)) = (1 : ℕ) + (0 : ℕ) := by simp [h1, h2]
          _ = 1 := by simp
  · rcases hc_sign with (hc_pos | hc_neg)
    · rcases hb_sign with (hb_pos | hb_neg)
      · have h_ab : a * b < 0 := by nlinarith
        have h_bc : ¬(b * c < 0) := by nlinarith
        have h1 : (if a * b < 0 then (1 : ℕ) else 0) = 1 := by simp [h_ab]
        have h2 : (if b * c < 0 then (1 : ℕ) else 0) = 0 := by simp [h_bc]
        calc ((if a * b < 0 then 1 else 0 : ℕ) + (if b * c < 0 then 1 else 0 : ℕ)) = (1 : ℕ) + (0 : ℕ) := by simp [h1, h2]
          _ = 1 := by simp
      · have h_ab : ¬(a * b < 0) := by nlinarith
        have h_bc : b * c < 0 := by nlinarith
        have h1 : (if a * b < 0 then (1 : ℕ) else 0) = 0 := by simp [h_ab]
        have h2 : (if b * c < 0 then (1 : ℕ) else 0) = 1 := by simp [h_bc]
        calc ((if a * b < 0 then 1 else 0 : ℕ) + (if b * c < 0 then 1 else 0 : ℕ)) = (0 : ℕ) + (1 : ℕ) := by simp [h1, h2]
          _ = 1 := by simp
    · nlinarith

lemma signChanges_triple_opposite (a b c : ℝ) (hac : a * c < 0) : signChanges [a, b, c] = 1 := by
  have ha_ne_zero : a ≠ 0 := by intro hzero; subst hzero; nlinarith
  have hc_ne_zero : c ≠ 0 := by intro hzero; subst hzero; nlinarith
  by_cases hb_zero : b = 0
  · subst hb_zero
    calc
      signChanges [a, 0, c] = signChanges ([a] ++ [0] ++ [c]) := rfl
      _ = signChanges ([a] ++ [c]) := by simpa using signChanges_splice_zero [a] [c]
      _ = signChanges [a, c] := by simp
      _ = 1 := by
        have h := signChanges_pair a c ha_ne_zero hc_ne_zero
        simp [hac, h]
  · have h_sum : ((if a * b < 0 then 1 else 0 : ℕ) + (if b * c < 0 then 1 else 0 : ℕ)) = 1 := triple_sign_lemma a b c hac hb_zero
    calc
      signChanges [a, b, c] = signChanges (a :: b :: [c]) := rfl
      _ = (if a * b < 0 then 1 else 0 : ℕ) + signChanges (b :: [c]) := by
        simpa using signChanges_cons_cons_nonzero a b [c] ha_ne_zero hb_zero
      _ = (if a * b < 0 then 1 else 0 : ℕ) + (if b * c < 0 then 1 else 0 : ℕ) := by
        simp [signChanges_pair, hc_ne_zero, hb_zero]
      _ = 1 := h_sum

lemma signChanges_flip_first_diff (a b : ℝ) (l : List ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a * b < 0) :
    signChanges (a :: b :: l) = signChanges ((-a) :: b :: l) + 1 := by
  have ha' : (-a) ≠ 0 := by intro hzero; apply ha; nlinarith
  have h1 : signChanges (a :: b :: l) = 1 + signChanges (b :: l) := by
    rw [signChanges_cons_cons_nonzero a b l ha hb]; simp [hab]
  have h2 : signChanges ((-a) :: b :: l) = signChanges (b :: l) := by
    rw [signChanges_cons_cons_nonzero (-a) b l ha' hb]
    split_ifs with h
    · exfalso; nlinarith
    · simp
  rw [h1, h2]; omega

lemma eval_remainder_at_root (a b : ℝ[X]) (r : ℝ) (hb : b.eval r = 0) : (a % b).eval r = a.eval r := by
  have h := EuclideanDomain.mod_add_div a b
  apply_fun (·.eval r) at h
  simp [eval_add, eval_mul, hb] at h; exact h

lemma squarefree_imp_separable (p : ℝ[X]) (hp : Squarefree p) : Separable p := by
  haveI : CharZero ℝ := by infer_instance
  haveI : PerfectField ℝ := PerfectField.ofCharZero
  rw [PerfectField.separable_iff_squarefree]; exact hp

lemma eval_derivative_ne_zero_of_squarefree_root (p : ℝ[X]) (hp : Squarefree p) (r : ℝ) (hr : p.eval r = 0) :
    p.derivative.eval r ≠ 0 := by
  have hsep : Separable p := squarefree_imp_separable p hp
  have hx : (aeval r) p = 0 := by simpa using hr
  have h := hsep.aeval_derivative_ne_zero (x := r) hx
  simpa using h

lemma factor_theorem_with_deriv (p : ℝ[X]) (r : ℝ) (hp0 : p.eval r = 0) : ∃ q : ℝ[X], p = (X - C r) * q ∧ q.eval r = (derivative p).eval r := by
  have hfactor : (X - C r) ∣ p := by rw [Polynomial.dvd_iff_isRoot]; exact hp0
  rcases hfactor with ⟨q, hpq⟩
  refine ⟨q, hpq, ?_⟩
  have hderiv : derivative p = q + (X - C r) * derivative q := by
    rw [hpq, derivative_mul, derivative_sub, derivative_X, derivative_C]; ring
  calc q.eval r = (q + (X - C r) * derivative q).eval r := by simp
    _ = (derivative p).eval r := by rw [hderiv]

lemma nonzero_near (q : ℝ[X]) (r : ℝ) (hq : q.eval r ≠ 0) : ∃ ε > 0, ∀ x, |x - r| < ε → q.eval x ≠ 0 := by
  have hcont : Continuous (q.eval : ℝ → ℝ) := Polynomial.continuous q
  have hcont_at : ContinuousAt (q.eval : ℝ → ℝ) r := hcont.continuousAt
  have hevent : ∀ᶠ x in nhds r, q.eval x ≠ 0 := hcont_at.tendsto.eventually_ne hq
  rcases Metric.mem_nhds_iff.mp hevent with ⟨ε, hε, hball⟩
  refine ⟨ε, hε, ?_⟩
  intro x hx_dist; apply hball; rw [Metric.mem_ball, Real.dist_eq]; exact hx_dist

lemma sign_constant_on_Ioo (q : ℝ[X]) (c d : ℝ) (hcd : c < d) (h_no_root : ∀ x ∈ Ioo c d, q.eval x ≠ 0) :
    (∀ x ∈ Ioo c d, q.eval x > 0) ∨ (∀ x ∈ Ioo c d, q.eval x < 0) := by
  have h_cont : Continuous (q.eval : ℝ → ℝ) := Polynomial.continuous q
  by_cases hpos : ∃ x ∈ Ioo c d, q.eval x > 0
  · rcases hpos with ⟨x, hx, hxpos⟩; refine Or.inl ?_
    intro y hy; by_contra! h_notpos
    have hy_nonzero : q.eval y ≠ 0 := h_no_root y hy
    have hy_neg : q.eval y < 0 := by
      have : q.eval y ≤ 0 := h_notpos; exact Ne.lt_of_le hy_nonzero this
    by_cases hxy : x < y
    · have h_cont_on : ContinuousOn (q.eval : ℝ → ℝ) (Icc x y) := h_cont.continuousOn
      have h0_in : (0 : ℝ) ∈ Ioo (q.eval y) (q.eval x) := by constructor <;> linarith
      have h_contains : Ioo (q.eval y) (q.eval x) ⊆ (q.eval : ℝ → ℝ) '' Ioo x y :=
        intermediate_value_Ioo' (by linarith) h_cont_on
      rcases h_contains h0_in with ⟨z, hz, hz0⟩
      apply h_no_root z; · rcases hz with ⟨hzx, hzy⟩; exact ⟨lt_of_lt_of_le hx.1 hzx.le, lt_of_le_of_lt hzy.le hy.2⟩
      · exact hz0
    · have hy_ne_x : y ≠ x := by intro h_eq; subst h_eq; linarith
      have hyx : y < x := by
        have hy_le_x : y ≤ x := by linarith
        exact Ne.lt_of_le hy_ne_x hy_le_x
      have h_cont_on : ContinuousOn (q.eval : ℝ → ℝ) (Icc y x) := h_cont.continuousOn
      have h0_in : (0 : ℝ) ∈ Ioo (q.eval y) (q.eval x) := by constructor <;> linarith
      have h_contains : Ioo (q.eval y) (q.eval x) ⊆ (q.eval : ℝ → ℝ) '' Ioo y x :=
        intermediate_value_Ioo (by linarith) h_cont_on
      rcases h_contains h0_in with ⟨z, hz, hz0⟩
      apply h_no_root z; · rcases hz with ⟨hzy, hzx⟩; exact ⟨lt_of_lt_of_le hy.1 hzy.le, lt_of_le_of_lt hzx.le hx.2⟩
      · exact hz0
  · refine Or.inr ?_
    intro y hy; have hy_nonzero : q.eval y ≠ 0 := h_no_root y hy
    have hy_nonpos : q.eval y ≤ 0 := by by_contra! hpos_y; exact hpos ⟨y, hy, hpos_y⟩
    exact Ne.lt_of_le hy_nonzero hy_nonpos

end Submission.Helpers