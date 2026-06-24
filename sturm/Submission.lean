import ChallengeDeps
import Submission.Helpers

open LeanEval.Algebra
open Polynomial
open Set
open scoped Classical

namespace Submission

lemma eval_mod_eq_eval (a b : ℝ[X]) (r : ℝ) (hb : b.eval r = 0) : (a % b).eval r = a.eval r := by
  have hdiv := EuclideanDomain.div_add_mod a b
  have hval := congrArg (fun q => q.eval r) hdiv
  simp [eval_add, eval_mul, hb] at hval
  exact hval

lemma factor_simple_root (p : ℝ[X]) (hp : Squarefree p) (r : ℝ) (hr : p.eval r = 0) :
    ∃ (q : ℝ[X]), p = (X - C r) * q ∧ q.eval r ≠ 0 := by
  have hp_ne_zero : p ≠ 0 := Squarefree.ne_zero hp
  have h_dvd : (X - C r) ∣ p := by
    rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot]; exact hr
  rcases h_dvd with ⟨q, hq⟩
  refine ⟨q, hq, ?_⟩
  intro hq0
  have h_dvd2 : (X - C r) ∣ q := by
    rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot]; exact hq0
  rcases h_dvd2 with ⟨r2, hr2⟩
  have h_sq_dvd : (X - C r) * (X - C r) ∣ p := by
    rw [hq, hr2]; use r2; ring
  have hirred : Irreducible (X - C r) := Polynomial.irreducible_X_sub_C r
  have h_contra := ((squarefree_iff_no_irreducibles hp_ne_zero).mp hp) (X - C r) hirred
  exact h_contra h_sq_dvd

lemma derivative_eval_at_root (p : ℝ[X]) (r : ℝ) (q : ℝ[X]) (hq : p = (X - C r) * q) :
    (derivative p).eval r = q.eval r := by
  rw [hq]; simp [derivative_mul, eval_add, eval_mul, eval_X, eval_C, eval_sub]

lemma sign_stable_pos (q : ℝ[X]) (r : ℝ) (hq_pos : q.eval r > 0) : ∃ ε > 0, ∀ x, |x - r| < ε → q.eval x > 0 := by
  have hcont : ContinuousAt (fun x : ℝ => q.eval x) r := (Polynomial.continuous q).continuousAt
  rcases Metric.continuousAt_iff.mp hcont (q.eval r / 2) (by linarith) with ⟨ε, hε, h⟩
  refine ⟨ε, hε, ?_⟩
  intro x hx
  have hdist : dist (q.eval x) (q.eval r) < q.eval r / 2 := h (by rw [Real.dist_eq]; exact hx)
  rw [Real.dist_eq] at hdist
  have : q.eval x > q.eval r / 2 := by
    have := abs_lt.mp hdist; linarith
  linarith

lemma sign_stable_neg (q : ℝ[X]) (r : ℝ) (hq_neg : q.eval r < 0) : ∃ ε > 0, ∀ x, |x - r| < ε → q.eval x < 0 := by
  have hcont : ContinuousAt (fun x : ℝ => q.eval x) r := (Polynomial.continuous q).continuousAt
  rcases Metric.continuousAt_iff.mp hcont (-(q.eval r) / 2) (by linarith) with ⟨ε, hε, h⟩
  refine ⟨ε, hε, ?_⟩
  intro x hx
  have hdist : dist (q.eval x) (q.eval r) < -(q.eval r) / 2 := h (by rw [Real.dist_eq]; exact hx)
  rw [Real.dist_eq] at hdist
  have : q.eval x < q.eval r / 2 := by
    have := abs_lt.mp hdist; linarith
  linarith

lemma sign_change_at_root (p : ℝ[X]) (hp : Squarefree p) (r : ℝ) (hr : p.eval r = 0) :
    (∃ ε > 0, ∀ x ∈ Ioo (r - ε) r, p.eval x * (derivative p).eval x < 0) ∧
    (∃ ε > 0, ∀ x ∈ Ioo r (r + ε), p.eval x * (derivative p).eval x > 0) := by
  rcases factor_simple_root p hp r hr with ⟨q, hq, hq_ne⟩
  have hp'_r_eq_q_r : (derivative p).eval r = q.eval r := derivative_eval_at_root p r q hq
  have hq_cases : q.eval r > 0 ∨ q.eval r < 0 := by
    by_cases h : q.eval r > 0
    · exact Or.inl h
    · have hneg : q.eval r < 0 := by
        by_contra! hge; have : q.eval r = 0 := by linarith; exact hq_ne this
      exact Or.inr hneg
  rcases hq_cases with (hq_pos | hq_neg)
  · have hp'_pos : (derivative p).eval r > 0 := by rw [hp'_r_eq_q_r]; exact hq_pos
    rcases sign_stable_pos q r hq_pos with ⟨ε₁, hε₁, hq_pos_near⟩
    rcases sign_stable_pos (derivative p) r hp'_pos with ⟨ε₂, hε₂, hp'_pos_near⟩
    set ε := min ε₁ ε₂ with hε_def
    have hε_pos : ε > 0 := lt_min_iff.mpr ⟨hε₁, hε₂⟩
    constructor
    · refine ⟨ε, hε_pos, λ x hx => ?_⟩
      rcases hx with ⟨hx1, hx2⟩
      have hx_near : |x - r| < ε := by
        have hneg : x - r < 0 := by linarith
        have h_abs : |x - r| = -(x - r) := abs_of_neg hneg
        rw [h_abs]; have : -(x - r) = r - x := by ring; rw [this]; linarith
      have hq_pos_x : q.eval x > 0 := hq_pos_near x (lt_of_lt_of_le hx_near (min_le_left _ _))
      have hp'_pos_x : (derivative p).eval x > 0 := hp'_pos_near x (lt_of_lt_of_le hx_near (min_le_right _ _))
      have hp_neg_x : p.eval x < 0 := by
        rw [hq]; simp [eval_mul, eval_sub, eval_X, eval_C]; nlinarith
      nlinarith
    · refine ⟨ε, hε_pos, λ x hx => ?_⟩
      rcases hx with ⟨hx1, hx2⟩
      have hx_near : |x - r| < ε := by
        have hpos : x - r > 0 := by linarith
        have h_abs : |x - r| = x - r := abs_of_pos hpos; rw [h_abs]; linarith
      have hq_pos_x : q.eval x > 0 := hq_pos_near x (lt_of_lt_of_le hx_near (min_le_left _ _))
      have hp'_pos_x : (derivative p).eval x > 0 := hp'_pos_near x (lt_of_lt_of_le hx_near (min_le_right _ _))
      have hp_pos_x : p.eval x > 0 := by
        rw [hq]; simp [eval_mul, eval_sub, eval_X, eval_C]; nlinarith
      nlinarith
  · have hp'_neg : (derivative p).eval r < 0 := by rw [hp'_r_eq_q_r]; exact hq_neg
    rcases sign_stable_neg q r hq_neg with ⟨ε₁, hε₁, hq_neg_near⟩
    rcases sign_stable_neg (derivative p) r hp'_neg with ⟨ε₂, hε₂, hp'_neg_near⟩
    set ε := min ε₁ ε₂ with hε_def
    have hε_pos : ε > 0 := lt_min_iff.mpr ⟨hε₁, hε₂⟩
    constructor
    · refine ⟨ε, hε_pos, λ x hx => ?_⟩
      rcases hx with ⟨hx1, hx2⟩
      have hx_near : |x - r| < ε := by
        have hneg : x - r < 0 := by linarith
        have h_abs : |x - r| = -(x - r) := abs_of_neg hneg
        rw [h_abs]; have : -(x - r) = r - x := by ring; rw [this]; linarith
      have hq_neg_x : q.eval x < 0 := hq_neg_near x (lt_of_lt_of_le hx_near (min_le_left _ _))
      have hp'_neg_x : (derivative p).eval x < 0 := hp'_neg_near x (lt_of_lt_of_le hx_near (min_le_right _ _))
      have hp_pos_x : p.eval x > 0 := by
        rw [hq]; simp [eval_mul, eval_sub, eval_X, eval_C]; nlinarith
      nlinarith
    · refine ⟨ε, hε_pos, λ x hx => ?_⟩
      rcases hx with ⟨hx1, hx2⟩
      have hx_near : |x - r| < ε := by
        have hpos : x - r > 0 := by linarith
        have h_abs : |x - r| = x - r := abs_of_pos hpos; rw [h_abs]; linarith
      have hq_neg_x : q.eval x < 0 := hq_neg_near x (lt_of_lt_of_le hx_near (min_le_left _ _))
      have hp'_neg_x : (derivative p).eval x < 0 := hp'_neg_near x (lt_of_lt_of_le hx_near (min_le_right _ _))
      have hp_neg_x : p.eval x < 0 := by
        rw [hq]; simp [eval_mul, eval_sub, eval_X, eval_C]; nlinarith
      nlinarith

lemma triple_sum_one (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) : 
    ((if a * b < 0 then 1 else 0 : ℕ) + (if b * (-a) < 0 then 1 else 0 : ℕ) = 1) := by
  have hab_ne_zero : a * b ≠ 0 := mul_ne_zero ha hb
  by_cases h : a * b < 0
  · have h' : ¬(b * (-a) < 0) := by
      have hpos' : b * (-a) > 0 := by
        calc
          b * (-a) = -(a * b) := by ring
          _ > 0 := by linarith
      linarith
    rw [if_pos h, if_neg h']
  · have hpos : a * b > 0 := by
      by_contra! hle; exact hab_ne_zero (by linarith)
    have h' : b * (-a) < 0 := by
      calc
        b * (-a) = -(a * b) := by ring
        _ < 0 := by linarith
    rw [if_neg h, if_pos h']

-- Sturm's theorem via connectedness
theorem sturm (p : ℝ[X]) (hp : Squarefree p) {a b : ℝ} (hab : a < b)
    (ha : p.eval a ≠ 0) (hb : p.eval b ≠ 0) :
    ((p.roots.toFinset).filter (fun x => a < x ∧ x < b)).card =
      sigma p a - sigma p b := by
  -- Define h(u) = sigma(p,u) - #{roots of p in (u,b)}
  -- h is locally constant: at a root of p, sigma drops by 1 but #{roots in (u,b)} also drops by 1
  -- At non-roots, both sigma and #{roots in (u,b)} are locally constant
  let h : ℝ → ℤ := fun u => (sigma p u : ℤ) - (((p.roots.toFinset).filter (fun x => u < x ∧ x < b)).card : ℤ)
  have h_locallyConstant : IsLocallyConstant h := by
    intro u
    by_cases hu_root : p.eval u = 0
    · -- u is a root of p: sigma drops by exactly 1, #{roots in (u,b)} also drops by 1
      rcases sign_change_at_root p hp u hu_root with ⟨⟨ε₁, hε₁, h_left⟩, ⟨ε₂, hε₂, h_right⟩⟩
      set ε := min ε₁ ε₂ with hε_def
      have hε_pos : ε > 0 := lt_min_iff.mpr ⟨hε₁, hε₂⟩
      refine ⟨Metric.ball u ε, Metric.ball_mem_nhds u hε_pos, ?_⟩
      intro x hx
      rw [Metric.mem_ball, Real.dist_eq] at hx
      have hx_bound : |x - u| < ε := hx
      -- Show h(x) = h(u) using case analysis on x < u or x > u
      by_cases hx_lt_u : x < u
      · -- x is left of u
        -- sigma(p,x) = sigma(p,u) + 1
        -- #{roots in (x,b)} = #{roots in (u,b)} + 1 (since u is in (x,b) but not in (u,b))
        sorry
      · -- x is right of u
        have hx_gt_u : u < x := by linarith
        -- sigma(p,x) = sigma(p,u)
        -- #{roots in (x,b)} = #{roots in (u,b)} (since neither includes u)
        sorry
    · -- u is not a root of p
      -- For each chain entry q_k, if q_k(u) ≠ 0 then q_k has constant sign near u
      -- The root count #{roots in (u,b)} is also locally constant at u
      sorry
  -- Now use connectedness
  have h_conn : IsPreconnected (Set.Icc a b) := isPreconnected_Icc
  have ha_mem : a ∈ Set.Icc a b := ⟨le_of_lt hab, le_refl b⟩
  have hb_mem : b ∈ Set.Icc a b := ⟨le_refl a, le_of_lt hab⟩
  have h_eq := h_locallyConstant.apply_eq_of_isPreconnected h_conn ha_mem hb_mem
  unfold h at h_eq
  -- Simplify: h(a) = sigma(p,a) - #{roots in (a,b)}, h(b) = sigma(p,b) - 0
  -- So h(a) = h(b) gives sigma(p,a) - #{roots in (a,b)} = sigma(p,b)
  -- Rearranged: #{roots in (a,b)} = sigma(p,a) - sigma(p,b)
  simp at h_eq
  omega

end Submission