import ChallengeDeps
import Submission.Helpers

open LeanEval.Algebra
open Polynomial
open Filter
open Set

set_option maxHeartbeats 0

namespace Submission

lemma sign_intro_neg (a : ℝ) (h : SignType.sign a = SignType.neg) : a < 0 := by
  rw [← sign_eq_neg_one_iff]; simpa using h
lemma sign_intro_pos (a : ℝ) (h : SignType.sign a = SignType.pos) : a > 0 := by
  have h' : SignType.sign a = (1 : SignType) := by simpa using h
  have := (sign_eq_one_iff (α := ℝ)).mp h'; simpa using this
lemma sign_pos_of_pos (a : ℝ) (h : a > 0) : SignType.sign a = SignType.pos := by
  have h' : SignType.sign a = (1 : SignType) := by simpa using (sign_eq_one_iff (α := ℝ)).mpr h
  simpa using h'
lemma sign_neg_of_neg (a : ℝ) (h : a < 0) : SignType.sign a = SignType.neg := by
  have h' : SignType.sign a = (-1 : SignType) := by simpa using (sign_eq_neg_one_iff (α := ℝ)).mpr h
  simpa using h'

lemma squarefree_deriv_nonzero_at_root (p : ℝ[X]) (hp : Squarefree p) (r : ℝ) (hr : p.eval r = 0) : 
    (derivative p).eval r ≠ 0 := by
  have hsep : p.Separable := (PerfectField.separable_iff_squarefree (g := p)).mpr hp
  have hcop : IsCoprime p (derivative p) := ((Polynomial.separable_def (f := p)).mp hsep)
  rcases hcop with ⟨a, b, h⟩
  have h_eval := congrArg (eval r) h
  have h_eval' : (a.eval r) * (p.eval r) + (b.eval r) * ((derivative p).eval r) = 1 := by
    simpa [eval_add, eval_mul, eval_one] using h_eval
  have h_eq : (b.eval r) * ((derivative p).eval r) = 1 := by simpa [hr] using h_eval'
  intro hzero; have hzero' : (b.eval r) * ((derivative p).eval r) = 0 := by simp [hzero]
  rw [hzero'] at h_eq; linarith

lemma sign_at_simple_root (p : ℝ[X]) (r : ℝ) (hp0 : p.eval r = 0) (hp1 : (derivative p).eval r ≠ 0) : 
    (∃ ε > 0, ∀ x, r - ε < x ∧ x < r → p.eval x * (derivative p).eval x < 0) ∧
    (∃ ε > 0, ∀ x, r < x ∧ x < r + ε → p.eval x * (derivative p).eval x > 0) := by
  have hderiv : deriv (fun (x : ℝ) => p.eval x) r = (derivative p).eval r := by simp
  have hp'_cont : ContinuousAt (fun (x : ℝ) => (derivative p).eval x) r := (derivative p).continuous.continuousAt
  by_cases hpos : (derivative p).eval r > 0
  · have hderiv_pos : deriv (fun (x : ℝ) => p.eval x) r > 0 := by rw [hderiv]; exact hpos
    have hsign := eventually_nhdsWithin_sign_eq_of_deriv_pos hderiv_pos hp0
    have hp'_near_pos : ∀ᶠ x in nhds r, (derivative p).eval x > 0 :=
      hp'_cont.eventually (lt_mem_nhds hpos)
    rcases Metric.mem_nhds_iff.mp hsign with ⟨ε₁, hε₁, hball₁⟩
    rcases Metric.mem_nhds_iff.mp hp'_near_pos with ⟨ε₂, hε₂, hball₂⟩
    let ε := min ε₁ ε₂
    have hε : ε > 0 := lt_min_iff.mpr ⟨hε₁, hε₂⟩
    have hleft : ∀ x, r - ε < x ∧ x < r → p.eval x * (derivative p).eval x < 0 := by
      intro x ⟨hx1, hx2⟩
      have hx_mem : x ∈ Metric.ball r ε := by
        rw [Metric.mem_ball, Real.dist_eq]; have hx_sub : x - r < 0 := by linarith
        have h_abs : |x - r| = -(x - r) := abs_of_neg hx_sub; rw [h_abs]; linarith
      have hx_dist : |x - r| < ε := Metric.mem_ball.mp hx_mem
      have hx_mem₁ : x ∈ Metric.ball r ε₁ := by
        rw [Metric.mem_ball, Real.dist_eq]; exact lt_of_lt_of_le hx_dist (min_le_left _ _)
      have hx_mem₂ : x ∈ Metric.ball r ε₂ := by
        rw [Metric.mem_ball, Real.dist_eq]; exact lt_of_lt_of_le hx_dist (min_le_right _ _)
      have hx_eq : SignType.sign (p.eval x) = SignType.sign (x - r) := hball₁ hx_mem₁
      have hx_pos : (derivative p).eval x > 0 := hball₂ hx_mem₂
      have hx_sub_neg : SignType.sign (x - r) = SignType.neg := sign_neg_of_neg (x - r) (sub_neg.mpr hx2)
      have hsign_p : SignType.sign (p.eval x) = SignType.neg := by rw [hx_eq, hx_sub_neg]
      have hp_val_neg : p.eval x < 0 := sign_intro_neg (p.eval x) hsign_p; nlinarith
    have hright : ∀ x, r < x ∧ x < r + ε → p.eval x * (derivative p).eval x > 0 := by
      intro x ⟨hx1, hx2⟩
      have hx_mem : x ∈ Metric.ball r ε := by
        rw [Metric.mem_ball, Real.dist_eq]; have hx_sub : x - r > 0 := by linarith
        have h_abs : |x - r| = x - r := abs_of_pos hx_sub; rw [h_abs]; linarith
      have hx_dist : |x - r| < ε := Metric.mem_ball.mp hx_mem
      have hx_mem₁ : x ∈ Metric.ball r ε₁ := by
        rw [Metric.mem_ball, Real.dist_eq]; exact lt_of_lt_of_le hx_dist (min_le_left _ _)
      have hx_mem₂ : x ∈ Metric.ball r ε₂ := by
        rw [Metric.mem_ball, Real.dist_eq]; exact lt_of_lt_of_le hx_dist (min_le_right _ _)
      have hx_eq : SignType.sign (p.eval x) = SignType.sign (x - r) := hball₁ hx_mem₁
      have hx_pos : (derivative p).eval x > 0 := hball₂ hx_mem₂
      have hx_sub_pos : SignType.sign (x - r) = SignType.pos := sign_pos_of_pos (x - r) (sub_pos.mpr hx1)
      have hsign_p : SignType.sign (p.eval x) = SignType.pos := by rw [hx_eq, hx_sub_pos]
      have hp_val_pos : p.eval x > 0 := sign_intro_pos (p.eval x) hsign_p; nlinarith
    exact ⟨⟨ε, hε, hleft⟩, ⟨ε, hε, hright⟩⟩
  · have hneg : (derivative p).eval r < 0 := by
      by_contra! H; have hle : (derivative p).eval r ≤ 0 := by linarith
      have h_eq : (derivative p).eval r = 0 := le_antisymm hle H; exact hp1 h_eq
    have hderiv_neg : deriv (fun (x : ℝ) => p.eval x) r < 0 := by rw [hderiv]; exact hneg
    have hsign := eventually_nhdsWithin_sign_eq_of_deriv_neg hderiv_neg hp0
    have hp'_near_neg : ∀ᶠ x in nhds r, (derivative p).eval x < 0 :=
      hp'_cont.eventually (gt_mem_nhds hneg)
    rcases Metric.mem_nhds_iff.mp hsign with ⟨ε₁, hε₁, hball₁⟩
    rcases Metric.mem_nhds_iff.mp hp'_near_neg with ⟨ε₂, hε₂, hball₂⟩
    let ε := min ε₁ ε₂
    have hε : ε > 0 := lt_min_iff.mpr ⟨hε₁, hε₂⟩
    have hleft : ∀ x, r - ε < x ∧ x < r → p.eval x * (derivative p).eval x < 0 := by
      intro x ⟨hx1, hx2⟩
      have hx_mem : x ∈ Metric.ball r ε := by
        rw [Metric.mem_ball, Real.dist_eq]; have hx_sub : x - r < 0 := by linarith
        have h_abs : |x - r| = -(x - r) := abs_of_neg hx_sub; rw [h_abs]; linarith
      have hx_dist : |x - r| < ε := Metric.mem_ball.mp hx_mem
      have hx_mem₁ : x ∈ Metric.ball r ε₁ := by
        rw [Metric.mem_ball, Real.dist_eq]; exact lt_of_lt_of_le hx_dist (min_le_left _ _)
      have hx_mem₂ : x ∈ Metric.ball r ε₂ := by
        rw [Metric.mem_ball, Real.dist_eq]; exact lt_of_lt_of_le hx_dist (min_le_right _ _)
      have hx_eq : SignType.sign (p.eval x) = SignType.sign (r - x) := hball₁ hx_mem₁
      have hx_neg : (derivative p).eval x < 0 := hball₂ hx_mem₂
      have hx_sub_pos : SignType.sign (r - x) = SignType.pos :=
        sign_pos_of_pos (r - x) (sub_pos.mpr (by linarith))
      have hsign_p : SignType.sign (p.eval x) = SignType.pos := by rw [hx_eq, hx_sub_pos]
      have hp_val_pos : p.eval x > 0 := sign_intro_pos (p.eval x) hsign_p; nlinarith
    have hright : ∀ x, r < x ∧ x < r + ε → p.eval x * (derivative p).eval x > 0 := by
      intro x ⟨hx1, hx2⟩
      have hx_mem : x ∈ Metric.ball r ε := by
        rw [Metric.mem_ball, Real.dist_eq]; have hx_sub : x - r > 0 := by linarith
        have h_abs : |x - r| = x - r := abs_of_pos hx_sub; rw [h_abs]; linarith
      have hx_dist : |x - r| < ε := Metric.mem_ball.mp hx_mem
      have hx_mem₁ : x ∈ Metric.ball r ε₁ := by
        rw [Metric.mem_ball, Real.dist_eq]; exact lt_of_lt_of_le hx_dist (min_le_left _ _)
      have hx_mem₂ : x ∈ Metric.ball r ε₂ := by
        rw [Metric.mem_ball, Real.dist_eq]; exact lt_of_lt_of_le hx_dist (min_le_right _ _)
      have hx_eq : SignType.sign (p.eval x) = SignType.sign (r - x) := hball₁ hx_mem₁
      have hx_neg : (derivative p).eval x < 0 := hball₂ hx_mem₂
      have hx_sub_neg : SignType.sign (r - x) = SignType.neg :=
        sign_neg_of_neg (r - x) (sub_neg.mpr (by linarith))
      have hsign_p : SignType.sign (p.eval x) = SignType.neg := by rw [hx_eq, hx_sub_neg]
      have hp_val_neg : p.eval x < 0 := sign_intro_neg (p.eval x) hsign_p; nlinarith
    exact ⟨⟨ε, hε, hleft⟩, ⟨ε, hε, hright⟩⟩

-- The main theorem: Count roots via Sturm sign changes
theorem sturm (p : ℝ[X]) (hp : Squarefree p) {a b : ℝ} (hab : a < b)
    (ha : p.eval a ≠ 0) (hb : p.eval b ≠ 0) :
    ((p.roots.toFinset).filter (fun x => a < x ∧ x < b)).card =
      sigma p a - sigma p b := by
  have hp_simple : ∀ r, p.eval r = 0 → (derivative p).eval r ≠ 0 :=
    fun r hr => squarefree_deriv_nonzero_at_root p hp r hr
  
  -- We prove the theorem by showing that sigma(p,a) - sigma(p,b) counts the roots
  -- Key idea: define f(c) = sigma(p,c) - (#roots of p in (c,b))
  -- Show f is constant on (a,b), then evaluate at c=a and c=b
  
  -- First, compute #roots in (a,b)
  let N := ((p.roots.toFinset).filter (fun x => a < x ∧ x < b)).card
  
  -- We'll prove the equivalent statement: sigma p a = N + sigma p b
  have h_eq : sigma p a = N + sigma p b := by
    -- By well-founded induction on the number of roots between a and b
    -- For the base case (no roots): sigma is constant on (a,b), so sigma a = sigma b
    -- For the inductive step: the largest root r contributes 1 to the drop
    
    -- Use the set of roots sorted
    let roots := ((p.roots.toFinset).filter (fun x => a < x ∧ x < b)).toList
    
    -- We'll use induction on the length of roots list
    induction' roots with r rs ih generalizing a
    · -- No roots case: show sigma p a = sigma p b
      -- On (a,b), p has no roots, and the sign change count is constant
      -- because p doesn't change sign, and other chain entries don't change the count
      -- For now, use ha, hb and continuity
      
      -- Since there are no roots, sigma should be constant on [a,b]
      -- We need: ∀ x ∈ Ioo a b, p.eval x ≠ 0 (no roots)
      have h_no_root : ∀ x ∈ Ioo a b, p.eval x ≠ 0 := by
        intro x ⟨hx1, hx2⟩
        intro hzero
        have hx_mem : x ∈ p.roots := by
          rw [Polynomial.mem_roots (Polynomial.ne_zero_of_squarefree hp), hr]
          exact hzero
        have hx_in_set : x ∈ (p.roots.toFinset).filter (fun x => a < x ∧ x < b) := by
          refine Finset.mem_filter.mpr ⟨Finset.mem_coe.mpr hx_mem, hx1, hx2⟩
        have hx_in_roots : x ∈ roots := by
          simpa [roots] using hx_in_set
        -- But roots is empty (induction base case), contradiction
        have : roots = [] := rfl
        simp [this] at hx_in_roots
      
      -- Now we argue that sigma is constant on [a,b] when there are no p-roots
      -- This requires showing that non-p chain roots don't change sigma
      -- For the purpose of this proof, we use the following argument:
      -- The Sturm chain has the property that if p has no roots in (a,b),
      -- then sigma(p,a) = sigma(p,b)
      
      -- We need to fill this in properly
      sorry
    · -- At least one root r in the list
      -- r is the smallest root of p in (a,b)
      -- We split: (a,r) has no roots, and (r,b) has the rest
      -- By induction on rs (the rest), sigma(p,a) = sigma(p,r⁻) ... 
      sorry
    
  -- From h_eq: sigma p a = N + sigma p b
  -- So sigma p a - sigma p b = N
  omega

end Submission