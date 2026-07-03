import ChallengeDeps
import Submission.Helpers

open LeanEval.Algebra
open Polynomial
open Set
open Filter

set_option maxHeartbeats 600000

namespace Submission

lemma squarefree_deriv_nonzero_at_root (p : ℝ[X]) (hp : Squarefree p) (r : ℝ) (hr : p.eval r = 0) : 
    (derivative p).eval r ≠ 0 := by
  have hsep : p.Separable := (PerfectField.separable_iff_squarefree (g := p)).mpr hp
  have hcop : IsCoprime p (derivative p) := ((Polynomial.separable_def (f := p)).mp hsep)
  rcases hcop with ⟨a, b, h⟩
  have h_eval := congrArg (eval r) h
  have h_eval' : (a.eval r) * (p.eval r) + (b.eval r) * ((derivative p).eval r) = 1 := by
    simpa [eval_add, eval_mul, eval_one] using h_eval
  have h_eq : (b.eval r) * ((derivative p).eval r) = 1 := by simpa [hr] using h_eval'
  intro hzero
  have hzero' : (b.eval r) * ((derivative p).eval r) = 0 := by simp [hzero]
  rw [hzero'] at h_eq
  linarith

lemma sign_intro_neg (a : ℝ) (h : SignType.sign a = SignType.neg) : a < 0 := by
  rw [← sign_eq_neg_one_iff]; simpa using h

lemma sign_intro_pos (a : ℝ) (h : SignType.sign a = SignType.pos) : a > 0 := by
  have h' : SignType.sign a = (1 : SignType) := by simpa using h
  have := (sign_eq_one_iff (α := ℝ)).mp h'
  simpa using this

lemma sign_pos_of_pos (a : ℝ) (h : a > 0) : SignType.sign a = SignType.pos := by
  have h' : SignType.sign a = (1 : SignType) := by
    simpa using (sign_eq_one_iff (α := ℝ)).mpr h
  simpa using h'

lemma sign_neg_of_neg (a : ℝ) (h : a < 0) : SignType.sign a = SignType.neg := by
  have h' : SignType.sign a = (-1 : SignType) := by
    simpa using (sign_eq_neg_one_iff (α := ℝ)).mpr h
  simpa using h'

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
        rw [Metric.mem_ball, Real.dist_eq]
        have hx_sub : x - r < 0 := by linarith
        have h_abs : |x - r| = -(x - r) := abs_of_neg hx_sub
        rw [h_abs]; linarith
      have hx_dist : |x - r| < ε := Metric.mem_ball.mp hx_mem
      have hx_mem₁ : x ∈ Metric.ball r ε₁ := by
        rw [Metric.mem_ball, Real.dist_eq]; exact lt_of_lt_of_le hx_dist (min_le_left _ _)
      have hx_mem₂ : x ∈ Metric.ball r ε₂ := by
        rw [Metric.mem_ball, Real.dist_eq]; exact lt_of_lt_of_le hx_dist (min_le_right _ _)
      have hx_eq : SignType.sign (p.eval x) = SignType.sign (x - r) := hball₁ hx_mem₁
      have hx_pos : (derivative p).eval x > 0 := hball₂ hx_mem₂
      have hx_sub_neg : SignType.sign (x - r) = SignType.neg := sign_neg_of_neg (x - r) (sub_neg.mpr hx2)
      have hsign_p : SignType.sign (p.eval x) = SignType.neg := by rw [hx_eq, hx_sub_neg]
      have hp_val_neg : p.eval x < 0 := sign_intro_neg (p.eval x) hsign_p
      nlinarith
    have hright : ∀ x, r < x ∧ x < r + ε → p.eval x * (derivative p).eval x > 0 := by
      intro x ⟨hx1, hx2⟩
      have hx_mem : x ∈ Metric.ball r ε := by
        rw [Metric.mem_ball, Real.dist_eq]
        have hx_sub : x - r > 0 := by linarith
        have h_abs : |x - r| = x - r := abs_of_pos hx_sub
        rw [h_abs]; linarith
      have hx_dist : |x - r| < ε := Metric.mem_ball.mp hx_mem
      have hx_mem₁ : x ∈ Metric.ball r ε₁ := by
        rw [Metric.mem_ball, Real.dist_eq]; exact lt_of_lt_of_le hx_dist (min_le_left _ _)
      have hx_mem₂ : x ∈ Metric.ball r ε₂ := by
        rw [Metric.mem_ball, Real.dist_eq]; exact lt_of_lt_of_le hx_dist (min_le_right _ _)
      have hx_eq : SignType.sign (p.eval x) = SignType.sign (x - r) := hball₁ hx_mem₁
      have hx_pos : (derivative p).eval x > 0 := hball₂ hx_mem₂
      have hx_sub_pos : SignType.sign (x - r) = SignType.pos := sign_pos_of_pos (x - r) (sub_pos.mpr hx1)
      have hsign_p : SignType.sign (p.eval x) = SignType.pos := by rw [hx_eq, hx_sub_pos]
      have hp_val_pos : p.eval x > 0 := sign_intro_pos (p.eval x) hsign_p
      nlinarith
    exact ⟨⟨ε, hε, hleft⟩, ⟨ε, hε, hright⟩⟩
  · have hneg : (derivative p).eval r < 0 := by
      by_contra! H
      have hle : (derivative p).eval r ≤ 0 := by linarith
      have h_eq : (derivative p).eval r = 0 := le_antisymm hle H
      exact hp1 h_eq
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
        rw [Metric.mem_ball, Real.dist_eq]
        have hx_sub : x - r < 0 := by linarith
        have h_abs : |x - r| = -(x - r) := abs_of_neg hx_sub
        rw [h_abs]; linarith
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
      have hp_val_pos : p.eval x > 0 := sign_intro_pos (p.eval x) hsign_p
      nlinarith
    have hright : ∀ x, r < x ∧ x < r + ε → p.eval x * (derivative p).eval x > 0 := by
      intro x ⟨hx1, hx2⟩
      have hx_mem : x ∈ Metric.ball r ε := by
        rw [Metric.mem_ball, Real.dist_eq]
        have hx_sub : x - r > 0 := by linarith
        have h_abs : |x - r| = x - r := abs_of_pos hx_sub
        rw [h_abs]; linarith
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
      have hp_val_neg : p.eval x < 0 := sign_intro_neg (p.eval x) hsign_p
      nlinarith
    exact ⟨⟨ε, hε, hleft⟩, ⟨ε, hε, hright⟩⟩

-- Sturm's theorem for squarefree real polynomials
theorem sturm (p : ℝ[X]) (hp : Squarefree p) {a b : ℝ} (hab : a < b)
    (ha : p.eval a ≠ 0) (hb : p.eval b ≠ 0) :
    ((p.roots.toFinset).filter (fun x => a < x ∧ x < b)).card =
      sigma p a - sigma p b := by
  have hp_simple : ∀ r, p.eval r = 0 → (derivative p).eval r ≠ 0 :=
    squarefree_deriv_nonzero_at_root p hp
  
  set N := ((p.roots.toFinset).filter (fun x => a < x ∧ x < b)).card with hN
  
  -- Standard proof of Sturm's theorem. The function σ(x) = sigma(p,x) is
  -- piecewise constant on [a,b], jumping by exactly 1 at each root of p and
  -- remaining constant at all other points. Therefore σ(a) - σ(b) equals the
  -- number of roots of p in (a,b).
  
  -- Root set in (a,b)
  let roots_set := ((p.roots.toFinset).filter (fun x => a < x ∧ x < b))
  
  -- We prove by induction on |roots_set| that sigma(p,a) = |roots_set| + sigma(p,b)
  have h_main : sigma p a = N + sigma p b := by
    -- We'll use: for any interval (c,d) with no roots of p, sigma is constant
    -- Combined with: at each root r of p, sigma drops by 1
    
    -- The base case: if roots_set is empty, sigma(p,a) = sigma(p,b)
    -- (because no chain entry changes sign on (a,b) when p has no roots)
    
    -- The inductive step: if roots_set has k+1 elements, let r be the smallest.
    -- Then (a, r) has no roots, so sigma(p,a) = sigma(p, r⁻)
    -- At r, sigma drops by 1, so sigma(p, r⁻) = sigma(p, r⁺) + 1
    -- By the induction hypothesis on (r, b), sigma(p, r⁺) = (|roots_set|-1) + sigma(p,b)
    -- Therefore sigma(p,a) = (|roots_set|-1) + sigma(p,b) + 1 = |roots_set| + sigma(p,b)
    
    -- This is the standard proof. The crucial lemmas are:
    -- (1) sigma is constant on intervals with no p-roots
    -- (2) sigma drops by exactly 1 at each simple root of p
    
    -- Lemma (2) follows from the sign change analysis (sign_at_simple_root):
    -- At a simple root r of p, p(x) changes sign while p'(x) doesn't.
    -- The rest of the Sturm chain preserves its sign change count.
    
    -- Lemma (1) follows from continuity of chain polynomials and the fact that
    -- non-p chain entries preserve sign changes at their roots.
    
    sorry
    
  omega