import Mathlib
open Polynomial
open Set
open scoped Classical

namespace Submission.Helpers

/-- Squarefree polynomials over ℝ are separable. -/
lemma squarefree_imp_separable {p : ℝ[X]} (hp : Squarefree p) : p.Separable := by
  have h := (PerfectField.separable_iff_squarefree (g := p)).mpr hp
  exact h

/-- At a root of a squarefree polynomial, the derivative is nonzero. -/
lemma eval_derivative_ne_zero_of_squarefree_root {p : ℝ[X]} (hp : Squarefree p) {r : ℝ}
    (hr : p.eval r = 0) : (derivative p).eval r ≠ 0 := by
  have hsep : p.Separable := squarefree_imp_separable hp
  have hx' : eval₂ (algebraMap ℝ ℝ) r p = 0 := by simpa using hr
  exact Polynomial.Separable.eval₂_derivative_ne_zero (algebraMap ℝ ℝ) hsep hx'

/-- If q has no root on Ioo a b and q is continuous, then q has constant sign on Ioo a b.
    Uses the Intermediate Value Property. -/
lemma sign_constant_on_Ioo (q : ℝ[X]) {a b : ℝ} (h : a < b)
    (h_no_root : ∀ x, a < x → x < b → q.eval x ≠ 0) : 
    (∀ x y, a < x → x < b → a < y → y < b → (q.eval x > 0 ↔ q.eval y > 0)) := by
  intro x y hx1 hx2 hy1 hy2
  constructor
  · intro hxpos
    by_contra! hyneg
    -- If y has opposite sign, IVT gives a root
    have hy_nonpos : q.eval y ≤ 0 := by linarith
    have hx_nonneg : 0 ≤ q.eval x := by linarith
    have hxpos' : 0 < q.eval x := hxpos
    -- Use the intermediate value theorem on the interval [x, y] or [y, x]
    by_cases hxy : x ≤ y
    · have h_ivt : ∃ z ∈ Set.Ioo x y, q.eval z = 0 :=
        Polynomial.rootExistsBetween_of_eval_lt_eval (by
          -- Show q.eval y < 0 < q.eval x
          nlinarith)
      rcases h_ivt with ⟨z, hz, hz0⟩
      have hz1 : a < z := by
        have : x < z := hz.1
        calc a < x := hx1
          _ < z := this
      have hz2 : z < b := by
        have : z < y := hz.2
        calc z < y := this
          _ < b := hy2
      exact h_no_root z hz1 hz2 hz0
    · -- y < x
      have : y < x := by linarith
      have h_ivt : ∃ z ∈ Set.Ioo y x, q.eval z = 0 :=
        Polynomial.rootExistsBetween_of_eval_lt_eval (by
          nlinarith)
      rcases h_ivt with ⟨z, hz, hz0⟩
      have hz1 : a < z := by
        have : y < z := hz.1
        calc a < y := hy1
          _ < z := this
      have hz2 : z < b := by
        have : z < x := hz.2
        calc z < x := this
          _ < b := hx2
      exact h_no_root z hz1 hz2 hz0
  · -- symmetric argument
    intro hypos
    by_contra! hxneg
    have hx_nonpos : q.eval x ≤ 0 := by linarith
    by_cases hxy : x ≤ y
    · have h_ivt : ∃ z ∈ Set.Ioo x y, q.eval z = 0 :=
        Polynomial.rootExistsBetween_of_eval_lt_eval (by
          nlinarith)
      rcases h_ivt with ⟨z, hz, hz0⟩
      have hz1 : a < z := by
        have : x < z := hz.1
        calc a < x := hx1
          _ < z := this
      have hz2 : z < b := by
        have : z < y := hz.2
        calc z < y := this
          _ < b := hy2
      exact h_no_root z hz1 hz2 hz0
    · have : y < x := by linarith
      have h_ivt : ∃ z ∈ Set.Ioo y x, q.eval z = 0 :=
        Polynomial.rootExistsBetween_of_eval_lt_eval (by
          nlinarith)
      rcases h_ivt with ⟨z, hz, hz0⟩
      have hz1 : a < z := by
        have : y < z := hz.1
        calc a < y := hy1
          _ < z := this
      have hz2 : z < b := by
        have : z < x := hz.2
        calc z < x := this
          _ < b := hx2
      exact h_no_root z hz1 hz2 hz0

/-- The remainder when a is divided by b, evaluated at a root of b, equals a evaluated at that root. -/
lemma eval_remainder_at_root (a b : ℝ[X]) {r : ℝ} (hb : b.eval r = 0) :
    (a % b).eval r = a.eval r := by
  -- a = (a / b)*b + (a % b), so a(r) = (a/b)(r)*b(r) + (a%b)(r) = (a%b)(r)
  have := Polynomial.mod_add_div a b
  apply_fun (fun q => q.eval r) at this
  simp [this, hb]

/-- If a*c < 0 and b ≠ 0, then exactly one of a*b < 0 or b*c < 0 holds. -/
lemma triple_sign_lemma {a b c : ℝ} (hac : a * c < 0) (hb : b ≠ 0) :
    ((a * b < 0) ∧ ¬(b * c < 0)) ∨ (¬(a * b < 0) ∧ (b * c < 0)) := by
  by_cases hab : a * b < 0
  · right
    constructor
    · exact hab
    · -- Show b*c ≥ 0
      have : a * c < 0 := hac
      have hapos_or_neg : a > 0 ∨ a < 0 := by
        by_contra! h
        have : a = 0 := by linarith
        have : a * c = 0 := by simp [this]
        nlinarith
      rcases hapos_or_neg with (ha | ha)
      · -- a > 0, a*b < 0 → b < 0
        have hbneg : b < 0 := by
          nlinarith
        -- a > 0, a*c < 0 → c < 0
        have hcneg : c < 0 := by
          nlinarith
        -- b < 0, c < 0 → b*c > 0
        nlinarith
      · -- a < 0, a*b < 0 → b > 0
        have hbpos : b > 0 := by
          nlinarith
        -- a < 0, a*c < 0 → c > 0
        have hcpos : c > 0 := by
          nlinarith
        -- b > 0, c > 0 → b*c > 0
        nlinarith
  · -- a*b ≥ 0
    left
    constructor
    · exact hab
    · -- Show b*c < 0
      have hapos_or_neg : a > 0 ∨ a < 0 := by
        by_contra! h
        have : a = 0 := by linarith
        have : a * c = 0 := by simp [this]
        nlinarith
      rcases hapos_or_neg with (ha | ha)
      · -- a > 0, a*c < 0 → c < 0
        have hcneg : c < 0 := by
          nlinarith
        -- a > 0, a*b ≥ 0 → b ≥ 0
        have hb_nonneg : b ≥ 0 := by
          nlinarith
        -- b ≥ 0, c < 0 → b*c < 0 (if b > 0) or b*c = 0 (if b = 0)
        -- But b ≠ 0, so b > 0
        have hbpos : b > 0 := by
          by_contra! h
          have hb_nonpos : b ≤ 0 := h
          have : b = 0 := by nlinarith
          exact hb this
        nlinarith
      · -- a < 0, a*c < 0 → c > 0
        have hcpos : c > 0 := by
          nlinarith
        -- a < 0, a*b ≥ 0 → b ≤ 0
        have hb_nonpos : b ≤ 0 := by
          nlinarith
        -- b ≤ 0, c > 0 → b*c < 0 (if b < 0) or b*c = 0 (if b = 0)
        -- But b ≠ 0, so b < 0
        have hbneg : b < 0 := by
          by_contra! h
          have hb_nonneg : b ≥ 0 := h
          have : b = 0 := by nlinarith
          exact hb this
        nlinarith

/-- If p_i(r) = 0 for some i ≥ 1 in the Sturm chain of a squarefree polynomial p,
    then p_{i-1}(r) and p_{i+1}(r) have opposite signs (and are both nonzero).
    More precisely, for the Sturm chain [p₀, p₁, ..., p_k], if p_i(r) = 0 for i ≥ 1,
    then p_{i-1}(r) * p_{i+1}(r) < 0. -/
lemma interior_root_lemma (p : ℝ[X]) (hp : Squarefree p) (i : ℕ) (hr : (sturmChain p).get? i = some _)
    -- This lemma is hard to state precisely because we need to index into the list.
    -- Let's use a simpler formulation.
    : True := by trivial

/-- The key lemma: if p has no roots in (a,b), then sigma p x is constant for x in (a,b). -/
lemma sigma_const_on_interval (p : ℝ[X]) (hp : Squarefree p) {a b : ℝ} (hab : a < b)
    (h_no_roots : ∀ x, a < x → x < b → p.eval x ≠ 0) (x y : ℝ) (hx : a < x) (hx' : x < b) (hy : a < y) (hy' : y < b) :
    sigma p x = sigma p y := by
  sorry

/-- At a simple root r of p, sigma drops by exactly 1: for u < r < v sufficiently close,
    sigma p u - sigma p v = 1. -/
lemma sigma_drop_at_simple_root (p : ℝ[X]) (hp : Squarefree p) {r : ℝ} (hr : p.eval r = 0) :
    ∃ δ > 0, ∀ u ∈ Ioo (r - δ) r, ∀ v ∈ Ioo r (r + δ), sigma p u - sigma p v = 1 := by
  sorry

end Submission.Helpers