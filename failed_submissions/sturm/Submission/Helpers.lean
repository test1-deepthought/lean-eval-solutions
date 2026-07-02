import Mathlib
open Polynomial
open scoped Classical

namespace LeanEval.Algebra

lemma signChanges_nil : signChanges ([] : List ℝ) = 0 := by
  unfold signChanges; simp

lemma signChanges_singleton (x : ℝ) : signChanges [x] = 0 := by
  unfold signChanges; dsimp
  classical
  by_cases hx : x = 0
  · subst x; simp
  · simp [hx]

lemma signChanges_pair (x y : ℝ) : signChanges [x, y] = if x * y < 0 then 1 else 0 := by
  unfold signChanges; dsimp
  classical
  by_cases hx0 : x = 0
  · subst x
    by_cases hy0 : y = 0
    · subst y; simp
    · simp [hy0]
  · by_cases hy0 : y = 0
    · subst y; simp [hx0]
    · by_cases h : x * y < 0
      · simp [hx0, hy0, h]
      · simp [hx0, hy0, h]

lemma signChanges_triple_opposite_ends {a b c : ℝ} (hac : a * c < 0) (hb : b ≠ 0) : signChanges [a, b, c] = 1 := by
  have ha : a ≠ 0 := by
    intro hzero; subst a; have : 0 * c < 0 := hac; simp at this
  have hc : c ≠ 0 := by
    intro hzero; subst c; have : a * 0 < 0 := hac; simp at this
  unfold signChanges; dsimp; classical
  simp [ha, hb, hc]
  have h_sq_pos : b ^ 2 > 0 := sq_pos_iff.mpr hb
  have h_prod_lt_zero : (a * b) * (b * c) < 0 := by
    calc
      (a * b) * (b * c) = (a * c) * (b ^ 2) := by ring
      _ < 0 * (b ^ 2) := mul_lt_mul_of_pos_right hac h_sq_pos
      _ = 0 := by simp
  have h_neg_one : (a * b < 0 ∧ ¬ (b * c < 0)) ∨ (¬ (a * b < 0) ∧ b * c < 0) := by
    by_cases hab : a * b < 0
    · have hbc_nonneg : ¬ (b * c < 0) := by
        intro hbc
        have : (a * b) * (b * c) > 0 := mul_pos_of_neg_of_neg hab hbc
        linarith
      exact Or.inl ⟨hab, hbc_nonneg⟩
    · have hbc_neg : b * c < 0 := by
        have hab_nonneg : 0 ≤ a * b := not_lt.mp hab
        by_contra! H
        have H' : 0 ≤ b * c := H
        have : (a * b) * (b * c) ≥ 0 := mul_nonneg hab_nonneg H'
        linarith
      exact Or.inr ⟨hab, hbc_neg⟩
  rcases h_neg_one with (⟨hab, hbc⟩ | ⟨hab, hbc⟩)
  · simp [hab, hbc]
  · simp [hab, hbc]

lemma sturmAux_recurse (a b : ℝ[X]) (n : ℕ) (hb : b ≠ 0) : 
    sturmAux a b (n+1) = a :: sturmAux b (-(a % b)) n := by
  simp [sturmAux, hb]

lemma sturmAux_ne_nil (a b : ℝ[X]) (n : ℕ) : sturmAux a b n ≠ [] := by
  induction' n with k ih generalizing a b
  · simp [sturmAux]
  · simp [sturmAux]; split <;> simp [ih]

lemma sturmChain_ne_nil (p : ℝ[X]) : sturmChain p ≠ [] :=
  sturmAux_ne_nil p (derivative p) (p.natDegree + 2)

lemma deriv_nz_at_root (p : ℝ[X]) (hp : Squarefree p) (r : ℝ) (hpr : p.eval r = 0) : p.derivative.eval r ≠ 0 := by
  have hp_sep : p.Separable := (PerfectField.separable_iff_squarefree.mpr hp)
  exact hp_sep.eval₂_derivative_ne_zero (RingHom.id ℝ) hpr

end LeanEval.Algebra