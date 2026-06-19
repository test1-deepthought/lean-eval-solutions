import Mathlib
open Polynomial

lemma eval_mod_eq_eval_of_root (a q : ℝ[X]) (r : ℝ) (hq : q.eval r = 0) : (a % q).eval r = a.eval r := by
  by_cases hq0 : q = 0
  · subst hq0; simp
  · have hlc0 : q.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hq0
    set m := q * C (q.leadingCoeff⁻¹) with hm_def
    have hm_root : m.eval r = 0 := by
      dsimp [m]; simp [hq]
    have hdiv : a %ₘ m + m * (a /ₘ m) = a := Polynomial.modByMonic_add_div a m
    have h_ev_mod : (a %ₘ m).eval r = a.eval r := by
      have := congrArg (fun p => p.eval r) hdiv
      simp [hm_root, eval_add, eval_mul] at this
      nlinarith
    calc
      (a % q).eval r = (a %ₘ m).eval r := by rw [Polynomial.mod_def, hm_def]
      _ = a.eval r := h_ev_mod

lemma squarefree_no_common_root (p : ℝ[X]) (hp : Squarefree p) (r : ℝ) (hr : p.eval r = 0) :
    (derivative p).eval r ≠ 0 := by
  intro h
  have hXdiv : (X - C r) ∣ p := by
    rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot, hr]
  rcases hXdiv with ⟨q, hpq⟩
  have hderiv : derivative p = q + (X - C r) * derivative q := by
    calc
      derivative p = derivative ((X - C r) * q) := by rw [hpq]
      _ = derivative (X - C r) * q + (X - C r) * derivative q := by rw [derivative_mul]
      _ = 1 * q + (X - C r) * derivative q := by simp
      _ = q + (X - C r) * derivative q := by simp
  have hq_root : q.eval r = 0 := by
    calc
      q.eval r = (q + (X - C r) * derivative q).eval r := by simp
      _ = (derivative p).eval r := by rw [hderiv]
      _ = 0 := h
  have hXdiv_q : (X - C r) ∣ q := by
    rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot, hq_root]
  rcases hXdiv_q with ⟨q', hqq'⟩
  have hXsq_div : (X - C r) * (X - C r) ∣ p := by
    use q'
    calc
      p = (X - C r) * q := hpq
      _ = (X - C r) * ((X - C r) * q') := by rw [hqq']
      _ = (X - C r) * (X - C r) * q' := by ring
  have h_sqfree := hp (X - C r) hXsq_div
  have h_not_unit : ¬ IsUnit (X - C r) := Polynomial.not_isUnit_X_sub_C r
  exact h_not_unit h_sqfree

lemma opposite_signs_at_root (p q : ℝ[X]) (r : ℝ) (hq : q.eval r = 0) (hp : p.eval r ≠ 0) :
    p.eval r * (-(p % q)).eval r < 0 := by
  have hmod : (p % q).eval r = p.eval r := eval_mod_eq_eval_of_root p q r hq
  have : p.eval r * (-(p.eval r)) < 0 := by
    nlinarith [sq_pos_of_ne_zero hp]
  calc
    p.eval r * (-(p % q)).eval r = p.eval r * (-((p % q).eval r)) := by simp
    _ = p.eval r * (-(p.eval r)) := by rw [hmod]
    _ < 0 := this

lemma factor_theorem (p : ℝ[X]) (r : ℝ) (hr : p.eval r = 0) : ∃ q, p = (X - C r) * q := by
  have hdiv : (X - C r) ∣ p := by
    rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot]
    exact hr
  exact hdiv

lemma factor_deriv (p q : ℝ[X]) (r : ℝ) (hpq : p = (X - C r) * q) : q.eval r = (derivative p).eval r := by
  have hderiv : derivative ((X - C r) * q) = q + (X - C r) * derivative q := by
    calc
      derivative ((X - C r) * q) = derivative (X - C r) * q + (X - C r) * derivative q := by
        rw [derivative_mul]
      _ = 1 * q + (X - C r) * derivative q := by simp
      _ = q + (X - C r) * derivative q := by simp
  calc
    q.eval r = (q + (X - C r) * derivative q).eval r := by simp
    _ = (derivative ((X - C r) * q)).eval r := by rw [hderiv]
    _ = (derivative p).eval r := by rw [hpq]
