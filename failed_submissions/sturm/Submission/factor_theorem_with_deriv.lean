lemma factor_theorem_with_deriv (p : ℝ[X]) (r : ℝ) (hr : p.eval r = 0) :
    ∃ q : ℝ[X], p = (X - C r) * q ∧ q.eval r = p.derivative.eval r := by
  have hroot : IsRoot p r := by rw [IsRoot, hr]
  have hdiv : (X - C r) ∣ p := (Polynomial.dvd_iff_isRoot).mpr hroot
  rcases hdiv with ⟨q, hp_eq⟩
  have hqeval : q.eval r = p.derivative.eval r := by
    calc
      q.eval r = (q + (X - C r) * derivative q).eval r := by simp
      _ = (derivative ((X - C r) * q)).eval r := by
        rw [derivative_mul, derivative_sub, derivative_X, derivative_C]; simp
      _ = (derivative p).eval r := by rw [hp_eq]
  refine ⟨q, hp_eq, hqeval⟩