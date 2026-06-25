lemma factor_theorem_with_deriv (p : ℝ[X]) (r : ℝ) (hp0 : p.eval r = 0) : ∃ q : ℝ[X], p = (X - C r) * q ∧ q.eval r = (derivative p).eval r := by
  have hfactor : (X - C r) ∣ p := by rw [Polynomial.dvd_iff_isRoot]; exact hp0
  rcases hfactor with ⟨q, hpq⟩; refine ⟨q, hpq, ?_⟩
  have hderiv : derivative p = q + (X - C r) * derivative q := by
    rw [hpq, derivative_mul, derivative_sub, derivative_X, derivative_C]; ring
  calc q.eval r = (q + (X - C r) * derivative q).eval r := by simp
    _ = (derivative p).eval r := by rw [hderiv]