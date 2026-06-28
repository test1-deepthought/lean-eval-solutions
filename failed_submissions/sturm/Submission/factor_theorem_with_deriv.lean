lemma factor_theorem_with_deriv (p : ℝ[X]) (r : ℝ) (hp0 : p.eval r = 0) : ∃ q : ℝ[X], p = (X - C r) * q ∧ q.eval r = (derivative p).eval r := by
  have hdiv : (X - C r) ∣ p := Polynomial.dvd_iff_isRoot.mpr hp0
  rcases hdiv with ⟨q, h⟩
  have hcalc : q.eval r = (derivative p).eval r := by
    have hderiv : derivative p = q + (X - C r) * derivative q := by
      rw [h]; rw [derivative_mul]; simp
    calc
      q.eval r = (q + (X - C r) * derivative q).eval r := by simp
      _ = (derivative p).eval r := by rw [hderiv]
  exact ⟨q, h, hcalc⟩