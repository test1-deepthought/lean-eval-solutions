lemma deriv_ne_zero_at_root (p : ℝ[X]) (hp : Squarefree p) (r : ℝ) (hr : p.eval r = 0) : (derivative p).eval r ≠ 0 := by
  have hsep : Polynomial.Separable p := (PerfectField.separable_iff_squarefree (g := p)).mpr hp
  have h := hsep.eval₂_derivative_ne_zero (RingHom.id ℝ) (by simpa using hr)
  simpa using h