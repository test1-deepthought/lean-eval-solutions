lemma deriv_ne_zero_at_root (p : ℝ[X]) (hp : Squarefree p) (r : ℝ) (hr : p.eval r = 0) : (derivative p).eval r ≠ 0 := by
  have hsep : Separable p := sqfree_imp_sep p hp
  have h0 : p.eval₂ (RingHom.id ℝ) r = 0 := by simpa using hr
  have h := hsep.eval₂_derivative_ne_zero (RingHom.id ℝ) h0
  simpa using h