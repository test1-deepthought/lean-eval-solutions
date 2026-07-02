lemma deriv_eq_poly_deriv (p : ℝ[X]) (x : ℝ) : deriv (fun x' : ℝ => p.eval x') x = (derivative p).eval x := by
  have h := Polynomial.hasDerivAt p x
  exact h.deriv