lemma eval_derivative_ne_zero_of_squarefree_root (p : ℝ[X]) (hp : Squarefree p) (r : ℝ) (hr : p.eval r = 0) :
    p.derivative.eval r ≠ 0 := by
  have hℝ : PerfectField ℝ := PerfectField.ofCharZero
  have hsep : p.Separable := ((PerfectField.separable_iff_squarefree (g := p)).mpr hp)
  have hae : aeval r p = 0 := by simpa using hr
  have hd : aeval r (derivative p) ≠ 0 :=
    Polynomial.Separable.aeval_derivative_ne_zero hsep hae
  simpa using hd