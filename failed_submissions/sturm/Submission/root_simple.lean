lemma root_simple (p : ℝ[X]) (hp : Squarefree p) (r : ℝ) (hr : p.eval r = 0) : (derivative p).eval r ≠ 0 := by
  have hsep : Separable p := by
    have hpf : PerfectField ℝ := by infer_instance
    exact ((PerfectField.separable_iff_squarefree (K := ℝ) (g := p)).mpr hp)
  rcases hsep with ⟨a, b, h⟩
  by_contra! hderiv
  have h1 : (a * p + b * derivative p).eval r = 1 := by
    calc (a * p + b * derivative p).eval r = (1 : ℝ[X]).eval r := by simpa [h]
    _ = 1 := by simp
  have h0 : (a * p + b * derivative p).eval r = 0 := by
    simp [hr, hderiv, Polynomial.eval_add, Polynomial.eval_mul]
  linarith