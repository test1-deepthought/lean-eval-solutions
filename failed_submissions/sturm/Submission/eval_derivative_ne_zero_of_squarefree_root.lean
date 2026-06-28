lemma eval_derivative_ne_zero_of_squarefree_root (p : ℝ[X]) (hp : Squarefree p) (r : ℝ) (hr : p.eval r = 0) : 
    p.derivative.eval r ≠ 0 := by
  have hsep : p.Separable := ((PerfectField.separable_iff_squarefree (K := ℝ) (g := p)).mpr hp)
  rcases ((Polynomial.separable_def p).mp hsep) with ⟨a, b, h⟩
  have h_eval : (a * p + b * derivative p).eval r = 1 := by rw [h, Polynomial.eval_one]
  have h_eval' : (a * p + b * derivative p).eval r = a.eval r * p.eval r + b.eval r * (derivative p).eval r := by
    simp [Polynomial.eval_add, Polynomial.eval_mul]
  rw [h_eval'] at h_eval; rw [hr] at h_eval; simp at h_eval
  intro hzero; rw [hzero] at h_eval; simp at h_eval