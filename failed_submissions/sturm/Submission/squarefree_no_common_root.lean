lemma squarefree_no_common_root (p : ℝ[X]) (hp : Squarefree p) (r : ℝ) (hr : p.eval r = 0) :
    (derivative p).eval r ≠ 0 := by
  have hsep : p.Separable := by
    have h := PerfectField.separable_iff_squarefree (K := ℝ) (g := p); exact h.mpr hp
  have h_coprime : IsCoprime p (derivative p) := ((Polynomial.separable_def (f := p)).mp hsep)
  rcases h_coprime with ⟨a, b, h⟩
  have h_eval := congrArg (fun q => q.eval r) h
  simp [hr, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_one] at h_eval
  intro hzero; rw [hzero] at h_eval; simp at h_eval