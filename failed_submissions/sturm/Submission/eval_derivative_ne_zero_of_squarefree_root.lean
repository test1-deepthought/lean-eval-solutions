lemma eval_derivative_ne_zero_of_squarefree_root (p : ℝ[X]) (hp : Squarefree p) (r : ℝ) (hr : p.eval r = 0) : (derivative p).eval r ≠ 0 := by
  have hsep : Separable p := squarefree_imp_separable p hp
  have hcop : IsCoprime p (derivative p) := ((Polynomial.separable_def p).mp hsep)
  intro hderiv
  have h_cop_eval : IsCoprime (p.eval r) ((derivative p).eval r) := hcop.map (evalRingHom r)
  rcases h_cop_eval with ⟨a, b, h⟩; rw [hr, hderiv] at h; simp at h