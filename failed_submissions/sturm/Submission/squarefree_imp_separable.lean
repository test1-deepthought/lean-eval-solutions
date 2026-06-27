lemma squarefree_imp_separable (p : ℝ[X]) (hp : Squarefree p) : Separable p :=
  (PerfectField.separable_iff_squarefree (K := ℝ) (g := p)).mpr hp