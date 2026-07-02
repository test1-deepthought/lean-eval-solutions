lemma sqfree_imp_sep (p : ℝ[X]) (hp : Squarefree p) : Separable p :=
  (PerfectField.separable_iff_squarefree (g := p)).mpr hp