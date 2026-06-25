lemma eval_remainder_at_root (a b : ℝ[X]) (r : ℝ) (hb : b.eval r = 0) : (a % b).eval r = a.eval r := by
  have hdiv := EuclideanDomain.div_add_mod a b
  have hval := congrArg (fun q : ℝ[X] => q.eval r) hdiv
  simp [hb] at hval; exact hval