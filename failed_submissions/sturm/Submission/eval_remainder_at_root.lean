lemma eval_remainder_at_root (a b : ℝ[X]) (r : ℝ) (hb : b.eval r = 0) : (a % b).eval r = a.eval r := by
  have hdiv := EuclideanDomain.div_add_mod a b
  apply_fun (·.eval r) at hdiv
  simp [eval_add, eval_mul, hb] at hdiv; exact hdiv