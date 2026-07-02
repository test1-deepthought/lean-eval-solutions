lemma eval_mod_eq_eval_at_root (a b : ℝ[X]) (r : ℝ) (hb : b.eval r = 0) : (a % b).eval r = a.eval r := by
  have h := EuclideanDomain.mod_add_div a b
  apply_fun (fun p => p.eval r) at h
  simp [eval_add, eval_mul, hb] at h
  exact h