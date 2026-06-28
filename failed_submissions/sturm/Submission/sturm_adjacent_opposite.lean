lemma sturm_adjacent_opposite (f g : ℝ[X]) (r : ℝ) (hg : g.eval r = 0) (hf : f.eval r ≠ 0) :
    f.eval r * (-(f % g)).eval r < 0 := by
  have hmod : (f % g).eval r = f.eval r := by
    have h := EuclideanDomain.mod_add_div f g
    apply_fun (·.eval r) at h
    simp [eval_add, eval_mul, hg] at h; exact h
  have hneg : (-(f % g)).eval r = -(f.eval r) := by simp [hmod]
  rw [hneg]
  have hsq : (f.eval r)^2 > 0 := sq_pos_of_ne_zero hf
  nlinarith