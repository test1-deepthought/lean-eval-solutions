lemma sturm_adjacent_opposite (f g : ℝ[X]) (r : ℝ) (hg : g.eval r = 0) (hf : f.eval r ≠ 0) :
    f.eval r * (-(f % g)).eval r < 0 := by
  have hmod : (f % g).eval r = f.eval r := eval_remainder_at_root f g r hg
  have hneg : (-(f % g)).eval r = -(f.eval r) := by simp [hmod]
  rw [hneg]
  have hsq : (f.eval r)^2 > 0 := sq_pos_of_ne_zero hf
  nlinarith