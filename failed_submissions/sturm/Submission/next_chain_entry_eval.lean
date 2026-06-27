lemma next_chain_entry_eval (a b : ℝ[X]) (r : ℝ) (hb : b.eval r = 0) : (-(a % b)).eval r = -(a.eval r) := by
  simp [eval_remainder_at_root a b r hb]