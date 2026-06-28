lemma signChanges_singleton (a : ℝ) (ha : a ≠ 0) : signChanges [a] = 0 := by
  dsimp [signChanges]; simp [ha]