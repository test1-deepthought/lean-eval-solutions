lemma signChanges_singleton (a : ℝ) : signChanges [a] = 0 := by
  unfold signChanges
  by_cases ha : a = 0
  · subst a; simp
  · have hfilter : ([a] : List ℝ).filter (· ≠ 0) = [a] := by
      ext x; simp [ha]
    rw [hfilter]; dsimp; simp