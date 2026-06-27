lemma signChanges_filter_eq (xs : List ℝ) : signChanges xs = signChanges (xs.filter (· ≠ 0)) := by
  unfold signChanges; simp