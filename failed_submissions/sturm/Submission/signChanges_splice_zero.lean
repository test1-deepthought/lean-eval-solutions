lemma signChanges_splice_zero (xs ys : List ℝ) : signChanges (xs ++ [0] ++ ys) = signChanges (xs ++ ys) := by
  unfold signChanges; simp