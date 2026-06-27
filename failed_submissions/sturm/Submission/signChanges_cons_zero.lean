lemma signChanges_cons_zero (a : ℝ) (xs : List ℝ) (ha : a = 0) : signChanges (a :: xs) = signChanges xs := by
  subst ha; unfold signChanges; simp