lemma signChanges_cons_cons_nonzero (a b : ℝ) (xs : List ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    signChanges (a :: b :: xs) = (if a * b < 0 then 1 else 0) + signChanges (b :: xs) := by
  unfold signChanges
  simp [ha, hb]
  by_cases h : a * b < 0
  · simpa [h, add_comm]
  · simpa [h]