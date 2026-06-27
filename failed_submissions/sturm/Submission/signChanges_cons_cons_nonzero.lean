lemma signChanges_cons_cons_nonzero (a b : ℝ) (rest : List ℝ) (ha : a ≠ 0) (hb : b ≠ 0) : 
    signChanges (a :: b :: rest) = (if a * b < 0 then 1 else 0) + signChanges (b :: rest) := by
  unfold signChanges; simp [ha, hb]
  by_cases h : a * b < 0; · simp [h, add_comm]; · simp [h]