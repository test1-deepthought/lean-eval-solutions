lemma signChanges_cons_cons_nonzero (a b : ℝ) (rest : List ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hrest : ∀ x ∈ rest, x ≠ 0) :
    signChanges (a :: b :: rest) = (if a * b < 0 then 1 else 0) + signChanges (b :: rest) := by
  unfold signChanges
  have hfilter_all : (a :: b :: rest).filter (· ≠ 0) = a :: b :: rest := by
    refine List.filter_eq_self.mpr ?_
    intro x hx; simp at hx; rcases hx with (rfl|rfl|hx)
    · simp [ha]
    · simp [hb]
    · simp [hrest x hx]
  have hfilter_rest : (b :: rest).filter (· ≠ 0) = b :: rest := by
    refine List.filter_eq_self.mpr ?_
    intro x hx; simp at hx; rcases hx with (rfl|hx)
    · simp [hb]
    · simp [hrest x hx]
  rw [hfilter_all, hfilter_rest]; dsimp
  by_cases h : a * b < 0; · simp [h]; omega; · simp [h]; omega