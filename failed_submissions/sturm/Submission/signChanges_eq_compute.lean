lemma signChanges_eq_compute (xs : List ℝ) : signChanges xs = computeSignChanges (nonZeroSigns xs) := by
  unfold signChanges nonZeroSigns computeSignChanges
  let A := xs.filter (· ≠ 0)
  have hA : ∀ x ∈ A, x ≠ 0 := by
    intro x hx; have h := (mem_filter.mp hx).2; simpa using h
  exact count_adj_opposite_eq A hA