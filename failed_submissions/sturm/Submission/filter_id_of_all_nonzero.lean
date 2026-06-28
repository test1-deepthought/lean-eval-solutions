lemma filter_id_of_all_nonzero (xs : List ℝ) (h : ∀ a ∈ xs, a ≠ 0) : xs.filter (· ≠ 0) = xs := by
  induction' xs with a as IH
  · rfl
  · have ha : a ≠ 0 := h a (by simp)
    have has : ∀ b ∈ as, b ≠ 0 := fun b hb => h b (by simp [hb])
    have IH_as : as.filter (· ≠ 0) = as := IH has
    rw [List.filter_cons]
    have hdec : decide (a ≠ 0) = true := by simp [ha]
    rw [hdec, IH_as]
    simp