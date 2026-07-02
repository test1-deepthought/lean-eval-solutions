lemma nonZeroSigns_map_eq (f g : α → ℝ) (l : List α) (h : ∀ a ∈ l, f a * g a > 0) : 
    nonZeroSigns (l.map f) = nonZeroSigns (l.map g) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have ha : f a * g a > 0 := h a (by simp)
    have ha_f_nonzero : f a ≠ 0 := by
      intro hzero; have : f a * g a = 0 := by
        calc
          f a * g a = 0 * g a := by rw [hzero]
          _ = 0 := by simp
      linarith
    have ha_g_nonzero : g a ≠ 0 := by
      intro hzero; have : f a * g a = 0 := by
        calc
          f a * g a = f a * 0 := by rw [hzero]
          _ = 0 := by simp
      linarith
    have h_rest : ∀ a' ∈ l, f a' * g a' > 0 := λ a' ha' => h a' (by simp [ha'])
    have h_ih := ih h_rest
    unfold nonZeroSigns
    simp [ha_f_nonzero, ha_g_nonzero]
    have h_head : (if f a > 0 then (1 : ℤ) else (-1 : ℤ)) = (if g a > 0 then (1 : ℤ) else (-1 : ℤ)) := by
      by_cases hpos : f a > 0
      · have hpos_g : g a > 0 := by by_contra! hng; have : f a * g a ≤ 0 := by nlinarith; nlinarith
        simp [hpos, hpos_g]
      · have hneg : f a < 0 := by by_contra! hge; have : f a = 0 := by nlinarith; exact ha_f_nonzero this
        have hneg_g : g a < 0 := by by_contra! hge; have : f a * g a ≤ 0 := by nlinarith; nlinarith
        simp [hpos, hneg, hneg_g]
    simp [h_head, h_ih]