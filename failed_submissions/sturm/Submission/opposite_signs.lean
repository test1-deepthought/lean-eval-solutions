lemma opposite_signs (x y : ℝ) : x * y < 0 ↔ (x < 0 ∧ 0 < y) ∨ (0 < x ∧ y < 0) := by
  constructor
  · intro h
    have hx0 : x ≠ 0 := by intro hx0; rw [hx0, zero_mul] at h; linarith
    have hy0 : y ≠ 0 := by intro hy0; rw [hy0, mul_zero] at h; linarith
    by_cases hx : x < 0
    · have hypos : 0 < y := by by_contra! H; nlinarith
      exact Or.inl ⟨hx, hypos⟩
    · have hxpos : 0 < x := by
        by_contra! H
        have hx_ge_0 : 0 ≤ x := by linarith
        have hx_le_0 : x ≤ 0 := by linarith
        have hx_eq0 : x = 0 := by nlinarith
        exact hx0 hx_eq0
      have hyneg : y < 0 := by by_contra! H; nlinarith
      exact Or.inr ⟨hxpos, hyneg⟩
  · intro h
    rcases h with (⟨hx, hy⟩ | ⟨hx, hy⟩)
    · nlinarith
    · nlinarith