lemma sign_opposite_at_simple_root (p : ℝ[X]) (r : ℝ) (hr : p.eval r = 0) (hderiv : (derivative p).eval r ≠ 0) :
    ∃ ε > 0, ∀ δ, 0 < δ → δ < ε → p.eval (r - δ) * p.eval (r + δ) < 0 := by
  by_cases hpos : (derivative p).eval r > 0
  · exact sign_opposite_pos_deriv p r hr hpos
  · have hneg : (derivative p).eval r < 0 := by
      have h_cases := lt_or_gt_of_ne (Ne.symm hderiv)
      rcases h_cases with (h | h)
      · exfalso; exact hpos h
      · exact h
    have h_neg_deriv : (derivative (-p)).eval r ≠ 0 := by
      simpa [derivative_neg] using hderiv
    have h_neg_root : (-p).eval r = 0 := by simp [hr]
    have h_neg_pos : (derivative (-p)).eval r > 0 := by
      have : (derivative (-p)).eval r = -((derivative p).eval r) := by simp [derivative_neg]
      rw [this]; linarith
    rcases sign_opposite_pos_deriv (-p) r h_neg_root h_neg_pos with ⟨ε, hε, h⟩
    refine ⟨ε, hε, ?_⟩
    intro δ hδ hδ_lt
    have h' := h δ hδ hδ_lt
    simp at h'
    nlinarith

end Sturm