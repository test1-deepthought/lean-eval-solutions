lemma mvt_eq (f : ℝ → ℝ) (a b : ℝ) (hab : a < b) (hcont : ContinuousOn f (Icc a b))
    (hdiff : DifferentiableOn ℝ f (Ioo a b)) : ∃ c ∈ Ioo a b, f b - f a = deriv f c * (b - a) := by
  rcases exists_deriv_eq_slope f hab hcont hdiff with ⟨c, hc, h⟩
  refine ⟨c, hc, ?_⟩
  have hpos : b - a ≠ 0 := by nlinarith
  calc
    f b - f a = ((f b - f a) / (b - a)) * (b - a) := by field_simp [hpos]
    _ = deriv f c * (b - a) := by rw [h]