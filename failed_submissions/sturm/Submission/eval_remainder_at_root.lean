lemma eval_remainder_at_root (a b : ℝ[X]) (r : ℝ) (hb : b.eval r = 0) : (a % b).eval r = a.eval r := by
  rw [Polynomial.mod_def]
  by_cases hb0 : b = 0
  · subst hb0; simp
  · have hmonic : Monic (b * C ((leadingCoeff b)⁻¹)) := by
      have hlc : leadingCoeff b ≠ 0 := leadingCoeff_ne_zero.mpr hb0
      rw [Monic, leadingCoeff_mul, leadingCoeff_C]; simp [hlc]
    have hzero : (b * C ((leadingCoeff b)⁻¹)).eval r = 0 := by simp [hb]
    rw [Polynomial.modByMonic_eq_sub_mul_div a (b * C ((leadingCoeff b)⁻¹))]
    simp [hzero]