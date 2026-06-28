lemma sign_constant_ac (a c : ℝ[X]) (r : ℝ) (ha : a.eval r ≠ 0) (hc : c.eval r ≠ 0) (h_ac : a.eval r * c.eval r < 0) :
    ∃ ε > 0, ∀ x, |x - r| < ε → (a.eval x) * (c.eval x) < 0 := by
  rcases em (a.eval r > 0) with (ha_pos | ha_notpos)
  · have ha_pos' : a.eval r > 0 := ha_pos
    have hc_neg : c.eval r < 0 := by nlinarith
    rcases sign_near a r ha_pos' with ⟨ε_a, hε_a, ha_near⟩
    rcases sign_near_neg c r hc_neg with ⟨ε_c, hε_c, hc_near⟩
    let ε := min ε_a ε_c
    have hε_pos : ε > 0 := lt_min_iff.mpr ⟨hε_a, hε_c⟩
    refine ⟨ε, hε_pos, λ x hx => ?_⟩
    have hx_a : |x - r| < ε_a := lt_of_lt_of_le hx (min_le_left _ _)
    have hx_c : |x - r| < ε_c := lt_of_lt_of_le hx (min_le_right _ _)
    nlinarith [ha_near x hx_a, hc_near x hx_c]
  · have ha_neg : a.eval r < 0 := by
      have : a.eval r ≤ 0 := le_of_not_gt ha_notpos; exact lt_of_le_of_ne this ha
    have hc_pos : c.eval r > 0 := by nlinarith
    rcases sign_near_neg a r ha_neg with ⟨ε_a, hε_a, ha_near⟩
    rcases sign_near c r hc_pos with ⟨ε_c, hε_c, hc_near⟩
    let ε := min ε_a ε_c
    have hε_pos : ε > 0 := lt_min_iff.mpr ⟨hε_a, hε_c⟩
    refine ⟨ε, hε_pos, λ x hx => ?_⟩
    have hx_a : |x - r| < ε_a := lt_of_lt_of_le hx (min_le_left _ _)
    have hx_c : |x - r| < ε_c := lt_of_lt_of_le hx (min_le_right _ _)
    nlinarith [ha_near x hx_a, hc_near x hx_c]