lemma triple_sign_lemma (a b c : ℝ) (hac : a * c < 0) (hb : b ≠ 0) :
    ((if a * b < 0 then 1 else 0 : ℕ) + (if b * c < 0 then 1 else 0 : ℕ)) = 1 := by
  have ha_ne_zero : a ≠ 0 := by intro hzero; subst hzero; nlinarith
  have hc_ne_zero : c ≠ 0 := by intro hzero; subst hzero; nlinarith
  have ha_sign : a > 0 ∨ a < 0 := lt_or_gt_of_ne ha_ne_zero.symm
  have hb_sign : b > 0 ∨ b < 0 := lt_or_gt_of_ne hb.symm
  rcases ha_sign with (ha_pos | ha_neg)
  · have hc_neg : c < 0 := by nlinarith
    rcases hb_sign with (hb_pos | hb_neg)
    · have h1 : ¬ (a * b < 0) := by nlinarith; have h2 : b * c < 0 := by nlinarith; simp [h1, h2]
    · have h1 : a * b < 0 := by nlinarith; have h2 : ¬ (b * c < 0) := by nlinarith; simp [h1, h2]
  · have hc_pos : c > 0 := by nlinarith
    rcases hb_sign with (hb_pos | hb_neg)
    · have h1 : a * b < 0 := by nlinarith; have h2 : ¬ (b * c < 0) := by nlinarith; simp [h1, h2]
    · have h1 : ¬ (a * b < 0) := by nlinarith; have h2 : b * c < 0 := by nlinarith; simp [h1, h2]