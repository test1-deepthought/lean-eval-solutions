lemma signChanges_triple_opposite (a b c : ℝ) (ha : a ≠ 0) (hc : c ≠ 0) (hac : a * c < 0) :
    signChanges [a, b, c] = 1 := by
  by_cases hb : b = 0
  · subst b; dsimp [signChanges]; simp [ha, hc, hac]
  · have hb' : b ≠ 0 := hb
    have hcalc : signChanges [a, b, c] = (if a * b < 0 then 1 else 0) + (if b * c < 0 then 1 else 0) := by
      calc
        signChanges [a, b, c] = (if a * b < 0 then 1 else 0) + signChanges (b :: [c]) :=
          signChanges_cons_cons a b ha hb' [c]
        _ = (if a * b < 0 then 1 else 0) + ((if b * c < 0 then 1 else 0) + signChanges [c]) := by
          rw [signChanges_cons_cons b c hb' hc []]
        _ = (if a * b < 0 then 1 else 0) + ((if b * c < 0 then 1 else 0) + 0) := by
          rw [signChanges_singleton c hc]
        _ = (if a * b < 0 then 1 else 0) + (if b * c < 0 then 1 else 0) := by simp
    rw [hcalc]
    by_cases ha_pos : a > 0
    · have hc_neg : c < 0 := by nlinarith
      by_cases hb_pos : b > 0
      · have h1 : ¬(a * b < 0) := by nlinarith
        have h2 : b * c < 0 := by nlinarith
        rw [if_neg h1, if_pos h2]
      · have hb_neg : b < 0 := by
          have hb_le : b ≤ 0 := by nlinarith
          by_contra! H; have : b = 0 := by linarith; exact hb' this
        have h1 : a * b < 0 := by nlinarith
        have h2 : ¬(b * c < 0) := by nlinarith
        rw [if_pos h1, if_neg h2]
    · have ha_neg : a < 0 := by
        have ha_le : a ≤ 0 := by nlinarith
        by_contra! H; have : a = 0 := by linarith; exact ha this
      have hc_pos : c > 0 := by nlinarith
      by_cases hb_pos : b > 0
      · have h1 : a * b < 0 := by nlinarith
        have h2 : ¬(b * c < 0) := by nlinarith
        rw [if_pos h1, if_neg h2]
      · have hb_neg : b < 0 := by
          have hb_le : b ≤ 0 := by nlinarith
          by_contra! H; have : b = 0 := by linarith; exact hb' this
        have h1 : ¬(a * b < 0) := by nlinarith
        have h2 : b * c < 0 := by nlinarith
        rw [if_neg h1, if_pos h2]