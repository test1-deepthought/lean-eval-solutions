lemma signChanges_triple_opposite (a b c : ℝ) (hac : a * c < 0) : signChanges [a, b, c] = 1 := by
  have ha0 : a ≠ 0 := by intro hzero; subst hzero; nlinarith
  have hc0 : c ≠ 0 := by intro hzero; subst hzero; nlinarith
  by_cases hb0 : b = 0
  · subst hb0; simp [ha0, hc0, hac]
  · have hb0' : b ≠ 0 := hb0
    have h1 : signChanges [a, b, c] = (if a * b < 0 then 1 else 0) + signChanges [b, c] := by
      simpa using signChanges_cons_cons_nonzero a b [c] ha0 hb0'
    have h2 : signChanges [b, c] = (if b * c < 0 then 1 else 0) := by
      calc
        signChanges [b, c] = (if b * c < 0 then 1 else 0) + signChanges [c] :=
          signChanges_cons_cons_nonzero b c [] hb0' hc0
        _ = (if b * c < 0 then 1 else 0) + 0 := by simp [signChanges_singleton]
        _ = (if b * c < 0 then 1 else 0) := by simp
    rw [h1, h2]
    have hsq_pos : b ^ 2 > 0 := sq_pos_of_ne_zero hb0'
    have hprod_lt0 : (a * b) * (b * c) < 0 := by
      calc
        (a * b) * (b * c) = (a * c) * (b ^ 2) := by ring
        _ < 0 := mul_neg_of_neg_of_pos hac hsq_pos
    have h_opp : (a * b < 0 ∧ 0 ≤ b * c) ∨ (0 ≤ a * b ∧ b * c < 0) := by
      by_cases hab : a * b < 0
      · left; refine ⟨hab, ?_⟩; nlinarith
      · have hab' : 0 ≤ a * b := by nlinarith
        have hbc_lt0 : b * c < 0 := by nlinarith
        right; exact ⟨hab', hbc_lt0⟩
    rcases h_opp with (⟨hab, hbc⟩ | ⟨hab, hbc⟩)
    · simp [hab, hbc]
    · simp [hab, hbc]