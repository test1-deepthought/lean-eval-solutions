lemma signChanges_triple_opposite (a b c : ℝ) (hac : a * c < 0) : signChanges [a, b, c] = 1 := by
  have ha_ne_zero : a ≠ 0 := by intro hzero; subst hzero; nlinarith
  have hc_ne_zero : c ≠ 0 := by intro hzero; subst hzero; nlinarith
  by_cases hb_zero : b = 0
  · subst hb_zero
    calc
      signChanges [a, 0, c] = signChanges ([a] ++ [0] ++ [c]) := rfl
      _ = signChanges ([a] ++ [c]) := by simpa using signChanges_splice_zero [a] [c]
      _ = signChanges [a, c] := by simp
      _ = 1 := by
        have h := signChanges_pair a c ha_ne_zero hc_ne_zero
        simp [hac, h]
  · have h_sum : ((if a * b < 0 then 1 else 0 : ℕ) + (if b * c < 0 then 1 else 0 : ℕ)) = 1 :=
      triple_sign_lemma a b c hac hb_zero
    calc
      signChanges [a, b, c] = (if a * b < 0 then 1 else 0) + signChanges (b :: [c]) := by
        simpa using signChanges_cons_cons_nonzero a b [c] ha_ne_zero hb_zero
      _ = (if a * b < 0 then 1 else 0) + (if b * c < 0 then 1 else 0) := by
        simp [signChanges_pair, hb_zero, hc_ne_zero]
      _ = 1 := h_sum