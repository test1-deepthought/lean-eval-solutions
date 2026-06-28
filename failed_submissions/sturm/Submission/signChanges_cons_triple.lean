lemma signChanges_cons_triple (a b c : ℝ) (rest : List ℝ) (ha : a ≠ 0) (hc : c ≠ 0) (h_ac : a * c < 0) :
    signChanges (a :: b :: c :: rest) = 1 + signChanges (c :: rest) := by
  by_cases hb0 : b = 0
  · subst hb0; calc
      signChanges (a :: 0 :: c :: rest) = signChanges (a :: c :: rest) := by
        dsimp [signChanges]; simp [ha, hc]
      _ = (if a * c < 0 then 1 else 0) + signChanges (c :: rest) :=
        signChanges_cons_nonzero a c rest ha hc
      _ = 1 + signChanges (c :: rest) := by simp [h_ac]
  · have hb : b ≠ 0 := hb0
    have h_triple_val : (if a * b < 0 then (1 : ℕ) else 0) + (if b * c < 0 then (1 : ℕ) else 0) = 1 := by
      have h_sq_pos : b * b > 0 := mul_self_pos.mpr hb
      have h_eq : (a * b) * (b * c) = (a * c) * (b * b) := by ring
      by_cases h_ab : a * b < 0
      · have h_not_bc : ¬(b * c < 0) := by
          intro h_bc; have h_pos : (a * b) * (b * c) > 0 := mul_pos_of_neg_of_neg h_ab h_bc
          rw [h_eq] at h_pos; nlinarith
        simp [h_ab, h_not_bc]
      · have h_ab_nonneg : a * b ≥ 0 := not_lt.mp h_ab
        have h_bc : b * c < 0 := by
          by_contra! h; have h_nonneg : (a * b) * (b * c) ≥ 0 := mul_nonneg h_ab_nonneg h
          rw [h_eq] at h_nonneg; nlinarith
        simp [h_ab, h_bc]
    calc
      signChanges (a :: b :: c :: rest) = (if a * b < 0 then 1 else 0) + signChanges (b :: c :: rest) :=
        signChanges_cons_nonzero a b (c :: rest) ha hb
      _ = (if a * b < 0 then 1 else 0) + ((if b * c < 0 then 1 else 0) + signChanges (c :: rest)) := by
        rw [signChanges_cons_nonzero b c rest hb hc]
      _ = ((if a * b < 0 then 1 else 0) + (if b * c < 0 then 1 else 0)) + signChanges (c :: rest) := by omega
      _ = 1 + signChanges (c :: rest) := by rw [h_triple_val]