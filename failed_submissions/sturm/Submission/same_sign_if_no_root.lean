lemma same_sign_if_no_root (q : ℝ[X]) {a b : ℝ} (hab : a ≤ b) (h : ∀ x ∈ Icc a b, q.eval x ≠ 0) :
    q.eval a * q.eval b > 0 := by
  by_cases ha_pos : q.eval a > 0
  · have hb_pos : q.eval b > 0 := by
      by_contra! hb_nonpos
      have hcont : ContinuousOn (fun (x : ℝ) => q.eval x) (Icc a b) :=
        (Polynomial.continuous q).continuousOn
      have h0 : (0 : ℝ) ∈ Icc (q.eval b) (q.eval a) := ⟨hb_nonpos, ha_pos.le⟩
      have h_ivt := intermediate_value_Icc' hab hcont h0
      rcases h_ivt with ⟨x, hx, hx0⟩
      exact h x hx hx0
    nlinarith
  · by_cases ha0 : q.eval a = 0
    · exfalso; exact h a (left_mem_Icc.mpr hab) ha0
    · have ha_nonpos : q.eval a ≤ 0 := by linarith
      have ha_neg : q.eval a < 0 := by
        by_contra! hge; have : q.eval a = 0 := by nlinarith; exact ha0 this
      have hb_neg : q.eval b < 0 := by
        by_contra! hb_nonneg
        have hcont : ContinuousOn (fun (x : ℝ) => q.eval x) (Icc a b) :=
          (Polynomial.continuous q).continuousOn
        have h0 : (0 : ℝ) ∈ Icc (q.eval a) (q.eval b) := ⟨ha_neg.le, hb_nonneg⟩
        have h_ivt := intermediate_value_Icc hab hcont h0
        rcases h_ivt with ⟨x, hx, hx0⟩
        exact h x hx hx0
      nlinarith