lemma sign_opposite_pos_deriv (p : ℝ[X]) (r : ℝ) (hr : p.eval r = 0) (hpos : (derivative p).eval r > 0) :
    ∃ ε > 0, ∀ δ, 0 < δ → δ < ε → p.eval (r - δ) * p.eval (r + δ) < 0 := by
  rcases exist_interval_deriv_pos p r hpos with ⟨ε, hε, hpos_near⟩
  refine ⟨ε, hε, ?_⟩
  intro δ hδ hδ_lt
  have hδ_ne : δ ≠ 0 := by linarith
  have hleft : r - δ ∈ Ioo (r - ε) (r + ε) := by constructor <;> nlinarith
  have hright : r + δ ∈ Ioo (r - ε) (r + ε) := by constructor <;> nlinarith
  have hp'_left_pos : (derivative p).eval (r - δ) > 0 := hpos_near (r - δ) hleft
  have hp'_right_pos : (derivative p).eval (r + δ) > 0 := hpos_near (r + δ) hright
  rcases exists_deriv_eq_slope (fun x : ℝ => p.eval x) (a := r - δ) (b := r) (by nlinarith)
    (Polynomial.continuous p).continuousOn (Polynomial.differentiableOn p) with ⟨c, hc, hc_eq⟩
  have hc_interval : c ∈ Ioo (r - ε) (r + ε) := by
    rcases hc with ⟨hc1, hc2⟩; constructor <;> nlinarith
  have hc_pos : (derivative p).eval c > 0 := hpos_near c hc_interval
  have h_sub_eq : r - (r - δ) = δ := by ring
  rw [h_sub_eq] at hc_eq
  rw [deriv_eq_poly_deriv p c] at hc_eq
  have h_eq1 : p.eval r - p.eval (r - δ) = (derivative p).eval c * δ := by
    calc
      p.eval r - p.eval (r - δ) = ((p.eval r - p.eval (r - δ)) / δ) * δ := by field_simp [hδ_ne]
      _ = (derivative p).eval c * δ := by rw [hc_eq]
  have hp_left_neg : p.eval (r - δ) < 0 := by
    rw [hr] at h_eq1; nlinarith
  rcases exists_deriv_eq_slope (fun x : ℝ => p.eval x) (a := r) (b := r + δ) (by nlinarith)
    (Polynomial.continuous p).continuousOn (Polynomial.differentiableOn p) with ⟨d, hd, hd_eq⟩
  have hd_interval : d ∈ Ioo (r - ε) (r + ε) := by
    rcases hd with ⟨hd1, hd2⟩; constructor <;> nlinarith
  have hd_pos : (derivative p).eval d > 0 := hpos_near d hd_interval
  have h_sub_eq2 : (r + δ) - r = δ := by ring
  rw [h_sub_eq2] at hd_eq
  rw [deriv_eq_poly_deriv p d] at hd_eq
  have h_eq2 : p.eval (r + δ) - p.eval r = (derivative p).eval d * δ := by
    calc
      p.eval (r + δ) - p.eval r = ((p.eval (r + δ) - p.eval r) / δ) * δ := by field_simp [hδ_ne]
      _ = (derivative p).eval d * δ := by rw [hd_eq]
  have hp_right_pos : p.eval (r + δ) > 0 := by
    rw [hr] at h_eq2; nlinarith
  nlinarith