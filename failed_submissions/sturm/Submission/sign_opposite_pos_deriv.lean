lemma sign_opposite_pos_deriv (p : ℝ[X]) (r : ℝ) (hr : p.eval r = 0) (hpos : (derivative p).eval r > 0) :
    ∃ ε > 0, ∀ δ, 0 < δ → δ < ε → p.eval (r - δ) * p.eval (r + δ) < 0 := by
  rcases exist_interval_deriv_pos p r hpos with ⟨ε, hε, hpos_near⟩
  refine ⟨ε, hε, ?_⟩
  intro δ hδ hδ_lt
  have hleft : r - δ ∈ Ioo (r - ε) (r + ε) := by constructor <;> nlinarith
  have hright : r + δ ∈ Ioo (r - ε) (r + ε) := by constructor <;> nlinarith
  have hp'_left_pos : (derivative p).eval (r - δ) > 0 := hpos_near (r - δ) hleft
  have hp'_right_pos : (derivative p).eval (r + δ) > 0 := hpos_near (r + δ) hright
  have hcont : ContinuousOn (fun x : ℝ => p.eval x) (Icc (r - δ) r) :=
    (Polynomial.continuous p).continuousOn
  have hdiff : DifferentiableOn ℝ (fun x : ℝ => p.eval x) (Ioo (r - δ) r) :=
    Polynomial.differentiableOn p
  rcases mvt_eq (fun x => p.eval x) (r - δ) r (by nlinarith) hcont hdiff with ⟨c, hc, h⟩
  have hc_interval : c ∈ Ioo (r - ε) (r + ε) := by
    rcases hc with ⟨hc1, hc2⟩; constructor <;> nlinarith
  have hc_pos : (derivative p).eval c > 0 := hpos_near c hc_interval
  have hmvt1_eq : p.eval r - p.eval (r - δ) = (derivative p).eval c * (r - (r - δ)) := by
    rw [deriv_eq_poly_deriv p c] at h
    simpa [hr] using h
  have hp_left_neg : p.eval (r - δ) < 0 := by
    have : p.eval r - p.eval (r - δ) = (derivative p).eval c * δ := by
      simpa [sub_sub, add_comm, add_left_comm, add_assoc] using hmvt1_eq
    nlinarith
  have hcont2 : ContinuousOn (fun x : ℝ => p.eval x) (Icc r (r + δ)) :=
    (Polynomial.continuous p).continuousOn
  have hdiff2 : DifferentiableOn ℝ (fun x : ℝ => p.eval x) (Ioo r (r + δ)) :=
    Polynomial.differentiableOn p
  rcases mvt_eq (fun x => p.eval x) r (r + δ) (by nlinarith) hcont2 hdiff2 with ⟨d, hd, h'⟩
  have hd_interval : d ∈ Ioo (r - ε) (r + ε) := by
    rcases hd with ⟨hd1, hd2⟩; constructor <;> nlinarith
  have hd_pos : (derivative p).eval d > 0 := hpos_near d hd_interval
  have hmvt2_eq : p.eval (r + δ) - p.eval r = (derivative p).eval d * ((r + δ) - r) := by
    rw [deriv_eq_poly_deriv p d] at h'
    simpa [hr] using h'
  have hp_right_pos : p.eval (r + δ) > 0 := by
    have : p.eval (r + δ) - p.eval r = (derivative p).eval d * δ := by
      simpa [add_sub_cancel] using hmvt2_eq
    nlinarith
  nlinarith