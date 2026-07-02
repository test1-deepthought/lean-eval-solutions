lemma sign_neighborhood (q : ℝ[X]) (r : ℝ) (hq : q.eval r ≠ 0) : ∃ ε > 0, ∀ x, |x - r| < ε → q.eval x * q.eval r > 0 := by
  have hcont : ContinuousAt (q.eval : ℝ → ℝ) r := (Polynomial.continuous q).continuousAt
  have hpos : q.eval r > 0 ∨ q.eval r < 0 := lt_or_gt_of_ne hq.symm
  rcases hpos with (hpos | hneg)
  · have h_open : Set.Ioo (0 : ℝ) (q.eval r * 2) ∈ 𝓝 (q.eval r) := by
      apply IsOpen.mem_nhds isOpen_Ioo; constructor <;> nlinarith
    have h_pre : (q.eval ⁻¹' Set.Ioo (0 : ℝ) (q.eval r * 2)) ∈ 𝓝 r := hcont.tendsto h_open
    rcases Metric.mem_nhds_iff.mp h_pre with ⟨ε, hε, hball⟩
    refine ⟨ε, hε, ?_⟩
    intro x hx; have hx_mem : x ∈ Metric.ball r ε := Metric.mem_ball.mpr hx
    have hx_val : q.eval x ∈ Set.Ioo (0 : ℝ) (q.eval r * 2) := hball hx_mem
    have hx_pos : q.eval x > 0 := hx_val.1; nlinarith
  · have h_open : Set.Ioo (q.eval r * 2) (0 : ℝ) ∈ 𝓝 (q.eval r) := by
      apply IsOpen.mem_nhds isOpen_Ioo; constructor <;> nlinarith
    have h_pre : (q.eval ⁻¹' Set.Ioo (q.eval r * 2) (0 : ℝ)) ∈ 𝓝 r := hcont.tendsto h_open
    rcases Metric.mem_nhds_iff.mp h_pre with ⟨ε, hε, hball⟩
    refine ⟨ε, hε, ?_⟩
    intro x hx; have hx_mem : x ∈ Metric.ball r ε := Metric.mem_ball.mpr hx
    have hx_val : q.eval x ∈ Set.Ioo (q.eval r * 2) (0 : ℝ) := hball hx_mem
    have hx_neg : q.eval x < 0 := hx_val.2; nlinarith