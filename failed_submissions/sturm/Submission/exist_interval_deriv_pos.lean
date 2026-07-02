lemma exist_interval_deriv_pos (p : ℝ[X]) (r : ℝ) (hpos : (derivative p).eval r > 0) :
    ∃ ε > 0, ∀ x, r - ε < x ∧ x < r + ε → (derivative p).eval x > 0 := by
  have hcont : ContinuousAt (fun x : ℝ => (derivative p).eval x) r :=
    (Polynomial.continuous (derivative p)).continuousAt
  rcases Metric.mem_nhds_iff.mp (hcont (isOpen_Ioi.mem_nhds hpos)) with ⟨ε, hε, hball⟩
  refine ⟨ε, hε, ?_⟩
  intro x ⟨hx1, hx2⟩
  have hx_mem : x ∈ Metric.ball r ε := by
    rw [Metric.mem_ball, dist_eq_norm, Real.norm_eq_abs, abs_lt]
    constructor <;> nlinarith
  exact hball hx_mem