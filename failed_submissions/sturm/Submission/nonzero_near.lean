lemma nonzero_near (q : ℝ[X]) (r : ℝ) (hq : q.eval r ≠ 0) : ∃ ε > 0, ∀ x, |x - r| < ε → q.eval x ≠ 0 := by
  have hcont : Continuous (fun x : ℝ => q.eval x) := Polynomial.continuous q
  have h_open : IsOpen {x | q.eval x ≠ 0} := by
    have : {x | q.eval x ≠ 0} = (fun x : ℝ => q.eval x)⁻¹' ({0} : Set ℝ)ᶜ := by ext x; simp
    rw [this]; exact IsOpen.preimage hcont (by exact isOpen_compl_singleton)
  have h_mem : r ∈ {x | q.eval x ≠ 0} := hq
  have h_nhds : {x | q.eval x ≠ 0} ∈ 𝓝 r := h_open.mem_nhds h_mem
  rcases Metric.mem_nhds_iff.mp h_nhds with ⟨ε, hε, hball⟩
  refine ⟨ε, hε, ?_⟩; intro x hx; apply hball; rw [Metric.mem_ball, Real.dist_eq]; exact hx