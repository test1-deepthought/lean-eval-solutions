lemma hp_ne_zero (p : ℝ[X]) (hp : Squarefree p) : p ≠ 0 := by
  haveI : CharZero ℝ := by infer_instance
  haveI : PerfectField ℝ := PerfectField.ofCharZero
  have hsep : Separable p := by rw [PerfectField.separable_iff_squarefree]; exact hp
  exact hsep.ne_zero