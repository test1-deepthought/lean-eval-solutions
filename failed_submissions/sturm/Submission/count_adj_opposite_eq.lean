lemma count_adj_opposite_eq (A : List ℝ) (hA : ∀ x ∈ A, x ≠ 0) : 
    ((A.zip A.tail).filter (fun q : ℝ × ℝ => q.1 * q.2 < 0)).length = 
    (((A.map sgnZ).zip (A.map sgnZ).tail).filter (fun (a, b) => a * b = (-1 : ℤ))).length := by
  induction A with
  | nil => rfl
  | cons x xs ih =>
    have hx : x ≠ 0 := hA x (by simp)
    have hxs : ∀ x' ∈ xs, x' ≠ 0 := λ x' hx' => hA x' (by simp [hx'])
    match xs with
    | [] => simp
    | y :: ys =>
      have hy : y ≠ 0 := hxs y (by simp)
      have h_all : ∀ z ∈ y :: ys, z ≠ 0 := by
        intro z hz; simp at hz; rcases hz with (rfl | hz')
        · exact hy
        · exact hxs z (by simp [hz'])
      simp
      by_cases hxy : x * y < 0
      · have h_sgn : sgnZ x * sgnZ y = (-1 : ℤ) := ((sgnZ_mul_neg_one_iff x y hx hy).mpr hxy)
        simp [hxy, h_sgn]
        simpa using ih h_all
      · have h_not_sgn : ¬(sgnZ x * sgnZ y = (-1 : ℤ)) := by
          rw [sgnZ_mul_neg_one_iff x y hx hy]; exact hxy
        simp [hxy, h_not_sgn]
        simpa using ih h_all