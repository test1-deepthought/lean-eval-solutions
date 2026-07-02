lemma sgnZ_mul_neg_one_iff (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) : (sgnZ x * sgnZ y = (-1 : ℤ)) ↔ (x * y < 0) := by
  by_cases hxpos : x > 0
  · by_cases hypos : y > 0
    · unfold sgnZ; simp [hxpos, hypos]; nlinarith
    · have hy_not_pos : ¬(y > 0) := hypos
      have hyneg : y < 0 := by by_contra! hge; exact hy (by nlinarith)
      unfold sgnZ; simp [hxpos, hy_not_pos, hyneg]; nlinarith
  · have hx_not_pos : ¬(x > 0) := hxpos
    have hxneg : x < 0 := by by_contra! hge; exact hx (by nlinarith)
    by_cases hypos : y > 0
    · unfold sgnZ; simp [hx_not_pos, hxneg, hypos]; nlinarith
    · have hy_not_pos : ¬(y > 0) := hypos
      have hyneg : y < 0 := by by_contra! hge; exact hy (by nlinarith)
      unfold sgnZ; simp [hx_not_pos, hy_not_pos, hxneg, hyneg]; nlinarith

noncomputable def nonZeroSigns (xs : List ℝ) : List ℤ :=
  (xs.filter (· ≠ 0)).map (fun x => if x > 0 then (1 : ℤ) else (-1 : ℤ))

def computeSignChanges (signs : List ℤ) : ℕ :=
  ((signs.zip signs.tail).filter (fun (a, b) => a * b = (-1 : ℤ))).length