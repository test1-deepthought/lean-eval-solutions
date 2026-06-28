lemma signChanges_flip_first (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (l : List ℝ) :
    |(signChanges (a :: b :: l) : ℤ) - (signChanges ((-a) :: b :: l) : ℤ)| = 1 := by
  have ha' : -a ≠ 0 := by intro h; apply ha; nlinarith
  have h1 : signChanges (a :: b :: l) = (if a * b < 0 then 1 else 0) + signChanges (b :: l) :=
    signChanges_cons_cons a b ha hb l
  have h2 : signChanges ((-a) :: b :: l) = (if (-a) * b < 0 then 1 else 0) + signChanges (b :: l) :=
    signChanges_cons_cons (-a) b ha' hb l
  rw [h1, h2]
  have hprod : (-a) * b = -(a * b) := by ring; rw [hprod]
  have hz : a * b ≠ 0 := mul_ne_zero ha hb
  by_cases hneg : a * b < 0
  · have hpos : ¬(-(a * b) < 0) := by nlinarith; rw [if_pos hneg, if_neg hpos]; simp
  · have hge : a * b ≥ 0 := by nlinarith
    have hpos : a * b > 0 := lt_of_le_of_ne hge hz.symm
    have hneg' : -(a * b) < 0 := by nlinarith; rw [if_neg hneg, if_pos hneg']; simp