lemma signChanges_cons_cons (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (l : List ℝ) :
    signChanges (a :: b :: l) = (if a * b < 0 then 1 else 0) + signChanges (b :: l) := by
  dsimp [signChanges]
  have h1 : (a :: b :: l).filter (· ≠ 0) = a :: (b :: l).filter (· ≠ 0) := by simp [ha]
  have h2 : (b :: l).filter (· ≠ 0) = b :: l.filter (· ≠ 0) := by simp [hb]
  rw [h1, h2]
  have htail : (a :: b :: l.filter (· ≠ 0)).tail = b :: l.filter (· ≠ 0) := rfl; rw [htail]
  have hzip : (a :: b :: l.filter (· ≠ 0)).zip (b :: l.filter (· ≠ 0)) = 
    (a, b) :: ((b :: l.filter (· ≠ 0)).zip (l.filter (· ≠ 0))) := by simp; rw [hzip]
  by_cases h : a * b < 0; simp [h, add_comm]; simp [h]