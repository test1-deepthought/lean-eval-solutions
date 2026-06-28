lemma signChanges_cons_nonzero (a b : ℝ) (rest : List ℝ) (ha : a ≠ 0) (hb : b ≠ 0) : 
    signChanges (a :: b :: rest) = (if a * b < 0 then 1 else 0) + signChanges (b :: rest) := by
  dsimp [signChanges]
  have hfilter : (a :: b :: rest).filter (· ≠ 0) = a :: (b :: rest).filter (· ≠ 0) := by simp [ha]
  have hfilter' : (b :: rest).filter (· ≠ 0) = b :: rest.filter (· ≠ 0) := by simp [hb]
  rw [hfilter, hfilter']
  have htail : (a :: b :: rest.filter (· ≠ 0)).tail = b :: rest.filter (· ≠ 0) := by simp
  rw [htail]
  set tail := rest.filter (· ≠ 0) with htail_def
  have hzip : (a :: b :: tail).zip (b :: tail) = (a, b) :: ((b :: tail).zip tail) := by simp
  rw [hzip]
  have hfilter_len : (List.filter (fun (q : ℝ × ℝ) => q.1 * q.2 < 0) ((a, b) :: ((b :: tail).zip tail))).length = 
    (if a * b < 0 then 1 else 0) + (List.filter (fun (q : ℝ × ℝ) => q.1 * q.2 < 0) ((b :: tail).zip tail)).length := by
    by_cases h_ab : a * b < 0; simp [h_ab]; omega; simp [h_ab]
  rw [hfilter_len]
  have htail_tail : (b :: tail).tail = tail := by simp
  simp [htail_tail]