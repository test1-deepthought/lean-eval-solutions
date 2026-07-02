lemma signChanges_map_eq_of_forall_mul_pos {α : Type} (f g : α → ℝ) (l : List α) (h : ∀ a ∈ l, f a * g a > 0) : 
    signChanges (l.map f) = signChanges (l.map g) := by
  calc
    signChanges (l.map f) = computeSignChanges (nonZeroSigns (l.map f)) := by rw [signChanges_eq_compute]
    _ = computeSignChanges (nonZeroSigns (l.map g)) := by rw [nonZeroSigns_map_eq f g l h]
    _ = signChanges (l.map g) := by rw [signChanges_eq_compute]