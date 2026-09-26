import Mathlib
open scoped Classical

namespace SC

noncomputable def signChanges (xs : List ℝ) : ℕ :=
  let ys := xs.filter (· ≠ 0)
  ((ys.zip ys.tail).filter (fun q => q.1 * q.2 < 0)).length

lemma signChanges_cons_cons (a b : ℝ) (t : List ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    signChanges (a :: b :: t) = (if a * b < 0 then 1 else 0) + signChanges (b :: t) := by
  unfold signChanges
  simp only
  rw [List.filter_cons_of_pos (by simpa using ha), List.filter_cons_of_pos (by simpa using hb)]
  simp only [List.zip_cons_cons, List.tail_cons, List.filter_cons]
  by_cases h : a * b < 0
  · simp only [h, decide_true, if_true, List.length_cons]
    omega
  · rw [if_neg (by simp [h])]
    simp only [h, decide_false, Bool.false_eq_true, if_false, List.length_cons, zero_add]

end SC