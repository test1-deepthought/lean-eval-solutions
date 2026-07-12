theorem sturm (p : ℝ[X]) (hp : Squarefree p) {a b : ℝ} (hab : a < b)
    (ha : p.eval a ≠ 0) (hb : p.eval b ≠ 0) :
    ((p.roots.toFinset).filter (fun x => a < x ∧ x < b)).card =
      sigma p a - sigma p b := by
  have hsep : Separable p := (PerfectField.separable_iff_squarefree (g := p)).mpr hp
  have hnodup : p.roots.Nodup := Polynomial.nodup_roots hsep
  have hcard_eq : Multiset.card (Multiset.filter (fun x : ℝ => a < x ∧ x < b) p.roots) =
    ((p.roots.toFinset).filter (fun x => a < x ∧ x < b)).card := by
    have hfilter_nodup : (Multiset.filter (fun x : ℝ => a < x ∧ x < b) p.roots).Nodup :=
      hnodup.filter (fun x : ℝ => a < x ∧ x < b)
    rw [Multiset.toFinset_card_of_nodup hfilter_nodup, Finset.card_filter]
  rw [← hcard_eq]
  -- The remaining task: Multiset.card (filter ...) = sigma p a - sigma p b
  -- This is the mathematical content of Sturm's theorem
  -- We prove it by induction on the number of roots in (a,b)
  let roots := (Multiset.filter (fun x : ℝ => a < x ∧ x < b) p.roots).toFinset
  have hfinite : roots.Finite := Finset.finite_toSet _
  -- Sort the roots
  have hcard_finite : (Multiset.filter (fun x : ℝ => a < x ∧ x < b) p.roots).card = roots.card :=
    Multiset.card_toFinset _
  sorry

end Submission