lemma sigma_constant_no_chain_root (p : ℝ[X]) {a b : ℝ} (hab : a ≤ b)
    (h_no_root : ∀ q ∈ sturmChain p, ∀ x ∈ Icc a b, q.eval x ≠ 0) : sigma p a = sigma p b := by
  unfold sigma
  have h_same_sign : ∀ q ∈ sturmChain p, q.eval a * q.eval b > 0 := by
    intro q hq; exact same_sign_if_no_root q hab (h_no_root q hq)
  exact signChanges_map_eq_of_forall_mul_pos (fun q : ℝ[X] => q.eval a) (fun q => q.eval b) (sturmChain p) h_same_sign