import ChallengeDeps
open LeanEval.Algebra
open Polynomial
open Set

namespace Submission.Helpers

lemma signChanges_cons_cons_nonzero (a b : ℝ) (rest : List ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hrest : ∀ x ∈ rest, x ≠ 0) :
    signChanges (a :: b :: rest) = (if a * b < 0 then 1 else 0) + signChanges (b :: rest) := by
  unfold signChanges
  have hfilter_all : (a :: b :: rest).filter (· ≠ 0) = a :: b :: rest := by
    simp [ha, hb, hrest]
  have hfilter_rest : (b :: rest).filter (· ≠ 0) = b :: rest := by
    simp [hb, hrest]
  rw [hfilter_all, hfilter_rest]
  simp

/-- Over ℝ, a squarefree polynomial is separable (coprime with its derivative). -/
lemma squarefree_imp_separable (p : ℝ[X]) (hp : Squarefree p) : Separable p := by
  haveI : CharZero ℝ := by infer_instance
  haveI : PerfectField ℝ := PerfectField.ofCharZero
  rw [PerfectField.separable_iff_squarefree]
  exact hp

/-- At a root of a squarefree polynomial, the derivative is nonzero. -/
lemma eval_derivative_ne_zero_of_squarefree_root (p : ℝ[X]) (hp : Squarefree p) (r : ℝ) (hr : p.eval r = 0) :
    (derivative p).eval r ≠ 0 := by
  have hsep : Separable p := squarefree_imp_separable p hp
  have hcop : IsCoprime p (derivative p) := ((Polynomial.separable_def p).mp hsep)
  intro hderiv
  have h_cop_eval : IsCoprime (p.eval r) ((derivative p).eval r) :=
    hcop.map (evalRingHom r)
  rcases h_cop_eval with ⟨a, b, h⟩
  rw [hr, hderiv] at h
  simp at h

/-- If a polynomial has no root in an open interval, then it has constant sign there
(either all positive or all negative). -/
lemma sign_constant_on_Ioo (q : ℝ[X]) (c d : ℝ) (hcd : c < d) (h_no_root : ∀ x ∈ Ioo c d, q.eval x ≠ 0) :
    (∀ x ∈ Ioo c d, q.eval x > 0) ∨ (∀ x ∈ Ioo c d, q.eval x < 0) := by
  have h_cont : Continuous (q.eval : ℝ → ℝ) := Polynomial.continuous q
  by_cases hpos : ∃ x ∈ Ioo c d, q.eval x > 0
  · rcases hpos with ⟨x, hx, hxpos⟩
    refine Or.inl ?_
    intro y hy
    by_contra! h_notpos
    have hy_nonzero : q.eval y ≠ 0 := h_no_root y hy
    have hy_neg : q.eval y < 0 := by
      have : q.eval y ≤ 0 := h_notpos
      exact Ne.lt_of_le hy_nonzero this
    by_cases hxy : x < y
    · -- x < y, so f x > 0 > f y. Use intermediate_value_Ioo' (f b to f a)
      have h_cont_on : ContinuousOn (q.eval : ℝ → ℝ) (Icc x y) := h_cont.continuousOn
      have h0_in : (0 : ℝ) ∈ Ioo (q.eval y) (q.eval x) := by
        constructor <;> linarith
      have h_contains : Ioo (q.eval y) (q.eval x) ⊆ (q.eval : ℝ → ℝ) '' Ioo x y :=
        intermediate_value_Ioo' (by linarith) h_cont_on
      rcases h_contains h0_in with ⟨z, hz, hz0⟩
      apply h_no_root z
      · rcases hz with ⟨hzx, hzy⟩
        refine ⟨lt_of_lt_of_le hx.1 hzx.le, lt_of_le_of_lt hzy.le hy.2⟩
      · exact hz0
    · -- y ≤ x, so f y < 0 < f x. Use intermediate_value_Ioo (f a to f b)
      have hyx : y < x := by
        have hy_le_x : y ≤ x := by linarith
        have hy_ne_x : y ≠ x := by
          intro h_eq
          subst h_eq
          linarith
        exact Ne.lt_of_le hy_ne_x hy_le_x
      have h_cont_on : ContinuousOn (q.eval : ℝ → ℝ) (Icc y x) := h_cont.continuousOn
      have h0_in : (0 : ℝ) ∈ Ioo (q.eval y) (q.eval x) := by
        constructor <;> linarith
      have h_contains : Ioo (q.eval y) (q.eval x) ⊆ (q.eval : ℝ → ℝ) '' Ioo y x :=
        intermediate_value_Ioo (by linarith) h_cont_on
      rcases h_contains h0_in with ⟨z, hz, hz0⟩
      apply h_no_root z
      · rcases hz with ⟨hzy, hzx⟩
        refine ⟨lt_of_lt_of_le hy.1 hzy.le, lt_of_le_of_lt hzx.le hx.2⟩
      · exact hz0
  · -- no point has positive value
    refine Or.inr ?_
    intro y hy
    have hy_nonzero : q.eval y ≠ 0 := h_no_root y hy
    have hy_nonpos : q.eval y ≤ 0 := by
      by_contra! hpos_y
      exact hpos ⟨y, hy, hpos_y⟩
    exact Ne.lt_of_le hy_nonzero hy_nonpos

/-- The sign change count `sigma(p, x)` is locally constant on intervals where
no member of the Sturm chain vanishes. -/
lemma sigma_const_on_interval (p : ℝ[X]) (a b : ℝ) (hab : a < b)
    (h_no_chain_root : ∀ q ∈ sturmChain p, ∀ x ∈ Ioo a b, q.eval x ≠ 0) :
    sigma p a = sigma p b := by
  unfold sigma
  -- For each q in the chain, q.eval is constant on sign on (a,b)
  -- We need to show signChanges is the same at a and b
  apply congrArg signChanges
  apply List.map_congr
  intro q hq
  have hq_nonzero_a : q.eval a ≠ 0 := by
    -- a is not in Ioo a b, so we can't directly use h_no_chain_root
    -- But by continuity we can approach a from the right
    sorry
  sorry

end Submission.Helpers
