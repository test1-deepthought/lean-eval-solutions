import ChallengeDeps
import Submission.Helpers

open LeanEval.Algebra
open Polynomial
open scoped Classical

set_option autoImplicit false

namespace Submission

open Submission.Helpers

lemma separable_derivative_ne_zero (p : ℝ[X]) (hp : Squarefree p) (r : ℝ) (hr : p.eval r = 0) : (derivative p).eval r ≠ 0 := by
  have hsep : p.Separable := (PerfectField.separable_iff_squarefree (K := ℝ)).mpr hp
  have hcop : IsCoprime p (derivative p) := ((Polynomial.separable_def p).mp hsep)
  rcases hcop with ⟨a, b, h⟩
  have heval := congrArg (fun q => q.eval r) h
  simp [eval_add, eval_mul, eval_one, hr] at heval
  intro hzero
  have : (0 : ℝ) = 1 := by
    calc
      (0 : ℝ) = (b.eval r) * ((derivative p).eval r) := by simp [hzero]
      _ = 1 := heval
  norm_num at this

lemma signChanges_flip_first_diff (a b : ℝ) (l : List ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a * b < 0) :
    signChanges (a :: b :: l) = signChanges ((-a) :: b :: l) + 1 := by
  have ha' : (-a) ≠ 0 := by
    intro hzero
    apply ha
    nlinarith
  have h1 : signChanges (a :: b :: l) = 1 + signChanges (b :: l) := by
    rw [signChanges_cons_cons a b l ha hb]
    simp [hab]
  have h2 : signChanges ((-a) :: b :: l) = signChanges (b :: l) := by
    rw [signChanges_cons_cons (-a) b l ha' hb]
    split_ifs with h
    · exfalso; nlinarith
    · rfl
  rw [h1, h2]
  simp [add_comm]

-- Roots of p that are greater than x
noncomputable def rootsAbove (p : ℝ[X]) (x : ℝ) : ℕ :=
  ((p.roots.toFinset).filter (· > x)).card

lemma rootsAbove_sub_eq (p : ℝ[X]) (a b : ℝ) (hab : a < b) (ha : p.eval a ≠ 0) (hb : p.eval b ≠ 0) :
    rootsAbove p a - rootsAbove p b = ((p.roots.toFinset).filter (fun x => a < x ∧ x < b)).card := by
  -- Note: rootsAbove a = |roots > a| = |roots in (a,b)| + |roots > b|
  -- This holds because a < b, so roots > a = roots in (a,b) ∪ roots > b (disjoint)
  -- Therefore rootsAbove a - rootsAbove b = |roots in (a,b)| (in ℕ with truncated subtraction)
  -- But we need to be careful about truncated subtraction
  -- Let's use a set-theoretic argument
  sorry

-- Main theorem: prove by strong induction on number of roots of p in (a,b)
theorem sturm (p : ℝ[X]) (hp : Squarefree p) {a b : ℝ} (hab : a < b)
    (ha : p.eval a ≠ 0) (hb : p.eval b ≠ 0) :
    ((p.roots.toFinset).filter (fun x => a < x ∧ x < b)).card =
      sigma p a - sigma p b := by
  let rootsSet := ((p.roots.toFinset).filter (fun x => a < x ∧ x < b))
  -- We will prove: sigma p a - sigma p b = rootsSet.card
  -- Equivalent to: rootsAbove p a - rootsAbove p b = sigma p a - sigma p b
  -- Because rootsAbove_sub_eq gives the RHS identity
  -- So we need to show: sigma p a - sigma p b = rootsAbove p a - rootsAbove p b
  -- i.e., D(a) = D(b) where D(x) := sigma p x - rootsAbove p x (subtraction in ℕ)
  -- We show D is constant by strong induction on rootsSet
  
  -- Actually, let's directly prove sigma p a - sigma p b = rootsSet.card by induction on rootsSet
  revert a b hab ha hb
  refine Finset.strongInductionOn rootsSet ?_
  intro R IH a b hab ha hb hR
  -- hR: R = ((p.roots.toFinset).filter (fun x => a < x ∧ x < b))
  by_cases h_empty : R = ∅
  · -- No roots of p in (a,b)
    subst h_empty
    -- Need to show sigma(a) = sigma(b)
    -- This requires a proof that sigma is constant on intervals with no roots of p
    sorry
  · -- There is at least one root
    have h_nonempty : R.Nonempty := Finset.nonempty_iff_ne_empty.mpr h_empty
    let r := R.min' h_nonempty
    have hr_mem : r ∈ R := Finset.min'_mem _ _ h_nonempty
    have hr_root : p.eval r = 0 := by
      rw [hR] at hr_mem
      rcases Finset.mem_filter.mp hr_mem with ⟨hmem, hbounds⟩
      have hmem_roots : r ∈ p.roots := by
        simpa using hmem
      rw [Polynomial.mem_roots (by
        have h_ne_zero : p ≠ 0 := by
          intro hzero
          apply ha
          simp [hzero]
        exact h_ne_zero)] at hmem_roots
      exact hmem_roots
    have hr_a : a < r := by
      rw [hR] at hr_mem
      rcases Finset.mem_filter.mp hr_mem with ⟨_, ⟨hleft, _⟩⟩
      exact hleft
    have hr_b : r < b := by
      rw [hR] at hr_mem
      rcases Finset.mem_filter.mp hr_mem with ⟨_, ⟨_, hright⟩⟩
      exact hright
    -- Let c := (r + b)/2, so r < c < b and there are fewer roots of p in (c,b)
    let c := (r + b) / 2
    have hc_r : r < c := by nlinarith
    have hc_b : c < b := by nlinarith
    have hc_ne : p.eval c ≠ 0 := by
      -- c is not a root of p because between r and the next root (or b) there are no roots
      -- Actually, we don't know if there are roots between r and c. But c is the midpoint
      -- between r and b, so there might be roots in (c,b).
      -- To apply IH we need p(c) ≠ 0. Let's check...
      sorry
    sorry

end Submission