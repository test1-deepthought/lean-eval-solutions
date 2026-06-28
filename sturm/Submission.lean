import ChallengeDeps
import Submission.Helpers

open LeanEval.Algebra
open Polynomial
open scoped Classical

set_option autoImplicit false

namespace Submission

open Submission.Helpers

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
    have hpos : (-a) * b > 0 := by nlinarith
    simp [hpos]
  rw [h1, h2]
  simp [add_comm]

-- Sigma doesn't change at a root of a non-first chain entry
lemma sigma_invariant_at_non_p_root (p : ℝ[X]) (c r d : ℝ) (hc : c < r) (hr : r < d)
    (h_no_p_root : p.eval r ≠ 0) (h_nonzero : ∀ q ∈ sturmChain p, q.eval r = 0 → q ≠ p)
    (h_chain_root : ∃ (q : ℝ[X]), q ∈ sturmChain p ∧ q ≠ p ∧ q.eval r = 0) : sigma p c - sigma p d = 0 := by
  sorry

-- Main theorem
theorem sturm (p : ℝ[X]) (hp : Squarefree p) {a b : ℝ} (hab : a < b)
    (ha : p.eval a ≠ 0) (hb : p.eval b ≠ 0) :
    ((p.roots.toFinset).filter (fun x => a < x ∧ x < b)).card =
      sigma p a - sigma p b := by
  -- Let R be the set of distinct roots of p in (a,b)
  let R := ((p.roots.toFinset).filter (fun x => a < x ∧ x < b))
  -- We need: |R| = sigma(p,a) - sigma(p,b)
  -- Use strong induction on |R|
  revert a b hab ha hb
  refine Finset.strongInductionOn R ?_
  intro R IH a b hab ha hb hR
  -- hR: R = ((p.roots.toFinset).filter (fun x => a < x ∧ x < b))
  by_cases h_empty : R = ∅
  · -- Base case: no roots of p in (a,b)
    subst h_empty
    -- Need to show sigma(p,a) = sigma(p,b)
    -- Since p has no roots in (a,b), any chain entry root doesn't affect sigma
    -- Construct the set of all chain entry roots in (a,b)
    sorry
  · -- Inductive case: there is at least one root of p in (a,b)
    -- Let r be the smallest such root
    have h_nonempty : R.Nonempty := Finset.nonempty_iff_ne_empty.mpr h_empty
    let r := R.min' h_nonempty
    have hr_mem : r ∈ R := Finset.min'_mem _ _ h_nonempty
    have hr_root : p.eval r = 0 := by
      rw [hR] at hr_mem
      have hmem : r ∈ (p.roots.toFinset) := by
        simpa [Finset.mem_filter] using hr_mem
      rw [Finset.mem_filter] at hr_mem
      rcases hr_mem with ⟨hmem, hbounds⟩
      have hroot : r ∈ p.roots := by simpa using hmem
      rw [Polynomial.mem_roots (by
        have : Squarefree p := hp
        have h_ne_zero : p ≠ 0 := by
          intro hzero
          apply ha
          simpa [hzero] using hzero
        exact h_ne_zero)] at hroot
      exact hroot
    have hr_a : a < r := by
      rw [hR] at hr_mem
      rcases Finset.mem_filter.mp hr_mem with ⟨_, ⟨hleft, _⟩⟩
      exact hleft
    have hr_b : r < b := by
      rw [hR] at hr_mem
      rcases Finset.mem_filter.mp hr_mem with ⟨_, ⟨_, hright⟩⟩
      exact hright
    -- Find a point c between a and r with no roots in (c,r) except possibly r
    -- and a point d between r and b with no roots in (r,d)
    -- Use the midpoint between r and the next point in R ∪ {b}
    let R' := R.erase r
    have hR'card : R'.card < R.card := Finset.card_erase_lt_of_mem hr_mem
    -- Find c ∈ (a, r) such that no chain entry has a root in (c, r)
    -- Find d ∈ (r, b) such that no chain entry has a root in (r, d)
    -- Use the fact that the set of chain entry roots in (a,b) is finite
    sorry

end Submission