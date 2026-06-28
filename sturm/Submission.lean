import ChallengeDeps
import Submission.Helpers

open LeanEval.Algebra
open Polynomial
open scoped Classical
open Set

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

lemma sign_constant_no_root (q : ℝ[X]) (a b : ℝ) (hab : a < b) (h_no_root : ∀ x, a ≤ x → x ≤ b → q.eval x ≠ 0) : q.eval a * q.eval b > 0 := by
  have h_cont : ContinuousOn (fun x : ℝ => q.eval x) (Icc a b) := by
    simpa using (Polynomial.continuousOn (s := Icc a b) (p := q))
  by_cases h_same_sign : q.eval a * q.eval b > 0
  · exact h_same_sign
  · have h_neg : q.eval a * q.eval b < 0 := by
      by_contra! hge
      have hzero : q.eval a * q.eval b = 0 := by nlinarith
      have ha0 : q.eval a ≠ 0 := h_no_root a (by linarith) (by linarith)
      have hb0 : q.eval b ≠ 0 := h_no_root b (by linarith) (by linarith)
      exact mul_ne_zero ha0 hb0 hzero
    by_cases ha_pos : q.eval a > 0
    · have hb_neg : q.eval b < 0 := by nlinarith
      have h0 : (0 : ℝ) ∈ Ioo (q.eval b) (q.eval a) := by
        constructor <;> nlinarith
      have h_ivt : (0 : ℝ) ∈ (fun x : ℝ => q.eval x) '' (Ioo a b) :=
        (intermediate_value_Ioo' (by linarith : a ≤ b) h_cont) h0
      rcases h_ivt with ⟨c, ⟨hca, hcb⟩, hc_eq⟩
      exfalso
      exact h_no_root c (hca.le) (hcb.le) hc_eq
    · have ha_neg : q.eval a < 0 := by
        by_contra! hge
        have : q.eval a ≥ 0 := hge
        have : q.eval a = 0 := by nlinarith
        exact h_no_root a (by linarith) (by linarith) this
      have hb_pos : q.eval b > 0 := by nlinarith
      have h0 : (0 : ℝ) ∈ Ioo (q.eval a) (q.eval b) := by
        constructor <;> nlinarith
      have h_ivt : (0 : ℝ) ∈ (fun x : ℝ => q.eval x) '' (Ioo a b) :=
        (intermediate_value_Ioo (by linarith : a ≤ b) h_cont) h0
      rcases h_ivt with ⟨c, ⟨hca, hcb⟩, hc_eq⟩
      exfalso
      exact h_no_root c (hca.le) (hcb.le) hc_eq

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

-- The main theorem: number of roots of p in (a,b) equals sigma(a) - sigma(b)
theorem sturm (p : ℝ[X]) (hp : Squarefree p) {a b : ℝ} (hab : a < b)
    (ha : p.eval a ≠ 0) (hb : p.eval b ≠ 0) :
    ((p.roots.toFinset).filter (fun x => a < x ∧ x < b)).card =
      sigma p a - sigma p b := by
  -- Let R = roots of p in (a,b)
  let R := ((p.roots.toFinset).filter (fun x => a < x ∧ x < b))
  -- We'll prove this by strong induction on |R|
  revert a b hab ha hb
  refine Finset.strongInductionOn R ?_
  intro R IH a b hab ha hb hR
  by_cases h_empty : R = ∅
  · -- Case 1: No roots of p in (a,b). Need sigma(a) = sigma(b)
    subst h_empty
    -- Use the fact that non-p chain entry roots don't affect sigma
    -- and the triple lemma
    -- Let S = all chain entry roots (including p) in (a,b)
    -- If S = ∅, all signs constant, sigma(a) = sigma(b)
    -- If S ≠ ∅, use induction on |S|
    -- Actually, since p has no roots, S only has non-p roots
    -- Process them one by one, using the fact that sigma doesn't change at each
    sorry
  · -- Case 2: There is at least one root of p in (a,b)
    have h_nonempty : R.Nonempty := Finset.nonempty_iff_ne_empty.mpr h_empty
    let r := R.min' h_nonempty
    have hr_mem : r ∈ R := Finset.min'_mem _ _ h_nonempty
    have hr_root : p.eval r = 0 := by
      rw [hR] at hr_mem
      rcases Finset.mem_filter.mp hr_mem with ⟨hmem, hbounds⟩
      have hmem_roots : r ∈ p.roots := by simpa using hmem
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
    -- Let R' = R \ {r}
    let R' := R.erase r
    have hR'card : R'.card < R.card := Finset.card_erase_lt_of_mem hr_mem
    -- Find a point c ∈ (r, b) with no roots of p in (r, c), to apply IH
    -- For that, find the next root after r, or use b if none
    let nextRoots := R.filter (λ x => r < x)
    by_cases h_next_empty : nextRoots = ∅
    · -- No more roots after r, use c = (r + b)/2
      let c := (r + b) / 2
      have hc_r : r < c := by nlinarith
      have hc_b : c < b := by nlinarith
      have hc_ne : p.eval c ≠ 0 := by
        intro hzero
        have hc_mem : c ∈ R := by
          rw [hR]
          apply Finset.mem_filter.mpr
          refine ⟨?_, hc_r, hc_b⟩
          -- c is a root of p
          -- Use the factorization p(c) = 0
          -- But we need c ∈ p.roots
          have : c ∈ p.roots := by
            rw [Polynomial.mem_roots (by
              have h_ne_zero : p ≠ 0 := by
                intro hzero_p
                apply ha
                simp [hzero_p]
              exact h_ne_zero), hzero]
            exact rfl
          exact this
        -- But c > r and there are no more roots, so c ∉ R. Contradiction.
        have : c ∉ R := by
          intro hcR
          have : c ∈ nextRoots := by
            apply Finset.mem_filter.mpr
            exact ⟨hcR, hc_r⟩
          rw [h_next_empty] at this
          exact Finset.not_mem_empty _ this
        exact this hc_mem
      -- Now we have: root r in (a,c), no other roots in (a,c), and R' has |R|-1 roots in (c,b)
      -- Need to show: sigma(a) - sigma(c) = 1 and sigma(c) - sigma(b) = |R'|
      sorry
    · let next := nextRoots.min' (Finset.nonempty_iff_ne_empty.mpr h_next_empty)
      sorry

end Submission