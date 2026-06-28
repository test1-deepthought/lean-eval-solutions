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

-- If the first two entries have opposite signs, signChanges is different from the flipped version
lemma signChanges_opposite_vs_same (a b : ℝ) (l : List ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a * b < 0) :
    signChanges (a :: b :: l) = signChanges (b :: l) + 1 := by
  rw [signChanges_cons_cons a b l ha hb]
  simp [hab]

lemma signChanges_same_sign (a b : ℝ) (l : List ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hpos : a * b > 0) :
    signChanges (a :: b :: l) = signChanges (b :: l) := by
  rw [signChanges_cons_cons a b l ha hb]
  simp [hpos]

-- The Sturm theorem
theorem sturm (p : ℝ[X]) (hp : Squarefree p) {a b : ℝ} (hab : a < b)
    (ha : p.eval a ≠ 0) (hb : p.eval b ≠ 0) :
    ((p.roots.toFinset).filter (fun x => a < x ∧ x < b)).card =
      sigma p a - sigma p b := by
  -- The set of roots of p in (a,b)
  let R := ((p.roots.toFinset).filter (fun x => a < x ∧ x < b))
  -- We'll construct a sequence of points from a to b, passing through each root,
  -- and show that sigma drops by exactly 1 between consecutive points
  -- Sort the roots
  let sortedR := R.sort (· ≤ ·)
  -- Construct the sequence: a, then the roots in order, then b
  let points := a :: (sortedR ++ [b])
  -- We'll prove by induction on points that sigma(a) - sigma(last) = |R|
  -- For each consecutive pair (x,y) in points, we need sigma(x) - sigma(y) = 1 if y ∈ R, 0 otherwise
  
  -- Actually, let's prove this by strong induction on |R|
  revert a b hab ha hb
  refine Finset.strongInductionOn R ?_
  intro R IH a b hab ha hb hR
  by_cases h_empty : R = ∅
  · -- No roots: need sigma(a) = sigma(b)
    subst h_empty
    -- Since there are no roots of p, and non-p chain roots don't affect sigma,
    -- we have sigma(a) = sigma(b)
    -- The key insight: sigma only changes at roots of p, so it's constant elsewhere
    -- Let's prove that if p has no roots in (a,b), then sigma(a) = sigma(b)
    -- We'll use the fact that signChanges is determined by the chain,
    -- and at any point where a non-p entry crosses zero, sigma is unchanged
    
    -- For each entry q in the chain, q(a) and q(b) have the same sign (since no roots)
    -- For non-p entries that cross zero in (a,b), the triple lemma keeps sigma unchanged
    -- Therefore sigma(a) = sigma(b)
    
    -- Replace with a simpler argument: the minimum and maximum sigma values
    -- Since sigma is ℕ-valued and we can compute it, the equality must hold
    -- because both sides equal the number of roots of p in (a,b) = 0
    
    -- Use the trivial fact that sigma(a) ≥ sigma(b) (sigma is nonincreasing)
    -- and the interval has no roots, so sigma(a) = sigma(b)
    sorry
  · -- There are roots
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
    -- Let c be a point between r and the next root (or b) with no roots of p in (r, c)
    -- Use c = (r + next)/2 where next is the next root or b
    -- Let R' = R \ {r}
    let R' := R.erase r
    have hR'card : R'.card < R.card := Finset.card_erase_lt_of_mem hr_mem
    -- We need to find c such that:
    -- 1. r < c < b
    -- 2. No roots of p in (r, c)
    -- 3. p(c) ≠ 0
    -- Then: sigma(a) - sigma(c) = 1 (by the lemma about drop at simple root)
    -- and sigma(c) - sigma(b) = |R'| (by IH on (c,b))
    -- So sigma(a) - sigma(b) = 1 + |R'| = |R|
    
    -- Let next = min {x ∈ R | x > r} or b if none
    let nextSet := R.filter (λ x => r < x)
    by_cases h_next_empty : nextSet = ∅
    · -- No next root, use c = (r + b)/2
      let c := (r + b) / 2
      have hc_r : r < c := by nlinarith
      have hc_b : c < b := by nlinarith
      have hc_ne : p.eval c ≠ 0 := by
        intro hzero
        have hc_mem : c ∈ R := by
          rw [hR]
          apply Finset.mem_filter.mpr
          refine ⟨by
            -- c ∈ p.roots because p(c) = 0
            rw [Polynomial.mem_roots (by
              have h_ne_zero : p ≠ 0 := by
                intro hzero_p
                apply ha
                simp [hzero_p]
              exact h_ne_zero), hzero]
            trivial, hc_r, hc_b⟩
        have hc_not_mem : c ∉ R := by
          intro hcR
          have : c ∈ nextSet := Finset.mem_filter.mpr ⟨hcR, hc_r⟩
          rw [h_next_empty] at this
          exact Finset.not_mem_empty _ this
        exact hc_not_mem hc_mem
      -- By IH on (c, b) (since R' = R \ {r} = R because R only has r)
      have hR'empty : R' = ∅ := by
        apply Finset.eq_empty_iff_forall_not_mem.mpr
        intro x hx
        have hxR : x ∈ R := Finset.mem_of_mem_erase hx
        have hx_ne_r : x ≠ r := Finset.ne_of_mem_erase hx
        have hx_gt_r : r < x := by
          by_contra! hle
          have : x < r ∨ x = r := by
            have : x ≤ r := hle
            -- Since x ∈ R, a < x < b. Since r = min R, we have r ≤ x
            -- So either x = r or r < x. But x ≠ r, so r < x
            sorry
          sorry
        -- Since x ∈ R and x > r, x ∈ nextSet, contradicting h_next_empty
        have : x ∈ nextSet := Finset.mem_filter.mpr ⟨hxR, hx_gt_r⟩
        rw [h_next_empty] at this
        exact Finset.not_mem_empty _ this
      -- Apply IH to (c, b)
      sorry
    · let nextRoot := nextSet.min' (Finset.nonempty_iff_ne_empty.mpr h_next_empty)
      sorry

end Submission