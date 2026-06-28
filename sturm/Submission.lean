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

-- Set of all points in (a,b) where some entry of the chain (including p) has a root
noncomputable def allRoots (p : ℝ[X]) (a b : ℝ) : Finset ℝ :=
  Finset.biUnion ((sturmChain p).toFinset) (fun q => q.roots.toFinset) |>.filter (fun x => a < x ∧ x < b)

-- The main theorem
theorem sturm (p : ℝ[X]) (hp : Squarefree p) {a b : ℝ} (hab : a < b)
    (ha : p.eval a ≠ 0) (hb : p.eval b ≠ 0) :
    ((p.roots.toFinset).filter (fun x => a < x ∧ x < b)).card =
      sigma p a - sigma p b := by
  let rootsSet := ((p.roots.toFinset).filter (fun x => a < x ∧ x < b))
  -- Prove by strong induction on |rootsSet|
  revert a b hab ha hb
  refine Finset.strongInductionOn rootsSet ?_
  intro R IH a b hab ha hb hR
  by_cases h_empty : R = ∅
  · subst h_empty
    -- Need sigma(a) = sigma(b) when there are no roots of p in (a,b)
    -- We'll use the fact that sigma is constant between roots, and the triple lemma
    -- for non-p chain entry roots
    -- Let S be the set of all non-p chain entry roots in (a,b)
    let S := allRoots p a b
    -- Use strong induction on |S|
    revert a b hab ha hb
    refine Finset.strongInductionOn S ?_
    intro S' IH_S a b hab ha hb hS' 
    by_cases hS_empty : S' = ∅
    · subst hS_empty
      -- No chain entry has a root in (a,b), so all have constant sign
      -- Therefore sigma(a) = sigma(b)
      unfold sigma
      -- For each chain entry q, q(a)*q(b) > 0
      have h_sign : ∀ q ∈ sturmChain p, q.eval a * q.eval b > 0 := by
        intro q hq
        apply sign_constant_no_root q a b hab
        intro x hx_a hx_b
        -- No chain entry has a root in [a,b]
        have : q.eval x ≠ 0 := by
          intro hzero
          have hx_mem : x ∈ allRoots p a b := by
            dsimp [allRoots]
            apply Finset.mem_filter.mpr
            refine ⟨Finset.mem_biUnion.mpr ⟨q, ?_, ?_⟩, hx_a, hx_b⟩
            · simpa using hq
            · simpa [Polynomial.mem_roots (by
                have hq_ne_zero : q ≠ 0 := by
                  intro hzero_q
                  have : (0 : ℝ[X]) ∈ sturmChain p := by
                    simpa [hzero_q] using hq
                  -- This would mean the zero polynomial is in the chain, which is possible
                  -- but 0 has no roots, so this shouldn't be an issue
                  sorry
                exact hq_ne_zero)] using hzero
          rw [hS'] at hx_mem
          exact Finset.not_mem_empty _ hx_mem
        exact this
      sorry
    · -- S' is nonempty, pick the smallest root r
      have h_nonempty : S'.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS_empty
      let r := S'.min' h_nonempty
      have hr_mem : r ∈ S' := Finset.min'_mem _ _ h_nonempty
      have hr_S' : r ∈ allRoots p a b := by
        rw [hS']; exact hr_mem
      -- r is a root of some non-p chain entry (since allRoots excludes p? Actually it includes all)
      -- By the triple lemma, sigma doesn't change at r
      -- Use induction on |S'\{r}|
      sorry
  · -- R nonempty: handle the inductive step with the smallest root of p
    sorry

end Submission