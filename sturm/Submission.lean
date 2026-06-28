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

-- Key lemma: sigma drops by exactly 1 across a simple root of p
lemma sigma_drop_one_at_root (p : ℝ[X]) (hp : Squarefree p) (c r d : ℝ) (hc : c < r) (hr : r < d)
    (hc_ne : p.eval c ≠ 0) (hd_ne : p.eval d ≠ 0) (hr_root : p.eval r = 0) : sigma p c - sigma p d = 1 := by
  -- We use the fact that p'(r) ≠ 0 and all other chain entries are nonzero at r
  -- This lemma will be proved by considering the sorted set of all chain roots in (c,d)
  -- For now, we use a simplified argument
  sorry

theorem sturm (p : ℝ[X]) (hp : Squarefree p) {a b : ℝ} (hab : a < b)
    (ha : p.eval a ≠ 0) (hb : p.eval b ≠ 0) :
    ((p.roots.toFinset).filter (fun x => a < x ∧ x < b)).card =
      sigma p a - sigma p b := by
  let rootsSet := ((p.roots.toFinset).filter (fun x => a < x ∧ x < b))
  -- Strong induction on |rootsSet|
  revert a b hab ha hb
  refine Finset.strongInductionOn rootsSet ?_
  intro R IH a b hab ha hb hR
  by_cases h_empty : R = ∅
  · -- Base case: no roots of p in (a,b)
    subst h_empty
    -- We need sigma(a) = sigma(b)
    -- Let S be the set of non-p chain entry roots in (a,b)
    -- If S is empty, each chain entry has constant sign, so sigma is constant
    -- If S is non-empty, iterate using the triple lemma
    sorry
  · -- Inductive case: at least one root
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
    -- Find a point c between r and the next root of p (or b) such that (r, c) has no roots of p
    -- Use the next root after r in R
    let nextSet := R.filter (λ x => r < x)
    by_cases h_next_empty : nextSet = ∅
    · -- No more roots after r, use c = (r + b)/2
      let c := (r + b) / 2
      have hc_r : r < c := by nlinarith
      have hc_b : c < b := by nlinarith
      have hc_ne : p.eval c ≠ 0 := by
        intro hzero
        have : c ∈ R := by
          rw [hR]
          apply Finset.mem_filter.mpr
          -- c is a root in (a,b)
          sorry
        have : c ∉ R := by
          -- c > r, but no roots after r, so c ∉ R
          sorry
        exact this
      sorry
    · let next := nextSet.min' (Finset.nonempty_iff_ne_empty.mpr h_next_empty)
      sorry

end Submission