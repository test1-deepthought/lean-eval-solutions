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

-- Set of all points in (a,b) where some entry of the sturm chain has a root
noncomputable def allRoots (p : ℝ[X]) (a b : ℝ) : Finset ℝ :=
  Finset.biUnion ((sturmChain p).toFinset) (fun q => q.roots.toFinset) |>.filter (fun x => a < x ∧ x < b)

lemma allRoots_finite (p : ℝ[X]) (a b : ℝ) : (allRoots p a b : Set ℝ).Finite := by
  apply Finset.finite_toSet

lemma sigma_constant_on_open_interval (p : ℝ[X]) (x y : ℝ) (hxy : x < y)
    (h_no_root : ∀ q ∈ sturmChain p, ∀ z, x < z → z < y → q.eval z ≠ 0) : sigma p x = sigma p y := by
  unfold sigma
  -- Each chain entry q has q.eval x * q.eval y > 0 (same sign) by sign_constant_no_root
  -- So signChanges of the evaluated lists is equal
  -- We'll use induction on the length of the chain
  induction' hchain : sturmChain p with q chain' ih generalizing x y
  · simp
  · have hq : q ∈ sturmChain p := by
      simpa [hchain] using List.mem_cons_self q chain'
    have hq_no_root : ∀ z, x < z → z < y → q.eval z ≠ 0 :=
      h_no_root q hq
    have hq_same_sign : q.eval x * q.eval y > 0 :=
      sign_constant_no_root q x y hxy (by
        intro z hz1 hz2
        by_cases hzx : z = x
        · subst hzx; exact hq_no_root z (by linarith) (by linarith)
        by_cases hzy : z = y
        · subst hzy; exact hq_no_root z (by linarith) (by linarith)
        have : x < z ∧ z < y := by
          constructor <;> linarith
        exact hq_no_root z this.1 this.2)
    have ih' := ih x y hxy (fun q' hq' => h_no_root q' (by
      -- q' ∈ chain' → q' ∈ sturmChain p
      have : q' ∈ sturmChain p := by
        simpa [hchain] using List.mem_cons_of_mem q hq'
      exact this))
    sorry

theorem sturm (p : ℝ[X]) (hp : Squarefree p) {a b : ℝ} (hab : a < b)
    (ha : p.eval a ≠ 0) (hb : p.eval b ≠ 0) :
    ((p.roots.toFinset).filter (fun x => a < x ∧ x < b)).card =
      sigma p a - sigma p b := by
  let P := ((p.roots.toFinset).filter (fun x => a < x ∧ x < b))
  let A := allRoots p a b ∪ {a, b}
  have hA_fin : (A : Set ℝ).Finite := by
    apply Finset.finite_toSet
  -- Sort the points
  let sortedA := A.sort (· ≤ ·)
  have h_sortedA : sortedA.Nodup := Finset.nodup_sort _
  have h_sortedA_len : sortedA.length ≥ 2 := by
    have ha_mem : a ∈ A := by
      apply Finset.mem_union_right
      simp
    have hb_mem : b ∈ A := by
      apply Finset.mem_union_right
      simp
    have ha_pos : a ∈ sortedA := by
      simpa [sortedA] using Finset.mem_sort _ ha_mem
    have hb_pos : b ∈ sortedA := by
      simpa [sortedA] using Finset.mem_sort _ hb_mem
    have hne : a ≠ b := by linarith
    have : a ≠ b := hne
    sorry
  sorry

end Submission