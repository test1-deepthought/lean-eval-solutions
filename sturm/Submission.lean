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
    · simp
  rw [h1, h2]
  simp [add_comm]

-- Factorization: p = (X - r) * (p / (X - C r)) when p(r) = 0
lemma factor_at_root (p : ℝ[X]) (r : ℝ) (hr : p.eval r = 0) : p = (X - C r) * (p / (X - C r)) := by
  have h_root : IsRoot p r := by rw [IsRoot, hr]
  simpa using (Polynomial.IsRoot.mul_div_eq h_root)

-- At a simple root r of p, find δ such that for x in (r-δ, r), p(x)*p'(x) < 0,
-- and for y in (r, r+δ), p(y)*p'(y) > 0
lemma sign_change_at_simple_root (p : ℝ[X]) (hp : Squarefree p) (r : ℝ) (hr : p.eval r = 0) :
    ∃ (δ : ℝ), δ > 0 ∧ ∀ (x y : ℝ), r - δ < x → x < r → r < y → y < r + δ → p.eval x * (derivative p).eval x < 0 ∧ p.eval y * (derivative p).eval y > 0 := by
  have hp'_ne : (derivative p).eval r ≠ 0 := separable_derivative_ne_zero p hp r hr
  let q := p / (X - C r)
  have h_factor : p = (X - C r) * q := factor_at_root p r hr
  have hq_eval_r : q.eval r = (derivative p).eval r := by
    -- From p = (X-r)*q, we have p' = q + (X-r)*q'
    -- Evaluating at r: p'(r) = q(r)
    have h_deriv := congrArg derivative h_factor
    -- derivative of (X-r)*q = 1*q + (X-r)*q'
    calc
      q.eval r = ((derivative (X - C r)) * q + (X - C r) * (derivative q)).eval r := by
        simp
      _ = (derivative ((X - C r) * q)).eval r := by
        simp [derivative_mul]
      _ = (derivative p).eval r := by rw [h_factor]
  have hpos : q.eval r * (derivative p).eval r > 0 := by
    rw [hq_eval_r]
    have : (derivative p).eval r * (derivative p).eval r > 0 := sq_pos_iff.mpr hp'_ne
    nlinarith
  have hcont_q : ContinuousAt (fun (t : ℝ) => q.eval t) r := q.continuousAt
  have hcont_p' : ContinuousAt (fun (t : ℝ) => (derivative p).eval t) r := (derivative p).continuousAt
  have hcont_prod : ContinuousAt (fun (t : ℝ) => q.eval t * (derivative p).eval t) r := by
    apply ContinuousAt.mul hcont_q hcont_p'
  rcases hcont_prod (by
    -- The product is > 0 at r, so there's a neighborhood where it's > 0
    have : {z : ℝ | z > 0} ∈ 𝓝 (q.eval r * (derivative p).eval r) := by
      apply IsOpen.mem_nhds isOpen_Ioi
      exact hpos
    exact this) with ⟨δ, hδ, h⟩
  refine ⟨δ, hδ, ?_⟩
  intro x y hx1 hx2 hy1 hy2
  have hx_dist : |x - r| < δ := by
    have : r - δ < x := hx1
    have : x < r := hx2
    rw [abs_lt]
    constructor <;> linarith
  have hy_dist : |y - r| < δ := by
    have : r < y := hy1
    have : y < r + δ := hy2
    rw [abs_lt]
    constructor <;> linarith
  have hx_prod : q.eval x * (derivative p).eval x > 0 := h x (by
    -- show |x - r| < δ
    exact hx_dist)
  have hy_prod : q.eval y * (derivative p).eval y > 0 := h y (by
    exact hy_dist)
  -- Now use factorization: p(t) = (t-r)*q(t)
  -- So p(t)*p'(t) = (t-r)*q(t)*p'(t)
  have hp_eval_x : p.eval x = (x - r) * q.eval x := by
    calc
      p.eval x = ((X - C r) * q).eval x := by rw [h_factor]
      _ = (x - r) * q.eval x := by simp
  have hp_eval_y : p.eval y = (y - r) * q.eval y := by
    calc
      p.eval y = ((X - C r) * q).eval y := by rw [h_factor]
      _ = (y - r) * q.eval y := by simp
  constructor
  · rw [hp_eval_x]
    have : x - r < 0 := by linarith
    have : q.eval x * (derivative p).eval x > 0 := hx_prod
    nlinarith
  · rw [hp_eval_y]
    have : y - r > 0 := by linarith
    have : q.eval y * (derivative p).eval y > 0 := hy_prod
    nlinarith

-- The set of all points in (a,b) where some chain entry has a root
noncomputable def allRoots (p : ℝ[X]) (a b : ℝ) : Finset ℝ :=
  Finset.biUnion ((sturmChain p).toFinset) (fun q => q.roots.toFinset) |>.filter (fun x => a < x ∧ x < b)

theorem sturm (p : ℝ[X]) (hp : Squarefree p) {a b : ℝ} (hab : a < b)
    (ha : p.eval a ≠ 0) (hb : p.eval b ≠ 0) :
    ((p.roots.toFinset).filter (fun x => a < x ∧ x < b)).card =
      sigma p a - sigma p b := by
  let P := ((p.roots.toFinset).filter (fun x => a < x ∧ x < b))
  -- We use the fact that the formula holds when there are no chain entry roots,
  -- and at each chain entry root, the RHS changes by the same amount as the LHS
  
  -- Construct the full sorted list of all chain entry roots in (a,b)
  let A := allRoots p a b
  have hA_fin : A.Finite := Finset.finite_toSet _
  
  -- Prove by strong induction on |A|
  revert a b hab ha hb
  refine Finset.strongInductionOn A ?_
  intro A' IH a b hab ha hb hA'
  
  by_cases h_empty : A' = ∅
  · -- No chain entry roots in (a,b). Then all signs are constant.
    subst h_empty
    -- Every chain entry has no roots in (a,b), so each has the same sign at a and b
    -- Therefore sigma(a) = sigma(b). And there are no roots of p, so both sides are 0.
    have h_no_roots : ∀ q ∈ sturmChain p, ∀ x, a < x → x < b → q.eval x ≠ 0 := by
      intro q hq x hx1 hx2
      intro hzero
      have : x ∈ A' := by
        dsimp [allRoots]
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_biUnion.mpr ⟨q, ?_, ?_⟩, hx1, hx2⟩
        · simpa using hq
        · rw [Polynomial.mem_roots (by
            have hq_ne_zero : q ≠ 0 := by
              intro hzero_q
              have : q.eval x = 0 := by simp [hzero_q]
              exact this
              -- Actually, we don't need q ≠ 0, we just need to know roots are defined
              -- If q = 0, then q has no roots (Multiset.empty), so we can't have x ∈ q.roots
              sorry
            exact hq_ne_zero), hzero]
          exact rfl
      -- But A' is empty, contradiction
      have : A' = ∅ := h_empty
      rw [this] at hx1
      -- Wait, hx1 is a hypothesis, not A'
      -- Actually, we have a contradiction because x ∈ A' but A' = ∅
      simpa [h_empty] using hx1
    sorry
  · -- There is at least one chain entry root
    sorry

end Submission