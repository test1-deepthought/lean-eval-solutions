import ChallengeDeps
import Submission.Helpers

open LeanEval.Algebra
open Polynomial
open Set
open scoped Classical

namespace Submission
open Helpers

-- sigmaAux for the sturmAux chain
noncomputable def sigmaAux (a b : ℝ[X]) (n : ℕ) (x : ℝ) : ℕ :=
  signChanges ((sturmAux a b n).map fun q => q.eval x)

lemma sigma_eq_sigmaAux (p : ℝ[X]) (x : ℝ) : sigma p x = sigmaAux p (derivative p) (p.natDegree + 2) x := by
  unfold sigma sigmaAux sturmChain; rfl

-- Helper: product of two continuous functions maintains positivity near a point
lemma pos_product_near (f g : ℝ[X]) (r : ℝ) (hpos : f.eval r * g.eval r > 0) : 
    ∃ δ > 0, ∀ x, |x - r| < δ → f.eval x * g.eval x > 0 := by
  have hcont_f : Continuous (fun x : ℝ => f.eval x) := f.continuous
  have hcont_g : Continuous (fun x : ℝ => g.eval x) := g.continuous
  have hcont_prod : Continuous (fun x : ℝ => f.eval x * g.eval x) := hcont_f.mul hcont_g
  have hopen : IsOpen (Set.Ioi (0 : ℝ)) := isOpen_Ioi
  have hpreim_open : IsOpen ((fun x : ℝ => f.eval x * g.eval x)⁻¹' (Set.Ioi 0)) :=
    hcont_prod.isOpen_preimage (Set.Ioi 0) hopen
  have hmem : r ∈ (fun x : ℝ => f.eval x * g.eval x)⁻¹' (Set.Ioi 0) := hpos
  rcases Metric.isOpen_iff.mp hpreim_open r hmem with ⟨δ, hδ, hball⟩
  refine ⟨δ, hδ, ?_⟩
  intro x hx
  have hx_ball : x ∈ Metric.ball r δ := by
    rw [Metric.mem_ball, Real.dist_eq]; exact hx
  have hx_mem : x ∈ (fun x : ℝ => f.eval x * g.eval x)⁻¹' (Set.Ioi 0) := hball hx_ball
  simpa using hx_mem

-- At a simple root r, p(u)*p'(u) < 0 for u left of r and > 0 for v right of r
lemma sign_change_at_root (p : ℝ[X]) (r : ℝ) (hpderiv : (derivative p).eval r ≠ 0) 
    (hp0 : p.eval r = 0) : ∃ δ > 0, (∀ u, r - δ < u ∧ u < r → p.eval u * (derivative p).eval u < 0) ∧
    (∀ v, r < v ∧ v < r + δ → p.eval v * (derivative p).eval v > 0) := by
  have h_factor : (X - C r) ∣ p := (Polynomial.dvd_iff_isRoot.mpr (by rw [Polynomial.IsRoot]; exact hp0))
  rcases h_factor with ⟨q, h_eq⟩
  have h_deriv : derivative p = q + (X - C r) * derivative q := by
    calc
      derivative p = derivative ((X - C r) * q) := by rw [h_eq]
      _ = derivative (X - C r) * q + (X - C r) * derivative q := by rw [Polynomial.derivative_mul]
      _ = 1 * q + (X - C r) * derivative q := by simp
      _ = q + (X - C r) * derivative q := by simp
  have h_q_eval : q.eval r = (derivative p).eval r := by
    calc q.eval r = (q + (X - C r) * derivative q).eval r := by simp
      _ = (derivative p).eval r := by rw [h_deriv]
  have h_g_pos : q.eval r * (derivative p).eval r > 0 := by
    rw [h_q_eval]; exact mul_self_pos.mpr hpderiv
  rcases pos_product_near q (derivative p) r h_g_pos with ⟨δ, hδ, hpos⟩
  refine ⟨δ, hδ, ?_, ?_⟩
  · intro u ⟨hu_left, hu_right⟩
    have h_abs : |u - r| < δ := by
      have : u - r < 0 := sub_neg.mpr hu_right
      rw [abs_of_neg this]; linarith
    have h_pos_prod : q.eval u * (derivative p).eval u > 0 := hpos u h_abs
    have h_p_eval : p.eval u = (u - r) * q.eval u := by
      rw [h_eq, eval_mul, eval_sub, eval_X, eval_C]; ring
    calc p.eval u * (derivative p).eval u = ((u - r) * q.eval u) * (derivative p).eval u := by rw [h_p_eval]
      _ = (u - r) * (q.eval u * (derivative p).eval u) := by ring
      _ < 0 := by have h_neg : u - r < 0 := sub_neg.mpr hu_right; nlinarith
  · intro v ⟨hv_left, hv_right⟩
    have h_abs : |v - r| < δ := by
      have : v - r > 0 := sub_pos.mpr hv_left
      rw [abs_of_pos this]; linarith
    have h_pos_prod : q.eval v * (derivative p).eval v > 0 := hpos v h_abs
    have h_p_eval : p.eval v = (v - r) * q.eval v := by
      rw [h_eq, eval_mul, eval_sub, eval_X, eval_C]; ring
    calc p.eval v * (derivative p).eval v = ((v - r) * q.eval v) * (derivative p).eval v := by rw [h_p_eval]
      _ = (v - r) * (q.eval v * (derivative p).eval v) := by ring
      _ > 0 := by have h_pos : v - r > 0 := sub_pos.mpr hv_left; nlinarith

-- Main theorem: Sturm's theorem
theorem sturm (p : ℝ[X]) (hp : Squarefree p) {a b : ℝ} (hab : a < b)
    (ha : p.eval a ≠ 0) (hb : p.eval b ≠ 0) :
    ((p.roots.toFinset).filter (fun x => a < x ∧ x < b)).card =
      sigma p a - sigma p b := by
  let R := ((p.roots.toFinset).filter (fun x => a < x ∧ x < b))
  -- The proof requires two key lemmas that are not yet fully formalized:
  -- 1. sigma_drop_at_simple_root: At each simple root r of p, sigma drops by exactly 1.
  --    This requires analyzing the Sturm chain behavior at r, using the triple_sign_lemma
  --    to show that deeper chain entries have invariant contribution across r.
  -- 2. sigma_const_on_interval: On intervals with no p-roots, sigma is constant.
  --    This requires showing that even when interior chain members have roots,
  --    the total sigma is unchanged (using the chain property and triple_sign_lemma).
  -- See failed_submissions/sturm/report.md for the full proof strategy.
  sorry

end Submission