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

lemma factor_at_root (p : ℝ[X]) (r : ℝ) (hr : p.eval r = 0) : p = (X - C r) * (p / (X - C r)) := by
  have h_root : IsRoot p r := by rw [IsRoot, hr]
  simpa using (Polynomial.IsRoot.mul_div_eq h_root)

lemma sign_change_at_simple_root (p : ℝ[X]) (hp : Squarefree p) (r : ℝ) (hr : p.eval r = 0) :
    ∃ (δ : ℝ), δ > 0 ∧ ∀ (x y : ℝ), r - δ < x → x < r → r < y → y < r + δ → p.eval x * (derivative p).eval x < 0 ∧ p.eval y * (derivative p).eval y > 0 := by
  have hp'_ne : (derivative p).eval r ≠ 0 := separable_derivative_ne_zero p hp r hr
  let q := p / (X - C r)
  have h_factor : p = (X - C r) * q := factor_at_root p r hr
  have hq_eval_r : q.eval r = (derivative p).eval r := by
    have h_deriv := congrArg derivative h_factor
    calc
      q.eval r = ((derivative (X - C r)) * q + (X - C r) * (derivative q)).eval r := by simp
      _ = (derivative ((X - C r) * q)).eval r := by simp [derivative_mul]
      _ = (derivative p).eval r := by rw [h_factor]
  have hpos : q.eval r * (derivative p).eval r > 0 := by
    rw [hq_eval_r]
    have : (derivative p).eval r * (derivative p).eval r > 0 := sq_pos_iff.mpr hp'_ne
    nlinarith
  have hcont_q : ContinuousAt (fun (t : ℝ) => q.eval t) r := q.continuousAt
  have hcont_p' : ContinuousAt (fun (t : ℝ) => (derivative p).eval t) r := (derivative p).continuousAt
  have hcont_prod : ContinuousAt (fun (t : ℝ) => q.eval t * (derivative p).eval t) r :=
    ContinuousAt.mul hcont_q hcont_p'
  rcases hcont_prod (by
    have : {z : ℝ | z > 0} ∈ 𝓝 (q.eval r * (derivative p).eval r) :=
      IsOpen.mem_nhds isOpen_Ioi hpos
    exact this) with ⟨δ, hδ, h⟩
  refine ⟨δ, hδ, ?_⟩
  intro x y hx1 hx2 hy1 hy2
  have hx_dist : |x - r| < δ := by
    rw [abs_lt]; constructor <;> linarith
  have hy_dist : |y - r| < δ := by
    rw [abs_lt]; constructor <;> linarith
  have hx_prod : q.eval x * (derivative p).eval x > 0 := h x hx_dist
  have hy_prod : q.eval y * (derivative p).eval y > 0 := h y hy_dist
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
    nlinarith
  · rw [hp_eval_y]
    have : y - r > 0 := by linarith
    nlinarith

-- At a simple root of p, the first entry of the chain flips sign relative to the second,
-- causing sigma to drop by exactly 1
lemma sigma_drop_at_simple_root (p : ℝ[X]) (hp : Squarefree p) (a r b : ℝ) (ha : a < r) (hr : r < b)
    (ha_ne : p.eval a ≠ 0) (hb_ne : p.eval b ≠ 0) (hr_root : p.eval r = 0) : sigma p a - sigma p b = 1 := by
  rcases sign_change_at_simple_root p hp r hr_root with ⟨δ, hδ, h⟩
  -- Choose x and y within (r-δ, r) and (r, r+δ) respectively, and also within (a,b)
  let x := max a (r - δ/2)
  let y := min b (r + δ/2)
  sorry

theorem sturm (p : ℝ[X]) (hp : Squarefree p) {a b : ℝ} (hab : a < b)
    (ha : p.eval a ≠ 0) (hb : p.eval b ≠ 0) :
    ((p.roots.toFinset).filter (fun x => a < x ∧ x < b)).card =
      sigma p a - sigma p b := by
  sorry

end Submission