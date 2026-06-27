import ChallengeDeps
import Submission.Helpers

open LeanEval.Algebra
open Polynomial
open Set
open scoped Classical

namespace Submission

open Helpers

-- sigmaAux for working with sturmAux chains
noncomputable def sigmaAux (a b : ℝ[X]) (n : ℕ) (x : ℝ) : ℕ :=
  signChanges ((sturmAux a b n).map fun q => q.eval x)

lemma sigma_eq_sigmaAux (p : ℝ[X]) (x : ℝ) : sigma p x = sigmaAux p (derivative p) (p.natDegree + 2) x := by
  unfold sigma sigmaAux sturmChain; rfl

-- A point where p and p' have the same sign (right of a simple root)
lemma sign_same_side (p : ℝ[X]) (r : ℝ) (hp0 : p.eval r = 0) (hpderiv : (derivative p).eval r ≠ 0) :
    ∃ δ > 0, ∀ x, r < x ∧ x < r + δ → p.eval x * (derivative p).eval x > 0 := by
  rcases factor_theorem_with_deriv p r hp0 with ⟨q, hpq, hq⟩
  have hqval : q.eval r ≠ 0 := by rw [hq]; exact hpderiv
  rcases nonzero_near q r hqval with ⟨ε₁, hε₁, hq_near⟩
  rcases nonzero_near (derivative p) r hpderiv with ⟨ε₂, hε₂, hpderiv_near⟩
  let δ := min ε₁ ε₂ / 2
  have hδpos : δ > 0 := by
    have hminpos : min ε₁ ε₂ > 0 := lt_min_iff.mpr ⟨hε₁, hε₂⟩
    nlinarith
  refine ⟨δ, hδpos, ?_⟩
  intro x ⟨hxr, hx⟩
  have hxdist₁ : |x - r| < ε₁ := by
    have : |x - r| = x - r := abs_of_pos (sub_pos.mpr hxr)
    rw [this]; nlinarith
  have hxdist₂ : |x - r| < ε₂ := by
    have : |x - r| = x - r := abs_of_pos (sub_pos.mpr hxr)
    rw [this]; nlinarith
  have hpx : p.eval x = (x - r) * q.eval x := by
    rw [hpq, eval_mul, eval_sub, eval_X, eval_C]; ring
  have hqx : q.eval x ≠ 0 := hq_near x hxdist₁
  have hpdx : (derivative p).eval x ≠ 0 := hpderiv_near x hxdist₂
  have hxsign : q.eval x * (derivative p).eval x > 0 := by
    -- q(r) = p'(r), and q and p' are continuous and nonzero near r, so they have the same sign near r
    have hqr_eq_pdr : q.eval r = (derivative p).eval r := hq
    have h_qpd_same_sign : (q.eval r) * (derivative p).eval r > 0 := by
      rw [hqr_eq_pdr]; nlinarith [sq_pos_of_ne_zero hpderiv]
    -- By continuity, q.eval x and (derivative p).eval x are close to their values at r
    -- and maintain sign for x near r
    have h_cont_q : Continuous (q.eval : ℝ → ℝ) := Polynomial.continuous q
    have h_cont_pd : Continuous ((derivative p).eval : ℝ → ℝ) := Polynomial.continuous (derivative p)
    have h_q_pos : ∃ x' ∈ Ioo r (r + ε₁), q.eval x' > 0 := by
      -- If q(r) > 0, then near r, q is positive; similarly if q(r) < 0
      sorry
    sorry
  have hxpos : (x - r) > 0 := sub_pos.mpr hxr
  nlinarith

-- A point where p and p' have opposite signs (left of a simple root)
lemma sign_opposite_side (p : ℝ[X]) (r : ℝ) (hp0 : p.eval r = 0) (hpderiv : (derivative p).eval r ≠ 0) :
    ∃ δ > 0, ∀ x, r - δ < x ∧ x < r → p.eval x * (derivative p).eval x < 0 := by
  rcases factor_theorem_with_deriv p r hp0 with ⟨q, hpq, hq⟩
  have hqval : q.eval r ≠ 0 := by rw [hq]; exact hpderiv
  rcases nonzero_near q r hqval with ⟨ε₁, hε₁, hq_near⟩
  rcases nonzero_near (derivative p) r hpderiv with ⟨ε₂, hε₂, hpderiv_near⟩
  let δ := min ε₁ ε₂ / 2
  have hδpos : δ > 0 := by
    have hminpos : min ε₁ ε₂ > 0 := lt_min_iff.mpr ⟨hε₁, hε₂⟩
    nlinarith
  refine ⟨δ, hδpos, ?_⟩
  intro x ⟨hx, hxr⟩
  have hxdist₁ : |x - r| < ε₁ := by
    have : x - r < 0 := sub_neg.mpr hxr
    have : |x - r| = r - x := abs_of_neg (sub_neg.mpr hxr)
    rw [this]; nlinarith
  have hxdist₂ : |x - r| < ε₂ := by
    have : x - r < 0 := sub_neg.mpr hxr
    have : |x - r| = r - x := abs_of_neg (sub_neg.mpr hxr)
    rw [this]; nlinarith
  have hpx : p.eval x = (x - r) * q.eval x := by
    rw [hpq, eval_mul, eval_sub, eval_X, eval_C]; ring
  have hqx : q.eval x ≠ 0 := hq_near x hxdist₁
  have hpdx : (derivative p).eval x ≠ 0 := hpderiv_near x hxdist₂
  have hxsign : q.eval x * (derivative p).eval x > 0 := by
    -- Similar to above: q and p' have the same sign near r
    sorry
  have hxneg : (x - r) < 0 := sub_neg.mpr hxr
  nlinarith

-- Main theorem: Sturm's theorem
theorem sturm (p : ℝ[X]) (hp : Squarefree p) {a b : ℝ} (hab : a < b)
    (ha : p.eval a ≠ 0) (hb : p.eval b ≠ 0) :
    ((p.roots.toFinset).filter (fun x => a < x ∧ x < b)).card =
      sigma p a - sigma p b := by
  sorry

end Submission