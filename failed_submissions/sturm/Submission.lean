import ChallengeDeps
import Submission.Helpers

open LeanEval.Algebra
open Polynomial
open Set
open scoped Classical

namespace Submission

lemma sigma_drop_at_simple_root (p : ℝ[X]) (hp : Squarefree p) (r : ℝ) (hr : p.eval r = 0) :
    ∃ δ > 0, ∀ u ∈ Ioo (r - δ) r, ∀ v ∈ Ioo r (r + δ), sigma p u - sigma p v = 1 := by
  have hderiv_ne_zero : (derivative p).eval r ≠ 0 :=
    eval_derivative_ne_zero_of_squarefree_root p hp r hr
  rcases factor_theorem_with_deriv p r hr with ⟨q, hpq, hqr⟩
  have hq_ne_zero : q.eval r ≠ 0 := by rwa [hqr]
  have hq_nonzero_near : ∃ ε₁ > 0, ∀ x ∈ Ioo (r - ε₁) (r + ε₁), q.eval x ≠ 0 := 
    nonzero_near q r hq_ne_zero
  have hpderiv_nonzero_near : ∃ ε₂ > 0, ∀ x ∈ Ioo (r - ε₂) (r + ε₂), (derivative p).eval x ≠ 0 :=
    nonzero_near (derivative p) r hderiv_ne_zero
  rcases hq_nonzero_near with ⟨ε₁, hε₁, hq_nonzero⟩
  rcases hpderiv_nonzero_near with ⟨ε₂, hε₂, hpderiv_nonzero⟩
  let δ := min ε₁ ε₂ / 2
  have hδpos : δ > 0 := by
    dsimp [δ]; have hminpos : min ε₁ ε₂ > 0 := lt_min_iff.mpr ⟨hε₁, hε₂⟩; nlinarith
  have hq_sign : (∀ x ∈ Ioo (r - δ) (r + δ), q.eval x > 0) ∨ (∀ x ∈ Ioo (r - δ) (r + δ), q.eval x < 0) := by
    apply sign_constant_on_Ioo q (r - δ) (r + δ) (by nlinarith)
    intro x hx; apply hq_nonzero x; rcases hx with ⟨hxl, hxr⟩; exact ⟨by nlinarith, by nlinarith⟩
  have hpderiv_sign : (∀ x ∈ Ioo (r - δ) (r + δ), (derivative p).eval x > 0) ∨ (∀ x ∈ Ioo (r - δ) (r + δ), (derivative p).eval x < 0) := by
    apply sign_constant_on_Ioo (derivative p) (r - δ) (r + δ) (by nlinarith)
    intro x hx; apply hpderiv_nonzero x; rcases hx with ⟨hxl, hxr⟩; exact ⟨by nlinarith, by nlinarith⟩
  -- The proof of sigma_drop_at_simple_root requires analyzing the Sturm chain tail.
  -- At a root r of p, the chain starts [p, p', ...]. p changes sign while p' has constant sign.
  -- The remaining entries contribute the same signChanges on both sides (by the chain property).
  -- Full proof requires formalizing the Euclidean algorithm of the Sturm chain.
  sorry

theorem sturm (p : ℝ[X]) (hp : Squarefree p) {a b : ℝ} (hab : a < b)
    (ha : p.eval a ≠ 0) (hb : p.eval b ≠ 0) :
    ((p.roots.toFinset).filter (fun x => a < x ∧ x < b)).card =
      sigma p a - sigma p b := by
  sorry

end Submission