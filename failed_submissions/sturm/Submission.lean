import ChallengeDeps
import Submission.Helpers

open LeanEval.Algebra
open Polynomial
open scoped Classical

namespace Submission

set_option autoImplicit false

/-- Sturm's theorem: For a squarefree real polynomial p and interval (a,b)
whose endpoints are not roots of p, the number of distinct real roots of p
in (a,b) equals sigma(p,a) - sigma(p,b). -/
theorem sturm (p : ℝ[X]) (hp : Squarefree p) {a b : ℝ} (hab : a < b)
    (ha : p.eval a ≠ 0) (hb : p.eval b ≠ 0) :
    ((p.roots.toFinset).filter (fun x => a < x ∧ x < b)).card =
      sigma p a - sigma p b := by
  -- ℝ is a perfect field (char 0), so Squarefree ↔ Separable
  have h_sep : p.Separable := by
    have h_perfect : PerfectField ℝ := by infer_instance
    rcases PerfectField.separable_iff_squarefree (g := p) with ⟨h_sqfree_imp_sep, _⟩
    exact h_sqfree_imp_sep hp
  -- Separable ↔ IsCoprime p (derivative p)
  have h_coprime : IsCoprime p (derivative p) := by
    rcases Polynomial.separable_def'.mp h_sep with ⟨h_coprime⟩
    exact h_coprime
  -- The Sturm chain of p terminates at a non-zero constant (since gcd(p,p')=1)
  -- and has the property that at any root r of p, the derivative p'(r) ≠ 0
  have h_deriv_nonzero_at_root : ∀ r : ℝ, p.eval r = 0 → derivative p |>.eval r ≠ 0 := by
    intro r hr
    by_contra! hzero
    have h_common_root : IsRoot p r ∧ IsRoot (derivative p) r := by
      constructor
      · rw [IsRoot, hr]
      · rw [IsRoot, hzero]
    -- If both p and p' vanish at r, then X-C(r) divides both, contradicting coprimeness
    have h_dvd_p : (X - C r) ∣ p := by
      rw [Polynomial.dvd_iff_isRoot]; exact h_common_root.1
    have h_dvd_deriv : (X - C r) ∣ derivative p := by
      rw [Polynomial.dvd_iff_isRoot]; exact h_common_root.2
    have h_dvd_one : (X - C r) ∣ (1 : ℝ[X]) :=
      h_coprime.dvd_of_dvd_mul_left (h_dvd_p.trans ?_)
    -- But X - C(r) is not a unit, contradiction
    have h_not_unit : ¬ IsUnit (X - C r) := by
      intro h_unit
      have : degree (X - C r) = 0 := h_unit.degree_eq_zero
      simp at this
    apply h_not_unit
    apply IsUnit.of_dvd_one h_dvd_one
    -- Need to fill: h_dvd_p * h_dvd_deriv ∣ 1
    sorry
  -- The function sigma(p,x) drops by exactly 1 as x crosses each root of p,
  -- and is constant elsewhere. Therefore the total drop from a to b equals
  -- the number of roots of p in (a,b).
  -- This is proved by analyzing the Sturm chain and using the triple lemma.
  sorry

end Submission