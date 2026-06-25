import ChallengeDeps
import Submission.Helpers

open LeanEval.Algebra
open Polynomial
open Set
open scoped Classical

namespace Submission

/-! # Sturm's Theorem — Partial Proof

We prove that for a squarefree real polynomial `p` and an interval `(a, b)` whose
endpoints are not roots of `p`, the number of distinct roots of `p` in `(a, b)`
equals `sigma p a - sigma p b` where `sigma` counts sign variations in the Sturm chain.

## Completed Lemmas

1. `signChanges_cons_cons_nonzero` — Computes sign changes for `a :: b :: rest` when all nonzero.
2. `squarefree_imp_separable` — Over ℝ, Squarefree ⇒ Separable.
3. `eval_derivative_ne_zero_of_squarefree_root` — At a root r of squarefree p, p'(r) ≠ 0.
4. `sign_constant_on_Ioo` — A polynomial with no root in (c,d) has constant sign there.

## Remaining Work

- **sigma_drop_at_simple_root**: At a simple root α of p (where p'(α) ≠ 0), σ drops by exactly 1
  as x passes α. This uses `signChanges_cons_cons_nonzero` and the sign change of p (flips sign)
  while p' maintains constant sign near α.
- **sigma_const_on_chain_root_free_interval**: On an interval where no Sturm chain member vanishes,
  σ is constant.
- **Combinatorial induction**: Partition (a,b) at all chain roots, sum the drops.
-/

open Submission.Helpers

/-- Near a simple root r of p (p'(r) ≠ 0), the Sturm chain sign pattern head changes
from `(a, b, ...)` with `a = p(x)` changing sign to `(a', b, ...)` with `a'` having opposite sign.
The first entry flips, the second (p') stays same-sign, and deeper entries are unaffected.
Hence exactly one sign variation is lost.

This is the core analytic lemma of Sturm's theorem. -/
lemma sigma_drop_at_simple_root (p : ℝ[X]) (hp : Squarefree p) (r : ℝ) (hr : p.eval r = 0) :
    ∃ δ > 0, ∀ u ∈ Ioo (r - δ) r, ∀ v ∈ Ioo r (r + δ), sigma p u - sigma p v = 1 := by
  have hderiv_ne_zero : (derivative p).eval r ≠ 0 :=
    eval_derivative_ne_zero_of_squarefree_root p hp r hr
  -- By continuity, p' is nonzero near r, hence maintains sign
  have h_cont_deriv : Continuous ((derivative p).eval : ℝ → ℝ) := Polynomial.continuous (derivative p)
  have h_deriv_nonzero_near : ∃ ε > 0, ∀ x ∈ Ioo (r - ε) (r + ε), (derivative p).eval x ≠ 0 := by
    have h_deriv_cont_at : ContinuousAt ((derivative p).eval : ℝ → ℝ) r := h_cont_deriv.continuousAt
    rcases h_deriv_cont_at.tendsto.eventually_ne (by exact hderiv_ne_zero) with ⟨h, hh⟩
    -- h : ∀ᶠ x in 𝓝 r, (derivative p).eval x ≠ 0
    -- We can extract an ε from the neighbourhood filter
    rcases Metric.mem_nhds_iff.mp h with ⟨ε, hε, hball⟩
    refine ⟨ε, hε, ?_⟩
    intro x hx
    apply hball
    rcases hx with ⟨hx1, hx2⟩
    have hx_dist : dist x r < ε := by
      rw [Real.dist_eq]
      have hx_range : x ∈ Ioo (r - ε) (r + ε) := hx
      rcases hx_range with ⟨hxl, hxr⟩
      have : |x - r| < ε := by
        have h1 : r - ε < x := hxl
        have h2 : x < r + ε := hxr
        nlinarith
      exact this
    exact hx_dist
  rcases h_deriv_nonzero_near with ⟨ε, hε, h_deriv_nonzero⟩
  have h_deriv_sign : (∀ x ∈ Ioo (r - ε) r, (derivative p).eval x > 0) ∨ (∀ x ∈ Ioo (r - ε) r, (derivative p).eval x < 0) := by
    apply sign_constant_on_Ioo (derivative p) (r - ε) r (by nlinarith)
    intro x hx
    exact h_deriv_nonzero x (by
      rcases hx with ⟨hxl, hxr⟩
      refine ⟨by nlinarith, by nlinarith⟩)
  -- p(x) = (x - r) * q(x) for some q with q(r) = p'(r) ≠ 0
  have h_factor : ∃ q : ℝ[X], p = (X - C r) * q ∧ q.eval r = (derivative p).eval r := by
    have h_div : (X - C r) ∣ p := by
      rw [← Polynomial.eq_X_sub_C_of_eval_eq_zero hr]
      exact dvd_refl _
    sorry
  sorry

/-- The main theorem: Sturm's theorem. Partial proof.

Strategy: Let R = {roots of p in (a,b)}. We prove by induction on |R| that
`|R| = sigma p a - sigma p b`.

Base case: |R| = 0 (no roots). Then p has no root in (a,b). By `sign_constant_on_Ioo`,
p has constant sign on (a,b). The Sturm chain members also have no root in (a,b) by
squarefreeness and the gcd property. Hence sigma is constant on (a,b), so sigma p a = sigma p b = 0.

Inductive step: Pick a root α ∈ (a,b) of p. By `sigma_drop_at_simple_root`, there exists δ > 0
such that sigma drops by 1 across α. Split the interval at α: count roots in (a,α) + 1 + roots in (α,b).
Apply the induction hypothesis to (a,α) and (α,b) and add the drop of 1 at α.
-/
theorem sturm (p : ℝ[X]) (hp : Squarefree p) {a b : ℝ} (hab : a < b)
    (ha : p.eval a ≠ 0) (hb : p.eval b ≠ 0) :
    ((p.roots.toFinset).filter (fun x => a < x ∧ x < b)).card =
      sigma p a - sigma p b := by
  -- Let R = {roots of p in (a,b)}
  let R := (p.roots.toFinset).filter (fun x => a < x ∧ x < b)
  have hR_finite : R.Finite := by
    apply Finset.finite_toSet
  -- We will prove by induction on |R| = n
  have hcard_pos : 0 ≤ R.card := by omega
  -- Case analysis on whether R is empty
  by_cases h_empty : R.card = 0
  · -- No roots in (a,b). We need to show sigma p a = sigma p b.
    -- Since p has no root in (a,b), it has constant sign there.
    have h_no_root : ∀ x ∈ Ioo a b, p.eval x ≠ 0 := by
      intro x hx
      have hx_mem : x ∈ p.roots := by
        apply Polynomial.mem_roots (by
          intro hzero
          apply ha
          -- If p = 0 then p.eval a = 0, contradiction
          have hp0 : p = 0 := hzero
          sorry)
        sorry
      sorry
    -- sigma is constant on (a,b) because no chain root exists
    sorry
  · -- R is nonempty. Pick a root α ∈ (a,b).
    have hR_nonempty : R.Nonempty := by
      apply Finset.one_le_card.mp
      omega
    rcases hR_nonempty with ⟨α, hα⟩
    have hα_mem : α ∈ p.roots := by
      have : α ∈ (p.roots.toFinset).filter (fun x => a < x ∧ x < b) := hα
      simpa [R] using this
    have hα_root : p.eval α = 0 := by
      rw [Polynomial.mem_roots (by
        -- p ≠ 0 because p.eval a ≠ 0
        intro hp0
        apply ha
        simp [hp0])] at hα_mem
      exact hα_mem
    have hα_range : a < α ∧ α < b := by
      have : α ∈ (p.roots.toFinset).filter (fun x => a < x ∧ x < b) := hα
      simpa [R] using this
    rcases hα_range with ⟨haα, hαb⟩
    -- By sigma_drop_at_simple_root, there exists δ > 0 such that sigma drops by 1 across α
    have h_drop : ∃ δ > 0, ∀ u ∈ Ioo (α - δ) α, ∀ v ∈ Ioo α (α + δ), sigma p u - sigma p v = 1 :=
      sigma_drop_at_simple_root p hp α hα_root
    rcases h_drop with ⟨δ, hδ, h_drop⟩
    -- Pick u ∈ (α-δ, α) and v ∈ (α, α+δ) with no other roots in (u,v)
    -- Then sigma p u - sigma p v = 1
    let u := max a (α - δ/2)
    let v := min b (α + δ/2)
    have hu_range : a < u ∧ u < α := by
      dsimp [u]
      have hmax_lt : max a (α - δ/2) < α := by
        have h_half : α - δ/2 < α := by nlinarith
        exact lt_of_le_of_lt (by exact le_max_right _ _) h_half
      sorry
    sorry
  sorry

end Submission
