import ChallengeDeps
import Submission.Helpers

open LeanEval.Algebra
open Polynomial
open scoped Classical

namespace Submission

set_option maxRecDepth 200000

/--
Sturm's theorem: For a squarefree real polynomial `p` and an interval `(a, b)` whose
endpoints are not roots of `p`, the number of distinct real roots of `p` in `(a, b)`
equals `σ_p(a) - σ_p(b)`, where `σ_p(x)` is the number of sign changes in the Sturm
chain of `p` evaluated at `x`.
-/
theorem sturm (p : ℝ[X]) (hp : Squarefree p) {a b : ℝ} (hab : a < b)
    (ha : p.eval a ≠ 0) (hb : p.eval b ≠ 0) :
    ((p.roots.toFinset).filter (fun x => a < x ∧ x < b)).card = sigma p a - sigma p b := by
  -- Count distinct real roots in (a,b)
  let roots_in_ab := ((p.roots.toFinset).filter (fun x => a < x ∧ x < b))

  -- If there are no roots, use the helper lemma
  by_cases hzero : roots_in_ab.card = 0
  · have h_no_roots : ∀ x ∈ Set.Ioo a b, p.eval x ≠ 0 := by
      intro x hx
      rcases hx with ⟨hx1, hx2⟩
      intro hzero_eval
      have hx_root : x ∈ roots_in_ab := by
        refine Finset.mem_filter.mpr ⟨?_, hx1, hx2⟩
        rw [Polynomial.mem_roots (Squarefree.ne_zero hp)]
        exact hzero_eval
      have : roots_in_ab.card ≥ 1 := Finset.one_le_card.mpr ⟨x, hx_root⟩
      linarith
    exact Submission.Helpers.sigma_eq_when_no_roots p hp hab ha hb h_no_roots

  -- There is at least one root. Let r be the smallest root in (a,b).
  have h_nonempty : roots_in_ab.Nonempty := by
    by_contra! h_empty
    have : roots_in_ab.card = 0 := Finset.card_empty.mpr (Finset.not_nonempty_iff_eq_empty.mp h_empty)
    exact hzero this
  let r := roots_in_ab.min' h_nonempty
  have hr_mem : r ∈ roots_in_ab := Finset.min'_mem _ _ h_nonempty
  have hr_root_props : p.eval r = 0 ∧ a < r ∧ r < b := by
    have hmem := hr_mem
    simp [roots_in_ab, Polynomial.mem_roots (Squarefree.ne_zero hp)] at hmem
    exact ⟨hmem.1.2, hmem.2.1, hmem.2.2⟩
  rcases hr_root_props with ⟨hr_root, hr_a, hr_b⟩

  -- Choose a point c between a and r where p is non-zero
  let c := (a + r) / 2
  have h_ac : a < c := by nlinarith
  have h_cr : c < r := by nlinarith
  have hc_nonzero : p.eval c ≠ 0 := by
    intro hzero_eval
    have hc_root : c ∈ roots_in_ab := by
      refine Finset.mem_filter.mpr ⟨?_, h_ac, hr_a⟩
      rw [Polynomial.mem_roots (Squarefree.ne_zero hp)]
      exact hzero_eval
    have : r ≤ c := Finset.min'_le _ _ hc_root
    nlinarith

  -- σ(a) - σ(r) = 1 at the root r (the core of Sturm's theorem)
  have h_drop_at_root : sigma p a - sigma p r = 1 := by
    have h_sigma_drop := Submission.Helpers.sigma_drops_at_root p hp r hr_root
    -- This gives us: for any x < r < y sufficiently close to r, sigma x - sigma y = 1
    have h_small_enough : sigma p c - sigma p r = 1 := by
      apply Submission.Helpers.sigma_drops_at_root_interval p hp r hr_root c (r + (b - r) / 2)
      · exact h_cr
      · nlinarith
      · exact hc_nonzero
      · exact hb
    have h_sigma_ac : sigma p a = sigma p c :=
      Submission.Helpers.sigma_eq_when_no_roots p hp h_ac h_cr hc_nonzero (by
        intro x hx
        rcases hx with ⟨hx1, hx2⟩
        intro hzero_eval
        have hx_root : x ∈ roots_in_ab := by
          refine Finset.mem_filter.mpr ⟨?_, hx1, hr_a⟩
          rw [Polynomial.mem_roots (Squarefree.ne_zero hp)]
          exact hzero_eval
        have : r ≤ x := Finset.min'_le _ _ hx_root
        nlinarith)
    calc
      sigma p a - sigma p r = (sigma p c - sigma p r) := by
        rw [h_sigma_ac]
        ring
      _ = 1 := h_small_enough

  -- By induction, the formula holds for (r, b)
  have h_induction : sigma p r - sigma p b = ((p.roots.toFinset).filter (fun x => r < x ∧ x < b)).card := by
    -- Count roots in (r,b)
    let roots_in_rb := ((p.roots.toFinset).filter (fun x => r < x ∧ x < b))
    have h_card_rb : roots_in_rb.card = roots_in_ab.card - 1 := by
      -- Since r is the smallest root in (a,b), roots_in_ab = {r} ∪ roots_in_rb
      have h_split : roots_in_ab = {r} ∪ roots_in_rb := by
        ext x; constructor
        · intro hx
          have hx_mem : x ∈ roots_in_ab := hx
          simp [roots_in_ab] at hx_mem
          by_cases hxr : x = r
          · subst x; simp
          · have : r < x := by
              have : r ≤ x := Finset.min'_le _ _ (by
                have : x ∈ roots_in_ab := hx
                exact this)
              exact Ne.lt_of_le hxr this
            simp [this, hx_mem.1, hx_mem.2.2]
        · intro hx
          simp at hx
          rcases hx with (rfl|hx)
          · exact hr_mem
          · refine Finset.mem_filter.mpr ⟨hx.1, ?_, hx.2.2⟩
            have : a < r := hr_a
            exact this.trans hx.2.1
      rw [h_split]
      simp
    -- Now use the outer induction hypothesis (which we apply recursively)
    sorry

  -- Combine the pieces
  calc
    sigma p a - sigma p b = (sigma p a - sigma p r) + (sigma p r - sigma p b) := by ring
    _ = 1 + ((p.roots.toFinset).filter (fun x => r < x ∧ x < b)).card := by rw [h_drop_at_root, h_induction]
    _ = ((p.roots.toFinset).filter (fun x => a < x ∧ x < b)).card := by
      -- Need to show: 1 + count(r,b) = count(a,b)
      sorry

end Submission