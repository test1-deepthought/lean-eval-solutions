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
  have hnonzero : (f * g).eval r ≠ 0 := by
    rw [eval_mul]; exact ne_of_gt hpos
  rcases nonzero_near (f * g) r hnonzero with ⟨ε, hε, hprod⟩
  let δ := ε / 2
  have hδpos : δ > 0 := by nlinarith
  refine ⟨δ, hδpos, ?_⟩
  intro x hx
  have hx' : |x - r| < ε := by
    have : |x - r| < δ := hx; nlinarith
  have hnonzero' : (f * g).eval x ≠ 0 := hprod x hx'
  have hpos' : (f * g).eval x > 0 := by
    rw [eval_mul] at hnonzero'
    have h_cont : Continuous (f.eval * g.eval : ℝ → ℝ) := by
      continuity
    -- Since (f*g).eval r > 0 and (f*g).eval x ≠ 0 for |x-r| < ε, (f*g).eval x > 0
    -- by continuity and the Intermediate Value Property
    have hroot_free : ∀ y ∈ Ioo (r - δ) (r + δ), (f * g).eval y ≠ 0 := by
      intro y hy
      apply hprod y
      have : |y - r| < δ := by
        rcases hy with ⟨hyl, hyr⟩
        have : y - r > -δ := by linarith
        have : y - r < δ := by linarith
        rw [abs_lt]; constructor <;> linarith
      exact this
    rcases sign_constant_on_Ioo (f * g) (r - δ) (r + δ) (by nlinarith) hroot_free with (h | h)
    · apply h x; nlinarith
    · have : (f * g).eval r > 0 := hpos
      have : (f * g).eval r < 0 := h r (by nlinarith)
      linarith
  exact hpos'

-- At a simple root r, p(u)*p'(u) < 0 for u left of r and > 0 for v right of r
lemma sign_change_at_root (p : ℝ[X]) (r : ℝ) (hpderiv : (derivative p).eval r ≠ 0) 
    (hp0 : p.eval r = 0) : ∃ δ > 0, (∀ u, r - δ < u ∧ u < r → p.eval u * (derivative p).eval u < 0) ∧
    (∀ v, r < v ∧ v < r + δ → p.eval v * (derivative p).eval v > 0) := by
  rcases factor_theorem_with_deriv p r hp0 with ⟨q, hpq, hq⟩
  have hqr : q.eval r * (derivative p).eval r > 0 := by
    rw [hq]; nlinarith [sq_pos_of_ne_zero hpderiv]
  rcases pos_product_near q (derivative p) r hqr with ⟨δ₁, hδ₁pos, hpos⟩
  have h_ur_neg : ∀ u, r - δ₁ < u ∧ u < r → (u - r) < 0 := by
    intro u ⟨hu1, hu2⟩; linarith
  have h_vr_pos : ∀ v, r < v ∧ v < r + δ₁ → (v - r) > 0 := by
    intro v ⟨hv1, hv2⟩; linarith
  refine ⟨δ₁, hδ₁pos, ?_, ?_⟩
  · intro u ⟨hu1, hu2⟩
    have hpu : p.eval u = (u - r) * q.eval u := by
      rw [hpq, eval_mul, eval_sub, eval_X, eval_C]; ring
    have hsign : q.eval u * (derivative p).eval u > 0 := hpos u (by
      have : |u - r| < δ₁ := by
        have : u - r < 0 := h_ur_neg u ⟨hu1, hu2⟩
        have : |u - r| = r - u := abs_of_neg (sub_neg.mpr hu2)
        rw [this]; nlinarith
      exact this)
    have h_neg : (u - r) < 0 := h_ur_neg u ⟨hu1, hu2⟩
    nlinarith
  · intro v ⟨hv1, hv2⟩
    have hpv : p.eval v = (v - r) * q.eval v := by
      rw [hpq, eval_mul, eval_sub, eval_X, eval_C]; ring
    have hsign : q.eval v * (derivative p).eval v > 0 := hpos v (by
      have : |v - r| < δ₁ := by
        have : v - r > 0 := h_vr_pos v ⟨hv1, hv2⟩
        have : |v - r| = v - r := abs_of_pos (sub_pos.mpr hv1)
        rw [this]; nlinarith
      exact this)
    have h_pos : (v - r) > 0 := h_vr_pos v ⟨hv1, hv2⟩
    nlinarith

-- Main theorem: Sturm's theorem
theorem sturm (p : ℝ[X]) (hp : Squarefree p) {a b : ℝ} (hab : a < b)
    (ha : p.eval a ≠ 0) (hb : p.eval b ≠ 0) :
    ((p.roots.toFinset).filter (fun x => a < x ∧ x < b)).card =
      sigma p a - sigma p b := by
  -- Key observation: For a squarefree polynomial p:
  -- (1) Between consecutive roots of p, sigma is constant (since p' ≠ 0 at roots of p,
  --     and other chain entries either maintain sign or contribute the same via triple_sign_lemma)
  -- (2) At each simple root r of p, sigma drops by exactly 1 (by sign_change_at_root
  --     and the signChanges_cons_cons_nonzero lemma)
  -- (3) Therefore, sigma p a - sigma p b = number of distinct roots of p in (a,b)
  --
  -- Formal proof by strong induction on the number of distinct roots in (a,b):
  let R := ((p.roots.toFinset).filter (fun x => a < x ∧ x < b))
  -- Use the fact that R is finite and we can extract its minimal element
  by_cases hR : R.Nonempty
  · -- Pick the smallest root r in (a,b)
    let r := R.min' hR
    have hrR : r ∈ R := Finset.min'_mem _ _ hR
    have hr_range : a < r ∧ r < b := by
      rcases Finset.mem_filter.mp hrR with ⟨hrRoot, hrRange⟩
      exact hrRange
    rcases hr_range with ⟨har, hrb⟩
    have hproot : p.eval r = 0 := by
      rcases Finset.mem_filter.mp hrR with ⟨hrRoot, hrRange⟩
      rw [Finset.mem_toFinset] at hrRoot
      exact hrRoot
    have hpderiv : (derivative p).eval r ≠ 0 :=
      eval_derivative_ne_zero_of_squarefree_root p hp r hproot
    rcases sign_change_at_root p r hpderiv hproot with ⟨δ, hδpos, hleft, hright⟩
    have hδ_small : r - δ > a ∧ r + δ < b := by
      have : δ < r - a := sorry
      sorry
    sorry
  · -- R empty: p has no roots in (a,b)
    -- Need to show sigma p a = sigma p b
    -- Since p has no roots in (a,b) and is squarefree, p' ≠ 0 everywhere in (a,b)
    -- and all Sturm chain members maintain constant sign relationships
    -- so sigma is constant on (a,b)
    have h_no_root : ∀ x ∈ Ioo a b, p.eval x ≠ 0 := by
      intro x hx
      rcases hx with ⟨hax, hxb⟩
      intro hzero
      apply hR
      refine ⟨x, Finset.mem_filter.mpr ⟨?_, hax, hxb⟩⟩
      rw [Finset.mem_toFinset, Polynomial.mem_roots (by
        -- p ≠ 0 since it has no roots and is squarefree
        intro hzero_p
        apply ha; rw [hzero_p, eval_zero])]
      exact hzero
    sorry

end Submission