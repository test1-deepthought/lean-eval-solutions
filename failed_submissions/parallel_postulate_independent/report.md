# Incomplete Lean-Eval attempt: parallel_postulate_independent

## Failed Lean Error

Submission.lean still contains `sorry` for both halves of the conjunction. The Euclidean half is partially formalized (axioms A1,A2,A3,A4,A6,A8,A9 verified over E2 = EuclideanSpace ℝ (Fin 2) with B = affine betweenness via dist and C = metric congruence); A5, A7, A10, A11 are unproved. The hyperbolic half (∃ M T, ¬ Euclidean M T) is entirely unproved: it requires constructing the Beltrami–Klein model of the hyperbolic plane (no such model exists in Mathlib) and proving A1–A9+A11 hold while A10 fails.

## Agent Response Context

The Lean-Eval problem `parallel_postulate_independent` asks for a single theorem: there exists a TarskiAbsolute model satisfying the Euclidean axiom and there exists a TarskiAbsolute model refuting it. Mathlib contains no Tarski geometry and no model of hyperbolic geometry, so the entire structure must be built from scratch and proved axiom-free (the evaluator runs the independent nanoda kernel and comparator, forbidding `sorry`/`axiom`/`native_decide`).

I built and machine-verified the Euclidean witness mechanics (M = EuclideanSpace ℝ (Fin 2) with affine betweenness and metric congruence): axioms A1, A2, A3, A6, A8 and the hard A9 (upper dimension) are fully proved placeholder-free. A9 required deriving that equidistance from two distinct points forces the perpendicular-bisector condition ⟪p−q, 2x−(p+q)⟫ = 0, placing all three points in a one-dimensional orthogonal complement and concluding collinearity via finrank. A4, A5, A7, A10, A11 remain unproved.

The second conjunct (a model of absolute geometry failing the Euclidean axiom) requires the Beltrami–Klein hyperbolic disk model, which does not exist in Mathlib and is research-scale to formalize; it is the load-bearing gap.

Per H13, formal verification could not be completed. The exact remaining goals are the two conjuncts of `parallel_postulate_independent`: (i) the residue of the Euclidean half — A4, A5, A7, A10, A11 over E2; (ii) the hyperbolic half — the Klein model with proofs of A1–A9, A11 and ¬Euclidean. Both are recorded; the partial verified fragment is attached.

## Lean 4 Code From This Attempt

```lean4
import Mathlib

set_option autoImplicit false
noncomputable section
namespace TarskiIndep

abbrev E2 := EuclideanSpace ℝ (Fin 2)
def EucB (a b c : E2) : Prop := dist a c = dist a b + dist b c
def EucC (a b c d : E2) : Prop := dist a b = dist c d

theorem bridge (a b c : E2) : EucB a b c ↔ Wbtw ℝ a b c := by
  rw [EucB, eq_comm, dist_add_dist_eq_iff]

theorem A1 (a b : E2) : EucC a b b a := by simp [EucC, dist_comm]

theorem A2 (a b c d e f : E2) (h1 : EucC a b c d) (h2 : EucC a b e f) : EucC c d e f := by
  simp only [EucC] at *; rw [← h1, h2]

theorem A3 (a b c : E2) (h : EucC a b c c) : a = b := by
  simp only [EucC, dist_self] at h; exact eq_of_dist_eq_zero h

theorem A6 (a b : E2) (h : EucB a b a) : a = b := by
  rw [EucB, dist_self] at h
  have h1 := dist_nonneg (x:=a) (y:=b); have h2 := dist_nonneg (x:=b) (y:=a)
  exact eq_of_dist_eq_zero (by linarith)

def p (a b : ℝ) : E2 := WithLp.equiv 2 (Fin 2 → ℝ) |>.symm ![a,b]

theorem d2 : dist (p 1 0) (p 0 1) = Real.sqrt 2 := by
  rw [dist_eq_norm, EuclideanSpace.norm_eq]; simp [p, Fin.sum_univ_two]; ring_nf
theorem d1 : dist (p 1 0) (p 0 0) = 1 := by
  rw [dist_eq_norm, EuclideanSpace.norm_eq]; simp [p, Fin.sum_univ_two]
theorem d0 : dist (p 0 0) (p 0 1) = 1 := by
  rw [dist_eq_norm, EuclideanSpace.norm_eq]; simp [p, Fin.sum_univ_two]

theorem A8_aux (h : EucB (p 1 0) (p 0 0) (p 0 1)) : False := by
  rw [EucB, d2, d1, d0] at h
  have : Real.sqrt 2 < 2 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  linarith

theorem inner_perp (p q x : E2) (h : dist p x = dist q x) :
    ⟪p - q, (2:ℝ) • x - (p + q)⟫_ℝ = 0 := by
  have expand : ∀ a b : E2, ⟪a - b, a - b⟫_ℝ = ⟪a,a⟫_ℝ - 2*⟪a,b⟫_ℝ + ⟪b,b⟫_ℝ := by
    intro a b; rw [inner_sub_left, inner_sub_right, inner_sub_right, real_inner_comm b a]; ring
  have h2 : ⟪p - x, p - x⟫_ℝ = ⟪q - x, q - x⟫_ℝ := by
    have h' : ‖p - x‖ = ‖q - x‖ := by rw [dist_eq_norm, dist_eq_norm] at h; exact h
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, h']
  rw [expand p x, expand q x] at h2
  simp only [inner_sub_left, inner_sub_right, inner_add_right, real_inner_smul_right, real_inner_comm q p]
  linarith [h2]

theorem perp_vsub (p q x y : E2) (hx : dist p x = dist q x) (hy : dist p y = dist q y) :
    ⟪p - q, x - y⟫_ℝ = 0 := by
  have h1 := inner_perp p q x hx
  have h2 := inner_perp p q y hy
  simp only [inner_sub_right, real_inner_smul_right] at h1 h2
  simp only [inner_sub_right]; linarith [h1, h2]

theorem A9 (p q : E2) (hpq : p ≠ q) (a b c : E2)
    (ha : dist p a = dist q a) (hb : dist p b = dist q b) (hc : dist p c = dist q c) :
    Collinear ℝ ({a, b, c} : Set E2) := by
  rw [collinear_iff_finrank_le_one]
  haveI : Fact (finrank ℝ E2 = 1 + 1) := ⟨by simp⟩
  set W : Submodule ℝ E2 := (ℝ ∙ (p - q))ᗮ with hW
  have hdim : finrank ℝ W = 1 := by
    rw [hW]; exact Submodule.finrank_orthogonal_span_singleton (sub_ne_zero.mpr hpq)
  have inner_ab : ⟪p - q, b - a⟫_ℝ = 0 := perp_vsub p q b a hb ha
  have inner_ac : ⟪p - q, c - a⟫_ℝ = 0 := perp_vsub p q c a hc ha
  have mem_ab : (a -ᵥ b : E2) ∈ W := by
    rw [hW, Submodule.mem_orthogonal_singleton_iff_inner_right]
    show ⟪p - q, a - b⟫_ℝ = 0
    rw [show a - b = -(b - a) by abel, inner_neg_right, inner_ab, neg_zero]
  have mem_ac : (a -ᵥ c : E2) ∈ W := by
    rw [hW, Submodule.mem_orthogonal_singleton_iff_inner_right]
    show ⟪p - q, a - c⟫_ℝ = 0
    rw [show a - c = -(c - a) by abel, inner_neg_right, inner_ac, neg_zero]
  have key : vectorSpan ℝ ({a, b, c} : Set E2) ≤ W := by
    rw [vectorSpan_eq_span_vsub_set_left ℝ (show a ∈ ({a,b,c}:Set E2) by simp)]
    rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx | hx
    · subst hx; simp
    · subst hx; exact mem_ab
    · subst hx; exact mem_ac
  calc finrank ℝ ↥(vectorSpan ℝ ({a,b,c}:Set E2)) ≤ finrank ℝ ↥W := Submodule.finrank_mono key
    _ = 1 := hdim

end TarskiIndep
```

## Evidence scope

Saved source and prose are attempt artifacts, not verification evidence. Only matching successful Lean evidence establishes verification. Missing source is not reconstructed from the report.

No candidate_submission was supplied; no Submission.lean artifact was saved.