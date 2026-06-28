import ChallengeDeps
import Submission.Helpers

open LeanEval.Algebra
open Polynomial
open scoped Classical

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
    by_cases h : (-a) * b < 0
    · exfalso; nlinarith
    · simp [h]
  rw [h1, h2]
  simp [add_comm]

-- The set of all points in (a,b) where some chain entry vanishes
def chainRootsSet (p : ℝ[X]) (a b : ℝ) : Finset ℝ :=
  ((Finset.biUnion ((sturmChain p).toFinset) (fun q => q.roots.toFinset)).filter (fun x => a < x ∧ x < b))

lemma mem_chainRootsSet_iff (p : ℝ[X]) (a b x : ℝ) :
    x ∈ chainRootsSet p a b ↔ (∃ q ∈ sturmChain p, q.eval x = 0) ∧ a < x ∧ x < b := by
  constructor
  · intro hx
    rcases Finset.mem_filter.mp hx with ⟨hx_mem, hx_bounds⟩
    rcases Finset.mem_biUnion.mp hx_mem with ⟨q, hq_chain, hq_root⟩
    refine ⟨⟨q, hq_chain, ?_⟩, hx_bounds.1, hx_bounds.2⟩
    rw [Polynomial.mem_roots (by
      have hq_ne_zero : q ≠ 0 := by
        intro hzero
        have : 0 ∈ (sturmChain p).toFinset := by
          simpa [hzero] using hq_chain
        -- This is a proof that 0 is in the chain, but we may not need it
        sorry
      exact hq_ne_zero)] at hq_root
    exact hq_root
  · intro ⟨⟨q, hq_chain, hq_root⟩, hx_a, hx_b⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_biUnion.mpr ⟨q, by
      simpa using hq_chain, ?_⟩, hx_a, hx_b⟩
    rw [Polynomial.mem_roots (by
      have hq_ne_zero : q ≠ 0 := by
        intro hzero
        have : q = 0 := hzero
        -- We need to show q ≠ 0 because if q = 0, it can't have roots
        -- But q = 0 could be in the chain. However, 0 has no roots, so we can exclude q = 0.
        exact hzero
      exact hq_ne_zero), hq_root]
    exact hq_root

theorem sturm (p : ℝ[X]) (hp : Squarefree p) {a b : ℝ} (hab : a < b)
    (ha : p.eval a ≠ 0) (hb : p.eval b ≠ 0) :
    ((p.roots.toFinset).filter (fun x => a < x ∧ x < b)).card =
      sigma p a - sigma p b := by
  -- We use induction on the size of chainRootsSet
  -- Actually, we'll use a stronger inductive statement
  sorry

end Submission