import Mathlib
open Polynomial
open List
open Set

namespace Submission.Helpers

/-! # Helper lemmas for Sturm's theorem -/


/-! ## signChanges lemmas -/

lemma signChanges_nil : LeanEval.Algebra.signChanges ([] : List ℝ) = 0 := by
  unfold LeanEval.Algebra.signChanges; simp

lemma signChanges_singleton (a : ℝ) : LeanEval.Algebra.signChanges [a] = 0 := by
  unfold LeanEval.Algebra.signChanges
  by_cases ha : a = 0
  · subst ha; simp
  · simp [ha]

lemma signChanges_cons_zero (a : ℝ) (xs : List ℝ) (ha : a = 0) : LeanEval.Algebra.signChanges (a :: xs) = LeanEval.Algebra.signChanges xs := by
  subst ha; unfold LeanEval.Algebra.signChanges; simp

lemma signChanges_cons_cons_nonzero (a b : ℝ) (xs : List ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    LeanEval.Algebra.signChanges (a :: b :: xs) = (if a * b < 0 then 1 else 0) + LeanEval.Algebra.signChanges (b :: xs) := by
  unfold LeanEval.Algebra.signChanges
  simp [ha, hb]
  by_cases h : a * b < 0
  · simpa [h, add_comm]
  · simpa [h]

lemma signChanges_filter_eq (xs : List ℝ) : LeanEval.Algebra.signChanges xs = LeanEval.Algebra.signChanges (xs.filter (· ≠ 0)) := by
  unfold LeanEval.Algebra.signChanges; simp

lemma signChanges_splice_zero (xs ys : List ℝ) : LeanEval.Algebra.signChanges (xs ++ [0] ++ ys) = LeanEval.Algebra.signChanges (xs ++ ys) := by
  unfold LeanEval.Algebra.signChanges; simp

lemma signChanges_pair (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) : LeanEval.Algebra.signChanges [a, b] = if a * b < 0 then 1 else 0 := by
  calc
    LeanEval.Algebra.signChanges [a, b] = (if a * b < 0 then 1 else 0) + LeanEval.Algebra.signChanges [b] := by
      simpa using signChanges_cons_cons_nonzero a b [] ha hb
    _ = (if a * b < 0 then 1 else 0) + 0 := by simp [signChanges_singleton]
    _ = if a * b < 0 then 1 else 0 := by simp


/-! ## Polynomial lemmas -/

lemma squarefree_imp_separable (p : ℝ[X]) (hp : Squarefree p) : Separable p :=
  (PerfectField.separable_iff_squarefree (K := ℝ) (g := p)).mpr hp

lemma eval_derivative_ne_zero_of_squarefree_root (p : ℝ[X]) (hp : Squarefree p) (r : ℝ) (hr : p.eval r = 0) : 
    p.derivative.eval r ≠ 0 := by
  have hsep : Separable p := squarefree_imp_separable p hp
  have hx : (aeval r) p = 0 := by simpa using hr
  have h := hsep.aeval_derivative_ne_zero (x := r) hx
  simpa using h


/-! ## Sturm chain property lemma

Key property: For any consecutive triple (q_{k-1}, q_k, q_{k+1}) in the Sturm chain
at a root r of q_k (k ≥ 1), we have q_{k-1}(r)·q_{k+1}(r) < 0.

Proof: The Sturm chain satisfies q_{k+1} = -(q_{k-1} mod q_k).
At the root r where q_k(r)=0, Euclidean division gives
q_{k-1}(r) = q_k(r)·(q_{k-1}/q_k)(r) + (q_{k-1} mod q_k)(r) = 0 + (q_{k-1} mod q_k)(r).
So q_{k+1}(r) = -(q_{k-1} mod q_k)(r) = -q_{k-1}(r).
Since each entry is nonzero at r (otherwise the chain would have terminated),
q_{k-1}(r)·q_{k+1}(r) = q_{k-1}(r)·(-q_{k-1}(r)) = -(q_{k-1}(r))² < 0.
-/

end Submission.Helpers