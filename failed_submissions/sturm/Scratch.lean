import Mathlib
open Polynomial
open scoped Classical
namespace Submission
noncomputable def sturmAux : ℝ[X] → ℝ[X] → ℕ → List ℝ[X]
  | a, _, 0       => [a]
  | a, b, (n + 1) => if b = 0 then [a] else a :: sturmAux b (-(a % b)) n
noncomputable def sturmChain (p : ℝ[X]) : List ℝ[X] := sturmAux p (derivative p) (p.natDegree + 2)
noncomputable def signChanges (xs : List ℝ) : ℕ :=
  let ys := xs.filter (· ≠ 0); ((ys.zip ys.tail).filter (fun q => q.1 * q.2 < 0)).length
noncomputable def sigma (p : ℝ[X]) (x : ℝ) : ℕ := signChanges ((sturmChain p).map fun q => q.eval x)
theorem signChanges_nil : signChanges ([] : List ℝ) = 0 := by unfold signChanges; rfl
theorem signChanges_singleton (y : ℝ) : signChanges [y] = 0 := by
  unfold signChanges; by_cases hy : y = 0
  · simp [hy]
  · have h1 : [y].filter (· ≠ 0) = [y] := by simp [hy]; rw [h1]; rfl
theorem sturmAux_zero (a b : ℝ[X]) : sturmAux a b 0 = [a] := rfl
theorem sturmAux_succ_ne (a b : ℝ[X]) (n : ℕ) (hb : b ≠ 0) :
    sturmAux a b (n + 1) = a :: sturmAux b (-(a % b)) n := by simp [sturmAux, hb]
theorem sturmAux_succ_eq (a b : ℝ[X]) (n : ℕ) (hb : b = 0) : sturmAux a b (n + 1) = [a] := by simp [sturmAux, hb]
theorem mod_eval_at_root (a b : ℝ[X]) (_hb : b ≠ 0) (β : ℝ) (hβ : b.eval β = 0) :
    (a % b).eval β = a.eval β := by
  have h := EuclideanDomain.mod_add_div a b
  have he : (a % b + b * (a / b)).eval β = a.eval β := by rw [h]
  rw [Polynomial.eval_add, Polynomial.eval_mul, hβ, zero_mul, add_zero] at he; exact he
theorem sturmChain_C (c : ℝ) : sturmChain (Polynomial.C c) = [Polynomial.C c] := by
  unfold sturmChain
  have hd : derivative (Polynomial.C c) = 0 := Polynomial.derivative_C
  rw [hd, Polynomial.natDegree_C]; exact sturmAux_succ_eq _ _ _ rfl
theorem sigma_C (c : ℝ) (x : ℝ) : sigma (Polynomial.C c) x = 0 := by
  unfold sigma; rw [sturmChain_C]; simp only [List.map_cons, List.map_nil]; exact signChanges_singleton _
end Submission