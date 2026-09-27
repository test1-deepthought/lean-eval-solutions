import Mathlib
open Polynomial
open scoped Classical

namespace Submission

noncomputable def sturmAux : ℝ[X] → ℝ[X] → ℕ → List ℝ[X]
  | a, _, 0       => [a]
  | a, b, (n + 1) =>
    if b = 0 then [a] else a :: sturmAux b (-(a % b)) n

noncomputable def sturmChain (p : ℝ[X]) : List ℝ[X] :=
  sturmAux p (derivative p) (p.natDegree + 2)

noncomputable def signChanges (xs : List ℝ) : ℕ :=
  let ys := xs.filter (· ≠ 0)
  ((ys.zip ys.tail).filter (fun q => q.1 * q.2 < 0)).length

noncomputable def sigma (p : ℝ[X]) (x : ℝ) : ℕ :=
  signChanges ((sturmChain p).map fun q => q.eval x)

-- Verified structural facts:
theorem sturmAux_zero (a b : ℝ[X]) : sturmAux a b 0 = [a] := rfl

theorem sturmAux_succ (a b : ℝ[X]) (n : ℕ) (hb : b ≠ 0) :
    sturmAux a b (n + 1) = a :: sturmAux b (-(a % b)) n := by
  simp [sturmAux, hb]

theorem sturmAux_stop (a : ℝ[X]) (n : ℕ) : sturmAux a 0 (n + 1) = [a] := by
  simp [sturmAux]

theorem signChanges_nil : signChanges ([] : List ℝ) = 0 := by
  simp [signChanges]

-- Linchpin sign-alternation identity, now FULLY PROVEN (no sorry):
theorem mod_eval_at_root (a b : ℝ[X]) (β : ℝ) (hβ : b.eval β = 0) :
    (a % b).eval β = a.eval β := by
  have h := EuclideanDomain.mod_add_div a b
  have h2 : (a % b).eval β + (b * (a / b)).eval β = a.eval β := by
    rw [← Polynomial.eval_add, h]
  rw [Polynomial.eval_mul, hβ, zero_mul, add_zero] at h2
  exact h2

-- Frozen final theorem: proof body still absent.
theorem sturm (p : ℝ[X]) (hp : Squarefree p) {a b : ℝ} (hab : a < b)
    (ha : p.eval a ≠ 0) (hb : p.eval b ≠ 0) :
    ((p.roots.toFinset).filter (fun x => a < x ∧ x < b)).card =
      sigma p a - sigma p b := by
  sorry

end Submission