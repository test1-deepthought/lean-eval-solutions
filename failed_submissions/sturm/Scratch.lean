import Mathlib
import Mathlib.Tactic

open Polynomial
open scoped Classical

namespace LeanEval
namespace Algebra

noncomputable def sturmAux : ℝ[X] → ℝ[X] → ℕ → List ℝ[X]
| a, _, 0 => [a]
| a, b, (n + 1) =>
  if b = 0 then [a] else a :: sturmAux b (-(a % b)) n

noncomputable def sturmChain (p : ℝ[X]) : List ℝ[X] :=
  sturmAux p (derivative p) (p.natDegree + 2)

noncomputable def signChanges (xs : List ℝ) : ℕ :=
  let ys := xs.filter (· ≠ 0)
  ((ys.zip ys.tail).filter (fun q => q.1 * q.2 < 0)).length

noncomputable def sigma (p : ℝ[X]) (x : ℝ) : ℕ :=
  signChanges ((sturmChain p).map fun q => q.eval x)

end Algebra
end LeanEval

open LeanEval.Algebra

namespace Submission

theorem sturm_aux_poly_ne_zero (p : ℝ[X]) (hp : Squarefree p) : p ≠ 0 :=
  hp.ne_zero

theorem sturm_aux_signChanges_le (xs : List ℝ) :
    signChanges xs ≤ (xs.filter (· ≠ 0)).length := by
  rw [signChanges]
  refine le_trans (List.length_filter_le _ _) ?_
  rw [List.length_zip, List.length_tail]
  omega

theorem sturm_aux_root_count_le (p : ℝ[X]) (a b : ℝ) :
    ((p.roots.toFinset).filter (fun x => a < x ∧ x < b)).card ≤ p.roots.card := by
  calc ((p.roots.toFinset).filter (fun x => a < x ∧ x < b)).card
      ≤ (p.roots.toFinset).card := Finset.card_filter_le _ _
    _ ≤ p.roots.card := Multiset.toFinset_card_le _

theorem sturm_aux_sigma_le (p : ℝ[X]) (x : ℝ) :
    sigma p x ≤ (sturmChain p).length := by
  rw [sigma]
  refine le_trans (sturm_aux_signChanges_le _) ?_
  have := List.length_filter_le (fun x : ℝ => decide (x ≠ 0))
    ((sturmChain p).map (fun q => q.eval x))
  rw [List.length_map] at this
  exact this

theorem sturm_aux_chain_length_pos (p : ℝ[X]) :
    0 < (sturmChain p).length := by
  rw [sturmChain]
  have h : p.natDegree + 2 ≠ 0 := by omega
  cases hc : p.natDegree + 2 with
  | zero => exact absurd hc h
  | succ n =>
    have key : (sturmAux p (derivative p) (n + 1)).length ≠ 0 := by
      rw [sturmAux]; split <;> simp
    omega

end Submission