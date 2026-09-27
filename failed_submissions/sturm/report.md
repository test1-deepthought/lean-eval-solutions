# Incomplete Lean-Eval attempt: sturm

## Failed Lean Error

The frozen theorem `sturm` remains unproved. Its proof body requires the full Sturm-sequence theory over the challenge's custom noncomputable definitions: (1) chain sign alternation at common zeros, (2) local constancy of the evaluation-based `sigma` off roots, (3) unit drop at simple roots at a root of p, then telescoping. `Polynomial.sturmSeq` and `List.signVariations` are local_missing in this compile environment (confirmed via mathlib_check and direct #check in the Lean sandbox). The custom `signChanges` filter/zip/decide layer has no simplification API. Verified this turn: signChanges_nil, signChanges_singleton, sturmAux_zero/succ_ne/succ_eq, mod_eval_at_root, neg_mod_eval_at_root, sturmChain_C, sigma_C, sturm_const (constant base case).

## Agent Response Context

Continuing the Lean-Eval sturm problem, genuine machine-checked progress was made this turn with inlined challenge definitions (Lean exit 0, no sorry): the custom signChanges foundation (signChanges_nil, signChanges_singleton), the sturmAux unfolding lemmas, the linchpin Euclidean identity mod_eval_at_root ((a % b).eval beta = a.eval beta when b.eval beta = 0) with its sign-alternation corollary neg_mod_eval_at_root, and the complete constant base case (sturmChain_C, sigma_C). The frozen theorem sturm remains UNPROVED. Exact remaining goal: the sturm proof body (Challenge.lean line 11), whose pillars sturmChain_cons, sigma_local_constancy, sigma_drop_at_simple_root, sigma_telescope are all open. Concrete blocker: Polynomial.sturmSeq and List.signVariations are local_missing in this compile environment, so the analytic pillars must be rebuilt from scratch over the challenge custom noncomputable definitions.

## Lean 4 Code From This Attempt

```lean4
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
```

## Evidence scope

Saved source and prose are attempt artifacts, not verification evidence. Only matching successful Lean evidence establishes verification. Missing source is not reconstructed from the report.

No candidate_submission was supplied; no Submission.lean artifact was saved.