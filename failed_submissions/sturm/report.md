# Incomplete Lean-Eval attempt: sturm

## Failed Lean Error

The main theorem `Submission.sturm` remains unproved; the placeholder-free Submission.lean still requires the full Sturm-theorem development. Remaining: prove local constancy of sigma off the union of chain roots, the unit jump of sigma at each simple root of p, and telescoping over (a,b), plus chain-coprimality and terminal-constant lemmas.

## Agent Response Context

## Summary

Solved the *Lean-Eval statement alignment and framework* for the `sturm` problem but did **not** complete the machine-checked proof within this session. This is a from-scratch formalization of Sturm's theorem; as the problem's own documentation states, Mathlib has no Sturm chain, no sign-variation counter, and no Sturm's theorem (the reference development is Manuel Eberl's Isabelle AFP entry `Sturm_Sequences`).

## Work completed and verified

1. **Statement skeleton accepted.** The target `sturm` theorem was frozen against the exact formal target
   `((p.roots.toFinset).filter (fun x => a < x ∧ x < b)).card = sigma p a - sigma p b`
   with the challenge definitions `sturmAux`, `sturmChain`, `signChanges`, `sigma` inlined to match `ChallengeDeps.lean` byte-for-byte (confirmed by reading the upstream workspace file).

2. **Key mathematical facts established computationally** (Python/SymPy):
   - Chain structure via negated remainders `pₖ₊₁ = -(pₖ₋₁ mod pₖ)`.
   - **Critical lemma**: at any interior zero x₀ of a chain entry `pₖ` (k ≥ 1), the neighbours satisfy `pₖ₋₁(x₀) = -pₖ₊₁(x₀) ≠ 0` — verified numerically across several squarefree polynomials. This is the crux of the local sign-change analysis (it explains why vanishing intermediate entries do not alter the variation count).

3. **One foundational Lean lemma proved and compile-checked** (`lean4_probe` exit 0):
   `signChanges_cons_cons : signChanges (a::b::t) = (if a*b<0 then 1 else 0) + signChanges (b::t)` for nonzero `a,b`.

## Exact remaining goals (registered frontier)

- `sturmAux_consecutive_coprime` — consecutive chain entries share no common real root.
- `sturmChain_terminal_const` — for squarefree `p`, the last nonzero chain entry is a nonzero constant (no real root), via `Squarefree`/coprimality with the derivative.
- `sigma_locally_const` — `σ` constant on open intervals avoiding all chain roots.
- `sigma_jump_one` — `σ` drops by exactly 1 across each simple root of `p`.
- `telescope_roots` — `σ(a) − σ(b) = #{roots in (a,b)}`, then the `roots.toFinset` cardinality identification.

## Blocker

The full development is a research-grade effort. The residual budget was consumed resolving Lean tactic-level issues in the list-signature calculus; the interval/continuity analysis and telescoping remain.

## Lean 4 Code From This Attempt

```lean4
import Mathlib
open scoped Classical

namespace SC

noncomputable def signChanges (xs : List ℝ) : ℕ :=
  let ys := xs.filter (· ≠ 0)
  ((ys.zip ys.tail).filter (fun q => q.1 * q.2 < 0)).length

lemma signChanges_cons_cons (a b : ℝ) (t : List ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    signChanges (a :: b :: t) = (if a * b < 0 then 1 else 0) + signChanges (b :: t) := by
  unfold signChanges
  simp only
  rw [List.filter_cons_of_pos (by simpa using ha), List.filter_cons_of_pos (by simpa using hb)]
  simp only [List.zip_cons_cons, List.tail_cons, List.filter_cons]
  by_cases h : a * b < 0
  · simp only [h, decide_true, if_true, List.length_cons]
    omega
  · rw [if_neg (by simp [h])]
    simp only [h, decide_false, Bool.false_eq_true, if_false, List.length_cons, zero_add]

end SC
```

## Evidence scope

Saved source and prose are attempt artifacts, not verification evidence. Only matching successful Lean evidence establishes verification. Missing source is not reconstructed from the report.

No candidate_submission was supplied; no Submission.lean artifact was saved.