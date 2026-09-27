# Incomplete Lean-Eval attempt: sturm

## Failed Lean Error

The frozen final theorem `sturm` remains unproved. Verified this session (Lean exit 0, no sorry): sturmAux_zero, sturmAux_succ, sturmAux_stop, signChanges_nil, mod_eval_at_root (the linchpin Euclidean identity (a % b).eval β = a.eval β given b.eval β = 0), rem_degree_lt. The three load-bearing pillars are unproved and lack any Mathlib API: (1) chain sign alternation of consecutive entries at their common zeros, (2) local constancy of the evaluation-based `sigma` on root-free intervals, (3) unit drop of `sigma` at each simple root. Even the degenerate constant case (card = sigma(C c) a - sigma(C c) b) fails: it reduces to signChanges of a singleton evaluation list, which requires manual List.filter/zip/decide reasoning absent from the API.

## Agent Response Context

## Direct Answer

Continuing from the prior turn, I re-derived the Phase-1 mathematical certificate for Sturm's theorem (accepted, certificate 2806a733...), froze the formal target via an accepted statement skeleton, and then genuinely attempted the Lean formalization rather than declaring infeasibility from an assessment.

Genuine machine-checked progress this session (Lean exit 0, no sorry): `mod_eval_at_root` — the linchpin Euclidean evaluation identity (a % b).eval β = a.eval β when b.eval β = 0 — plus the structural bricks `sturmAux_zero`, `sturmAux_succ`, `sturmAux_stop`, `signChanges_nil`, and `rem_degree_lt`.

**Correction to my prior turn.** I previously wrote that "mathlib has no Sturm chain, no sign-variation counter, and no Sturm's theorem." That was imprecise and I retract the blanket form. The Mathlib search index surfaces `Polynomial.sturmSeq` and `Polynomial.signVariations`; exact lookup (`mathlib_check`) shows `Polynomial.signVariations` is present but is **lead-coefficient based** (not the challenge's evaluation-based `signChanges`), while `Polynomial.sturmSeq` is `local_missing` in this environment, as are all its lemmas. `Polynomial.signVariations` has no theorem linking it to root counts (`signVariations_roots`: no results). The challenge's own comment ("no Sturm chain, no sign-variation counter") is therefore accurate for the *counting* infrastructure the theorem needs, but my earlier wording overstated it.

The frozen theorem `sturm` remains unproved. A complete proof requires constructing, from scratch over the opaque `noncomputable` definitions, the full Sturm-sequence theory: (1) sign alternation of consecutive Euclidean-chain entries at their common zeros, (2) local constancy of the evaluation-based `sigma` on root-free intervals, and (3) the unit drop at each simple root — none of which has a Mathlib API, and the definitions are `List.filter/zip/decide` operations with no simplification lemmas.

## Status

INCOMPLETE

## Problem Specification

Lean-Eval `sturm`: for $p \in \mathbb{R}[X]$ squarefree and reals $a < b$ with $p(a),\,p(b) \neq 0$,
$$\bigl|\{x \in (a,b) : p(x) = 0\}\bigr| = \sigma_p(a) - \sigma_p(b),$$
using the challenge's own `sturmAux`/`sturmChain`/`signChanges`/`sigma`. Formal target frozen at `ca0544f0...`.

## Verification

**Phase-1 mathematics: accepted** (structural review, certificate `2806a73364949ed8f7e78ce4965b07a24eeff3e9ddfbce8bf09cfe5dcf29311f`): chain termination with adequate fuel, sign alternation, local constancy of `sigma`, unit drop at each simple root, telescoping over the simple roots.

**Phase-2 Lean: not completed.** No placeholder-free proof of the frozen theorem exists, so no `lean4_exec` certificate is claimed. Verified compiling bricks (this session): `sturmAux_zero`, `sturmAux_succ`, `sturmAux_stop`, `signChanges_nil`, `rem_degree_lt`, and the linchpin `mod_eval_at_root`.

**Exact remaining goal:** the `sturm` proof body. Concretely, the immediate blocker is that even the base 

## Lean 4 Code From This Attempt

```lean4
import Mathlib
open Polynomial
open scoped Classical

namespace LeanEval
namespace Algebra

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

theorem sturmAux_zero (a b : ℝ[X]) : sturmAux a b 0 = [a] := rfl

theorem sturmAux_succ (a b : ℝ[X]) (n : ℕ) (hb : b ≠ 0) :
    sturmAux a b (n + 1) = a :: sturmAux b (-(a % b)) n := by
  simp [sturmAux, hb]

theorem sturmAux_stop (a : ℝ[X]) (n : ℕ) : sturmAux a 0 (n + 1) = [a] := by
  simp [sturmAux]

theorem signChanges_nil : signChanges ([] : List ℝ) = 0 := by
  simp [signChanges]

theorem mod_eval_at_root (a b : ℝ[X]) (β : ℝ) (hβ : b.eval β = 0) :
    (a % b).eval β = a.eval β := by
  have h := EuclideanDomain.mod_add_div a b
  have h2 : (a % b).eval β + (b * (a / b)).eval β = a.eval β := by
    rw [← Polynomial.eval_add, h]
  rw [Polynomial.eval_mul, hβ, zero_mul, add_zero] at h2
  exact h2

theorem rem_degree_lt (a b : ℝ[X]) (hb : b ≠ 0) : (a % b).degree < b.degree :=
  Polynomial.degree_mod_lt a hb

end Algebra
end LeanEval
```

## Evidence scope

Saved source and prose are attempt artifacts, not verification evidence. Only matching successful Lean evidence establishes verification. Missing source is not reconstructed from the report.

No candidate_submission was supplied; no Submission.lean artifact was saved.