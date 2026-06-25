# Failed Lean-Eval Submission

Problem: sturm
Mode: fix
Submission ref before failure: (none)

## Verified Lemmas Completed

The following core lemmas have been verified with `lean4_exec` (exit code 0):

1. **`signChanges_cons_cons_nonzero`**: For `a, b ≠ 0` and all entries of `rest` nonzero,
   `signChanges (a :: b :: rest) = (if a*b < 0 then 1 else 0) + signChanges (b :: rest)`.
   This is the key combinatorial lemma for analyzing `sigma` across a root of `p`.

2. **`squarefree_imp_separable`**: Over ℝ, `Squarefree p` implies `Separable p`.
   Uses `PerfectField.separable_iff_squarefree` with `PerfectField.ofCharZero`.
   This connects the problem hypothesis to the Mathlib theory of separable polynomials.

3. **`eval_derivative_ne_zero_of_squarefree_root`**: If `p` is squarefree and `p.eval r = 0`,
   then `(derivative p).eval r ≠ 0`. Uses `Separable` ↔ `IsCoprime p p'` via
   `Polynomial.separable_def`, then `IsCoprime.map (evalRingHom r)` to get a contradiction
   in ℝ if both vanish.

4. **`sign_constant_on_Ioo`**: If a polynomial `q` has no root in `Ioo c d` (with `c < d`),
   then either `∀ x, q.eval x > 0` or `∀ x, q.eval x < 0` on `(c,d)`.
   Uses the Intermediate Value Theorem (`intermediate_value_Ioo` / `intermediate_value_Ioo'`)
   and the fact that polynomial evaluation is continuous (`Polynomial.continuous`).

## Current State

The main theorem `sturm` in `Submission.lean` has a partial proof structure:

- The `R = (p.roots.toFinset).filter (fun x => a < x ∧ x < b)` set is defined.
- The base case (`R.card = 0`) is set up but the argument that `sigma p a = sigma p b` when
  there are no roots is incomplete.
- The inductive step is set up with a root `α ∈ (a,b)` selected, but the critical lemma
  `sigma_drop_at_simple_root` is not yet proven.

## Remaining Work

### Lemma: sigma_drop_at_simple_root (Critical)

Prove: At a simple root `r` of squarefree `p` (so `p'(r) ≠ 0`), there exists `δ > 0` such that
for all `u ∈ (r-δ, r)` and `v ∈ (r, r+δ)`, `sigma p u - sigma p v = 1`.

**Strategy**: 
1. By `eval_derivative_ne_zero_of_squarefree_root`, `p'(r) ≠ 0`.
2. By continuity, `p'` is nonzero in a neighborhood `(r-ε, r+ε)`, hence by `sign_constant_on_Ioo`,
   `p'` has constant sign on `(r-ε, r)` and on `(r, r+ε)`.
3. By the factor theorem, `p(x) = (x - r) * q(x)` where `q(r) = p'(r)`. Near `r`, `(x-r)` changes
   sign while `q(x)` maintains sign (since `q(r) ≠ 0` and `q` is continuous). Hence `p(x)` 
   flips sign across `r`.
4. In the Sturm chain `(p, p', p_2, ...)`, only the first entry `p` changes sign across `r`.
   The second entry `p'` keeps its sign. The remaining entries `p_2, ...` are evaluated at
   points near `r` where they are nonzero and continuous, hence their signs are also stable.
5. Using `signChanges_cons_cons_nonzero`, compute the sign change count before and after `r`:
   - Before: sign pattern is `(sign(p(u)), sign(p'(u)), ...)` 
   - After: sign pattern is `(sign(p(v)), sign(p'(v)), ...)`
   Since `p(u)` and `p(v)` have opposite signs while `p'` and deeper entries have the same
   signs, exactly one sign variation is gained or lost.
6. Show it's lost (not gained): `sigma p u > sigma p v`, and the difference is exactly 1.

**Required Mathlib lemmas**:
- `Polynomial.eq_X_sub_C_of_eval_eq_zero` for factor theorem
- `Polynomial.eval_mul`, `Polynomial.eval_sub`, `Polynomial.eval_C`, `Polynomial.eval_X`
- `Polynomial.continuous` for continuity
- `Metric.mem_nhds_iff` or `eventually_nhdsWithin` for extracting δ from continuity at a point

### Lemma: sigma_const_on_interval (Recurring)

Prove: On an interval `(a,b)` where no Sturm chain member vanishes, `sigma p` is constant.

**Strategy**:
- By `sign_constant_on_Ioo`, each Sturm chain member `q_i` has constant sign on `(a,b)`.
- Hence the sequence `(q_0(a), q_1(a), ..., q_m(a))` has the same sign pattern (ignoring zeros)
  as `(q_0(x), q_1(x), ..., q_m(x))` for any `x ∈ (a,b)`.
- Since `signChanges` depends only on the sign pattern of nonzero entries, `sigma` is constant.

### Main Theorem: Induction

Given the two lemmas above:
1. Let `R = {roots of p in (a,b)}`.
2. Sort them: `a < r_1 < r_2 < ... < r_k < b`.
3. Between consecutive partition points (and between `a` and `r_1`, `r_k` and `b`), no chain root
   exists (by squarefreeness and the properties of the Sturm chain), so `sigma` is constant
   on each subinterval.
4. At each `r_i` (a root of `p`), `sigma` drops by exactly 1.
5. Summing the drops: `sigma a - sigma b = k = |R|`.

## Key Resources

- ChallengeDeps defines `sturmChain`, `signChanges`, `sigma` in `LeanEval.Algebra`.
- The Lean-Eval comparator tests the theorem against the `Solution.lean` specification.
- Mathlib lemmas available for continuity, IVT, separable polynomials, perfect fields.
- The `intermediate_value_Ioo` variants work over ℝ with `ContinuousOn` on `Icc`.

## Attempt Date

2026-06-24
