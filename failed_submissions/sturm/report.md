# Failed Lean-Eval Submission

Problem: sturm
Mode: fix
Submission ref before failure: (none)

## Verified Lemmas Completed

The following core lemmas have been verified with `lean4_exec` (exit code 0):

1. **`eval_mod_eq_eval_of_root`**: `p.eval r = 0 → q.eval r = 0 → (p % q).eval r = p.eval r` — The remainder of p divided by q vanishes at a common root.

2. **`squarefree_no_common_root`**: `Squarefree p → p.eval r = 0 → p.derivative.eval r ≠ 0` — At a root of a squarefree polynomial, the derivative does not vanish.

3. **`opposite_signs_at_root`**: `q.eval r = 0 → p.eval r ≠ 0 → p.eval r * (-(p % q)).eval r < 0` — At a root of one Sturm chain member, the two neighbors have opposite signs.

4. **`sign_const_between`**: A polynomial with no roots in the interval (x,y) has the same sign at x and y (by the Intermediate Value Theorem for polynomial functions, which are continuous).

5. **`factor_theorem`**: `p.eval r = 0 → ∃ q, p = (X - C r) * q` — The factor theorem: r is a root iff (X - r) divides p.

6. **`factor_deriv`**: If `p = (X - C r) * q`, then `q.eval r = p.derivative.eval r` — Evaluating the cofactor of (X - r) at r gives the derivative at r.

## Current Frontier Lemma

**`sigma_drop_at_p_root`** — Prove that at a root r of p (with `p.derivative.eval r ≠ 0` by squarefreeness), there exists δ > 0 such that for all u ∈ (r-δ, r) and v ∈ (r, r+δ), we have `sigma p u - sigma p v = 1`.

**Strategy**: Using `factor_theorem`, write `p = (X - r) * q` where `q.eval r = p.derivative.eval r ≠ 0`. This implies `q` maintains constant sign near r. Meanwhile, `(X - r)` changes sign from negative (for u < r) to positive (for v > r). Thus `p(x) = (x-r)·q(x)` changes sign from opposite to `q(r)` to the same as `q(r)`. Meanwhile, neighbors `p1 = p % p'` and `p2 = -(p % p')` evaluate to 0 at r by construction, and by the Euclidean algorithm, `p1` and `p2` are non-zero near r. The sign change analysis of the chain `(p, p1, p2, ...)` around r shows exactly one sign variation drops.

## Exact Failed Lean Error

Proof incomplete. The full formalization of Sturm's theorem requires approximately 200+ additional lines to complete three major components:

### 1. Sigma Drops by Exactly 1 at Each Root of p (sigma_drop_at_p_root)
The continuity + factor theorem argument needs to be formalized:
- Choose δ > 0 small enough that q has no root in (r-δ, r+δ) (possible since q.eval r ≠ 0 and q is continuous)
- Show `sigma p` drops by exactly 1 across r because:
  - At the first position in the chain, sign(p) flips while sign(p1) is locally constant by `opposite_signs_at_root` and continuity
  - All later positions in the chain are unaffected

### 2. Sigma is Locally Constant at Roots of Other Chain Members (sigma_const_at_chain_root)
At a point r where `p_i.eval r = 0` for some i > 0:
- The neighbors `p_{i-1}` and `p_{i+1}` have opposite signs at r (property of the Euclidean remainder chain)
- By `opposite_signs_at_root`, the sign pattern at positions i-1, i, i+1 is `(s, 0, -s)`
- For small δ, `p_i` changes sign but `p_{i-1}` and `p_{i+1}` maintain their signs
- The sign variation count is unchanged because `(s, ±ε, -s)` yields the same count as `(s, 0, -s)`

### 3. Interval Partition and Summation
- Collect all roots of all Sturm chain members within (a,b)
- Sort them: `a < r_1 < r_2 < ... < r_k < b`
- Apply sigma_drop_at_p_root at each r_i that is a root of p
- Apply sigma_const_at_chain_root at each r_i that is a root of a non-p chain member
- `sigma a - sigma b = sum_i (sigma(r_i-ε) - sigma(r_i+ε)) = count of p-roots in (a,b)`

## Next Lemma To Prove

`sigma_drop_at_p_root` — prove that at a root r of p (with p'(r) ≠ 0), there exists δ > 0 such that for u ∈ (r-δ, r), v ∈ (r, r+δ), sigma u - sigma v = 1. This uses the factor theorem to show sign(p) changes while sign(p') doesn't.

## Complete Proof Sketch (for reference)

The full proof of Sturm's theorem follows these steps:

1. **Construct the Sturm chain**: `p_0 = p, p_1 = p', p_{i+1} = -(p_{i-1} % p_i)`. The chain terminates when `p_m = 0`. For squarefree p, the chain has length ≥ 2 and all non-zero members are coprime.

2. **Define sign variation**: `sigma(p, x) =` the number of sign changes in the sequence `(p_0.eval x, ..., p_m.eval x)`, ignoring zeros.

3. **Key properties at non-root points**: At any point x where no chain member vanishes, sigma is locally constant (by continuity and the fact that each polynomial has a neighborhood where it keeps its sign).

4. **Key property at a root of p**: At a root r of p (with p'(r) ≠ 0 by squarefreeness), by the factor theorem `p(x) = (x-r)·q(x)` with `q(r) ≠ 0`. Just to the left of r, `p(x)` has sign opposite to `q(r)`; just to the right, it has the same sign as `q(r)`. Meanwhile, `p_1 = p'` satisfies `p'(r) = q(r) ≠ 0`, so `p'` maintains sign near r. Thus the sign variation count drops by exactly 1 as we cross r.

5. **Key property at a root of `p_i` (i ≥ 1)**: At a root r of `p_i`, the recurrence `p_{i-1} = q_i·p_i - p_{i+1}` (for some quotient `q_i`) implies `p_{i-1}(r)·p_{i+1}(r) < 0`. So the two neighbors have opposite signs, and the sign pattern `(s, 0, -s)` becomes `(s, ±ε, -s)` near r — no net change in variation count.

6. **Interval partition**: Partition (a,b) at all roots of all chain members. Between successive partition points, sigma is constant. At each partition point that is a root of p, sigma drops by 1. At partition points that are roots of other chain members, sigma is unchanged. Summing the drops yields `sigma(a) - sigma(b) =` number of roots of p in (a,b).

---
