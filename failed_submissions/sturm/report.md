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
## Attempt 20260618T152502Z

## Agent Response Context

The proof of Sturm's theorem for Lean-Eval problem 'sturm' is incomplete. I have proven:
1. derivative_ne_zero_at_root - at a root of squarefree p, the derivative is nonzero
2. not_mem_roots_of_eval_ne_zero/eval_nonroot_not_mem
3. card_diff_eq_card_filter - cardinality lemma for root counting
4. Various continuity/sign constancy lemmas

Remaining work:
1. Prove sigma is constant on intervals where p has no roots (sigma_const_on_root_free_interval). This requires analyzing the sign pattern at non-p chain member roots using the Euclidean algorithm recurrence p_{i-1} = q_i·p_i - p_{i+1} and the lemma exactly_one_negative.
2. Prove sigma drops by exactly 1 at simple roots of p (sigma_drop_at_root), combining sign_change_at_simple_root with analysis of non-p chain members near the root.
3. Complete the main theorem by induction on the number of roots, using the two lemmas above and the cardinality lemma.

---
## Attempt 20260619T023717Z

## Verified Lean 4 Code From This Attempt

```lean4
import Mathlib
open Polynomial
open Set

lemma eval_mod_eq_eval_of_root (a q : ℝ[X]) (r : ℝ) (hq : q.eval r = 0) : (a % q).eval r = a.eval r := by
  by_cases hq0 : q = 0
  · subst hq0; simp
  · have hlc0 : q.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hq0
    set m := q * C (q.leadingCoeff⁻¹) with hm_def
    have hm_root : m.eval r = 0 := by
      dsimp [m]; simp [hq]
    have hdiv : a %ₘ m + m * (a /ₘ m) = a := Polynomial.modByMonic_add_div a m
    have h_ev_mod : (a %ₘ m).eval r = a.eval r := by
      have := congrArg (fun p => p.eval r) hdiv
      simp [hm_root, eval_add, eval_mul] at this
      nlinarith
    calc
      (a % q).eval r = (a %ₘ m).eval r := by rw [Polynomial.mod_def, hm_def]
      _ = a.eval r := h_ev_mod

lemma squarefree_no_common_root (p : ℝ[X]) (hp : Squarefree p) (r : ℝ) (hr : p.eval r = 0) : 
    (derivative p).eval r ≠ 0 := by
  by_contra! h
  have hXdiv : (X - C r) ∣ p := by
    rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot, hr]
  rcases hXdiv with ⟨q, hpq⟩
  have hq_root : q.eval r = 0 := by
    have hderiv : derivative p = q + (X - C r) * derivative q := by
      calc
        derivative p = derivative ((X - C r) * q) := by rw [hpq]
        _ = derivative (X - C r) * q + (X - C r) * derivative q := by rw [derivative_mul]
        _ = 1 * q + (X - C r) * derivative q := by simp
        _ = q + (X - C r) * derivative q := by simp
    calc
      q.eval r = (q + (X - C r) * derivative q).eval r := by simp
      _ = (derivative p).eval r := by rw [hderiv]
      _ = 0 := h
  have hXdiv_q : (X - C r) ∣ q := by
    rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot, hq_root]
  rcases hXdiv_q with ⟨q', hqq'⟩
  have hXsq_div : (X - C r) * (X - C r) ∣ p := by
    use q'
    calc
      p = (X - C r) * q := hpq
      _ = (X - C r) * ((X - C r) * q') := by rw [hqq']
      _ = (X - C r) * (X - C r) * q' := by ring
  have h_sqfree := hp (X - C r) hXsq_div
  have h_not_unit : ¬ IsUnit (X - C r) := Polynomial.not_isUnit_X_sub_C r
  exact h_not_unit h_sqfree

lemma opposite_signs_at_root (p q : ℝ[X]) (r : ℝ) (hq : q.eval r = 0) (hp : p.eval r ≠ 0) : 
    p.eval r * (-(p % q)).eval r < 0 := by
  have hmod : (p % q).eval r = p.eval r := eval_mod_eq_eval_of_root p q r hq
  have : p.eval r * (-(p.eval r)) < 0 := by
    nlinarith [sq_pos_of_ne_zero hp]
  calc
    p.eval r * (-(p % q)).eval r = p.eval r * (-((p % q).eval r)) := by simp
    _ = p.eval r * (-(p.eval r)) := by rw [hmod]
    _ < 0 := this
```


## Sturm's Theorem - Lean Formalization Attempt

### Status: INCOMPLETE

### Verified Lemmas (3 of 3 - all compiled)

1. **`eval_mod_eq_eval_of_root`**: For polynomials a, q over ℝ and point r, if q(r) = 0, then (a % q)(r) = a(r). This follows from polynomial division: a = (a/q)·q + (a%q), and evaluating at a root of q gives the result.

2. **`squarefree_no_common_root`**: For a squarefree polynomial p and root r (p(r) = 0), the derivative p'(r) ≠ 0. Uses the factor theorem (X - r)|p and the squarefree property: if (X-r)²|p, then X-r is a unit (contradiction).

3. **`opposite_signs_at_root`**: For polynomials p, q with q(r) = 0 and p(r) ≠ 0, we have p(r)·(-(p%q))(r) < 0. This shows that at a root of one chain member, the two neighboring entries have opposite signs.

### Remaining Work (3 major components)

1. **sigma_drop_at_root**: Prove that at a root r of a squarefree polynomial p, sigma drops by exactly 1 when crossing from left to right of r. Requires analyzing the sign pattern of the Sturm chain near a simple root: p changes sign while all later entries maintain their signs, causing exactly one sign variation to be lost.

2. **sigma_const_no_root**: Prove that if p has no root in (x,y), then sigma(p,x) = sigma(p,y). Requires analyzing the behavior at roots of non-p chain members where the opposite_signs lemma shows sigma is invariant.

3. **Interval partition and summation**: Collect all roots of chain members in (a,b), sort them, apply the two lemmas above, and use a telescoping sum to get the final result.

### Complete Proof Sketch

The full Sturm theorem proof follows this structure:
1. For each root r of p (simple, by squarefreeness), pick δ small enough that no other chain member has a root in (r-δ, r+δ). Then sigma drops by exactly 1.
2. For each root r of a non-p chain member, sigma is unchanged.
3. Sort all roots r_1 < ... < r_k in (a,b).
4. sigma(a) - sigma(b) = Σ_i (sigma(r_i-ε_i) - sigma(r_i+ε_i)) = k = number of p-roots in (a,b).

### Isabelle/HOL Comparison
The same theorem is formalized in Manuel Eberl's AFP entry "Sturm_Sequences" (~2000 lines). The Lean 4 formalization would be of similar magnitude.