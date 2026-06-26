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

---
## Attempt 20260625T094517Z

## Verified Lean 4 Code From This Attempt

```lean4
import Mathlib
open Polynomial
open Set
open scoped Classical

lemma triple_sign_lemma (a b c : ℝ) (hac : a * c < 0) (hb : b ≠ 0) : 
    ((if a * b < 0 then 1 else 0 : ℕ) + (if b * c < 0 then 1 else 0 : ℕ)) = 1 := by
  have ha_ne_zero : a ≠ 0 := by intro hzero; subst hzero; nlinarith
  have hc_ne_zero : c ≠ 0 := by intro hzero; subst hzero; nlinarith
  have ha_sign : a > 0 ∨ a < 0 := lt_or_gt_of_ne ha_ne_zero.symm
  have hb_sign : b > 0 ∨ b < 0 := lt_or_gt_of_ne hb.symm
  rcases ha_sign with (ha_pos | ha_neg)
  · have hc_neg : c < 0 := by nlinarith
    rcases hb_sign with (hb_pos | hb_neg)
    · have h1 : ¬ (a * b < 0) := by nlinarith; have h2 : b * c < 0 := by nlinarith; simp [h1, h2]
    · have h1 : a * b < 0 := by nlinarith; have h2 : ¬ (b * c < 0) := by nlinarith; simp [h1, h2]
  · have hc_pos : c > 0 := by nlinarith
    rcases hb_sign with (hb_pos | hb_neg)
    · have h1 : a * b < 0 := by nlinarith; have h2 : ¬ (b * c < 0) := by nlinarith; simp [h1, h2]
    · have h1 : ¬ (a * b < 0) := by nlinarith; have h2 : b * c < 0 := by nlinarith; simp [h1, h2]

lemma eval_remainder_at_root (a b : ℝ[X]) (r : ℝ) (hb : b.eval r = 0) : (a % b).eval r = a.eval r := by
  have hdiv := EuclideanDomain.div_add_mod a b
  have hval := congrArg (fun q : ℝ[X] => q.eval r) hdiv
  simp [hb] at hval; exact hval

lemma sign_constant_on_Ioo (q : ℝ[X]) (c d : ℝ) (hcd : c < d) (h_no_root : ∀ x ∈ Ioo c d, q.eval x ≠ 0) :
    (∀ x ∈ Ioo c d, q.eval x > 0) ∨ (∀ x ∈ Ioo c d, q.eval x < 0) := by
  have h_cont : Continuous (q.eval : ℝ → ℝ) := Polynomial.continuous q
  by_cases hpos : ∃ x ∈ Ioo c d, q.eval x > 0
  · rcases hpos with ⟨x, hx, hxpos⟩; refine Or.inl ?_
    intro y hy; by_contra! h_notpos
    have hy_nonzero : q.eval y ≠ 0 := h_no_root y hy
    have hy_neg : q.eval y < 0 := by have : q.eval y ≤ 0 := h_notpos; exact Ne.lt_of_le hy_nonzero this
    by_cases hxy : x < y
    · have h_cont_on : ContinuousOn (q.eval : ℝ → ℝ) (Icc x y) := h_cont.continuousOn
      have h0_in : (0 : ℝ) ∈ Ioo (q.eval y) (q.eval x) := by constructor <;> linarith
      have h_contains : Ioo (q.eval y) (q.eval x) ⊆ (q.eval : ℝ → ℝ) '' Ioo x y :=
        intermediate_value_Ioo' (by linarith) h_cont_on
      rcases h_contains h0_in with ⟨z, hz, hz0⟩
      apply h_no_root z; · rcases hz with ⟨hzx, hzy⟩; exact ⟨lt_of_lt_of_le hx.1 hzx.le, lt_of_le_of_lt hzy.le hy.2⟩
      · exact hz0
    · have hyx : y < x := by
        have hy_le_x : y ≤ x := by linarith
        have hy_ne_x : y ≠ x := by intro h_eq; subst h_eq; linarith
        exact Ne.lt_of_le hy_ne_x hy_le_x
      have h_cont_on : ContinuousOn (q.eval : ℝ → ℝ) (Icc y x) := h_cont.continuousOn
      have h0_in : (0 : ℝ) ∈ Ioo (q.eval y) (q.eval x) := by constructor <;> linarith
      have h_contains : Ioo (q.eval y) (q.eval x) ⊆ (q.eval : ℝ → ℝ) '' Ioo y x :=
        intermediate_value_Ioo (by linarith) h_cont_on
      rcases h_contains h0_in with ⟨z, hz, hz0⟩
      apply h_no_root z; · rcases hz with ⟨hzy, hzx⟩; exact ⟨lt_of_lt_of_le hy.1 hzy.le, lt_of_le_of_lt hzx.le hx.2⟩
      · exact hz0
  · refine Or.inr ?_
    intro y hy; have hy_nonzero : q.eval y ≠ 0 := h_no_root y hy
    have hy_nonpos : q.eval y ≤ 0 := by by_contra! hpos_y; exact hpos ⟨y, hy, hpos_y⟩
    exact Ne.lt_of_le hy_nonzero hy_nonpos

lemma squarefree_imp_separable (p : ℝ[X]) (hp : Squarefree p) : Separable p := by
  haveI : CharZero ℝ := by infer_instance
  haveI : PerfectField ℝ := PerfectField.ofCharZero
  rw [PerfectField.separable_iff_squarefree]; exact hp

lemma eval_derivative_ne_zero_of_squarefree_root (p : ℝ[X]) (hp : Squarefree p) (r : ℝ) (hr : p.eval r = 0) :
    (derivative p).eval r ≠ 0 := by
  have hsep : Separable p := squarefree_imp_separable p hp
  have hcop : IsCoprime p (derivative p) := ((Polynomial.separable_def p).mp hsep)
  intro hderiv
  have h_cop_eval : IsCoprime (p.eval r) ((derivative p).eval r) := hcop.map (evalRingHom r)
  rcases h_cop_eval with ⟨a, b, h⟩; rw [hr, hderiv] at h; simp at h

lemma factor_theorem_with_deriv (p : ℝ[X]) (r : ℝ) (hp0 : p.eval r = 0) : ∃ q : ℝ[X], p = (X - C r) * q ∧ q.eval r = (derivative p).eval r := by
  have hfactor : (X - C r) ∣ p := by rw [Polynomial.dvd_iff_isRoot]; exact hp0
  rcases hfactor with ⟨q, hpq⟩; refine ⟨q, hpq, ?_⟩
  have hderiv : derivative p = q + (X - C r) * derivative q := by
    rw [hpq, derivative_mul, derivative_sub, derivative_X, derivative_C]; ring
  calc q.eval r = (q + (X - C r) * derivative q).eval r := by simp
    _ = (derivative p).eval r := by rw [hderiv]

lemma nonzero_near (q : ℝ[X]) (r : ℝ) (hq : q.eval r ≠ 0) : ∃ ε > 0, ∀ x, |x - r| < ε → q.eval x ≠ 0 := by
  have hcont : Continuous (q.eval : ℝ → ℝ) := Polynomial.continuous q
  have hcont_at : ContinuousAt (q.eval : ℝ → ℝ) r := hcont.continuousAt
  have hevent : ∀ᶠ x in nhds r, q.eval x ≠ 0 := hcont_at.tendsto.eventually_ne hq
  rcases Metric.mem_nhds_iff.mp hevent with ⟨ε, hε, hball⟩
  refine ⟨ε, hε, ?_⟩; intro x hx_dist; apply hball; rw [Metric.mem_ball, Real.dist_eq]; exact hx_dist

lemma signChanges_cons_cons_nonzero (a b : ℝ) (rest : List ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hrest : ∀ x ∈ rest, x ≠ 0) :
    signChanges (a :: b :: rest) = (if a * b < 0 then 1 else 0) + signChanges (b :: rest) := by
  unfold signChanges
  have hfilter_all : (a :: b :: rest).filter (· ≠ 0) = a :: b :: rest := by
    refine List.filter_eq_self.mpr ?_
    intro x hx; simp at hx; rcases hx with (rfl|rfl|hx)
    · simp [ha]
    · simp [hb]
    · simp [hrest x hx]
  have hfilter_rest : (b :: rest).filter (· ≠ 0) = b :: rest := by
    refine List.filter_eq_self.mpr ?_
    intro x hx; simp at hx; rcases hx with (rfl|hx)
    · simp [hb]
    · simp [hrest x hx]
  rw [hfilter_all, hfilter_rest]; dsimp
  by_cases h : a * b < 0; · simp [h]; omega; · simp [h]; omega
```

---
## Attempt 20260625T094736Z

## Verified Lean 4 Code From This Attempt

```lean4
import Mathlib
open Polynomial
open Set
open scoped Classical

lemma triple_sign_lemma (a b c : ℝ) (hac : a * c < 0) (hb : b ≠ 0) : 
    ((if a * b < 0 then 1 else 0 : ℕ) + (if b * c < 0 then 1 else 0 : ℕ)) = 1 := by
  have ha_ne_zero : a ≠ 0 := by intro hzero; subst hzero; nlinarith
  have hc_ne_zero : c ≠ 0 := by intro hzero; subst hzero; nlinarith
  have ha_sign : a > 0 ∨ a < 0 := lt_or_gt_of_ne ha_ne_zero.symm
  have hb_sign : b > 0 ∨ b < 0 := lt_or_gt_of_ne hb.symm
  rcases ha_sign with (ha_pos | ha_neg)
  · have hc_neg : c < 0 := by nlinarith
    rcases hb_sign with (hb_pos | hb_neg)
    · have h1 : ¬ (a * b < 0) := by nlinarith; have h2 : b * c < 0 := by nlinarith; simp [h1, h2]
    · have h1 : a * b < 0 := by nlinarith; have h2 : ¬ (b * c < 0) := by nlinarith; simp [h1, h2]
  · have hc_pos : c > 0 := by nlinarith
    rcases hb_sign with (hb_pos | hb_neg)
    · have h1 : a * b < 0 := by nlinarith; have h2 : ¬ (b * c < 0) := by nlinarith; simp [h1, h2]
    · have h1 : ¬ (a * b < 0) := by nlinarith; have h2 : b * c < 0 := by nlinarith; simp [h1, h2]

lemma eval_remainder_at_root (a b : ℝ[X]) (r : ℝ) (hb : b.eval r = 0) : (a % b).eval r = a.eval r := by
  have hdiv := EuclideanDomain.div_add_mod a b
  have hval := congrArg (fun q : ℝ[X] => q.eval r) hdiv
  simp [hb] at hval; exact hval

lemma sign_constant_on_Ioo (q : ℝ[X]) (c d : ℝ) (hcd : c < d) (h_no_root : ∀ x ∈ Ioo c d, q.eval x ≠ 0) :
    (∀ x ∈ Ioo c d, q.eval x > 0) ∨ (∀ x ∈ Ioo c d, q.eval x < 0) := by
  have h_cont : Continuous (q.eval : ℝ → ℝ) := Polynomial.continuous q
  by_cases hpos : ∃ x ∈ Ioo c d, q.eval x > 0
  · rcases hpos with ⟨x, hx, hxpos⟩; refine Or.inl ?_
    intro y hy; by_contra! h_notpos
    have hy_nonzero : q.eval y ≠ 0 := h_no_root y hy
    have hy_neg : q.eval y < 0 := by have : q.eval y ≤ 0 := h_notpos; exact Ne.lt_of_le hy_nonzero this
    by_cases hxy : x < y
    · have h_cont_on : ContinuousOn (q.eval : ℝ → ℝ) (Icc x y) := h_cont.continuousOn
      have h0_in : (0 : ℝ) ∈ Ioo (q.eval y) (q.eval x) := by constructor <;> linarith
      have h_contains : Ioo (q.eval y) (q.eval x) ⊆ (q.eval : ℝ → ℝ) '' Ioo x y :=
        intermediate_value_Ioo' (by linarith) h_cont_on
      rcases h_contains h0_in with ⟨z, hz, hz0⟩
      apply h_no_root z; · rcases hz with ⟨hzx, hzy⟩; exact ⟨lt_of_lt_of_le hx.1 hzx.le, lt_of_le_of_lt hzy.le hy.2⟩
      · exact hz0
    · have hyx : y < x := by
        have hy_le_x : y ≤ x := by linarith
        have hy_ne_x : y ≠ x := by intro h_eq; subst h_eq; linarith
        exact Ne.lt_of_le hy_ne_x hy_le_x
      have h_cont_on : ContinuousOn (q.eval : ℝ → ℝ) (Icc y x) := h_cont.continuousOn
      have h0_in : (0 : ℝ) ∈ Ioo (q.eval y) (q.eval x) := by constructor <;> linarith
      have h_contains : Ioo (q.eval y) (q.eval x) ⊆ (q.eval : ℝ → ℝ) '' Ioo y x :=
        intermediate_value_Ioo (by linarith) h_cont_on
      rcases h_contains h0_in with ⟨z, hz, hz0⟩
      apply h_no_root z; · rcases hz with ⟨hzy, hzx⟩; exact ⟨lt_of_lt_of_le hy.1 hzy.le, lt_of_le_of_lt hzx.le hx.2⟩
      · exact hz0
  · refine Or.inr ?_
    intro y hy; have hy_nonzero : q.eval y ≠ 0 := h_no_root y hy
    have hy_nonpos : q.eval y ≤ 0 := by by_contra! hpos_y; exact hpos ⟨y, hy, hpos_y⟩
    exact Ne.lt_of_le hy_nonzero hy_nonpos

lemma squarefree_imp_separable (p : ℝ[X]) (hp : Squarefree p) : Separable p := by
  haveI : CharZero ℝ := by infer_instance
  haveI : PerfectField ℝ := PerfectField.ofCharZero
  rw [PerfectField.separable_iff_squarefree]; exact hp

lemma eval_derivative_ne_zero_of_squarefree_root (p : ℝ[X]) (hp : Squarefree p) (r : ℝ) (hr : p.eval r = 0) :
    (derivative p).eval r ≠ 0 := by
  have hsep : Separable p := squarefree_imp_separable p hp
  have hcop : IsCoprime p (derivative p) := ((Polynomial.separable_def p).mp hsep)
  intro hderiv
  have h_cop_eval : IsCoprime (p.eval r) ((derivative p).eval r) := hcop.map (evalRingHom r)
  rcases h_cop_eval with ⟨a, b, h⟩; rw [hr, hderiv] at h; simp at h

lemma factor_theorem_with_deriv (p : ℝ[X]) (r : ℝ) (hp0 : p.eval r = 0) : ∃ q : ℝ[X], p = (X - C r) * q ∧ q.eval r = (derivative p).eval r := by
  have hfactor : (X - C r) ∣ p := by rw [Polynomial.dvd_iff_isRoot]; exact hp0
  rcases hfactor with ⟨q, hpq⟩; refine ⟨q, hpq, ?_⟩
  have hderiv : derivative p = q + (X - C r) * derivative q := by
    rw [hpq, derivative_mul, derivative_sub, derivative_X, derivative_C]; ring
  calc q.eval r = (q + (X - C r) * derivative q).eval r := by simp
    _ = (derivative p).eval r := by rw [hderiv]

lemma nonzero_near (q : ℝ[X]) (r : ℝ) (hq : q.eval r ≠ 0) : ∃ ε > 0, ∀ x, |x - r| < ε → q.eval x ≠ 0 := by
  have hcont : Continuous (q.eval : ℝ → ℝ) := Polynomial.continuous q
  have hcont_at : ContinuousAt (q.eval : ℝ → ℝ) r := hcont.continuousAt
  have hevent : ∀ᶠ x in nhds r, q.eval x ≠ 0 := hcont_at.tendsto.eventually_ne hq
  rcases Metric.mem_nhds_iff.mp hevent with ⟨ε, hε, hball⟩
  refine ⟨ε, hε, ?_⟩; intro x hx_dist; apply hball; rw [Metric.mem_ball, Real.dist_eq]; exact hx_dist

lemma signChanges_cons_cons_nonzero (a b : ℝ) (rest : List ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hrest : ∀ x ∈ rest, x ≠ 0) :
    signChanges (a :: b :: rest) = (if a * b < 0 then 1 else 0) + signChanges (b :: rest) := by
  unfold signChanges
  have hfilter_all : (a :: b :: rest).filter (· ≠ 0) = a :: b :: rest := by
    refine List.filter_eq_self.mpr ?_
    intro x hx; simp at hx; rcases hx with (rfl|rfl|hx)
    · simp [ha]
    · simp [hb]
    · simp [hrest x hx]
  have hfilter_rest : (b :: rest).filter (· ≠ 0) = b :: rest := by
    refine List.filter_eq_self.mpr ?_
    intro x hx; simp at hx; rcases hx with (rfl|hx)
    · simp [hb]
    · simp [hrest x hx]
  rw [hfilter_all, hfilter_rest]; dsimp
  by_cases h : a * b < 0; · simp [h]; omega; · simp [h]; omega
```

---
## Attempt 20260626T150636Z

Partial attempt - WIP on sigma_drop_at_simple_root lemma

---
## Attempt 20260626T151315Z

WIP on sturm proof - working on key lemmas