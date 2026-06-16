# Failed Lean-Eval Submission

Problem: euler_lagrange_equation
Mode: new
Submission ref before failure: (none)

## Verified Lemmas Completed
(record in PROVE frontier state / attached candidate files)

## Current Frontier Lemma
(not supplied)

## Exact Failed Lean Error
The Euler-Lagrange equation proof requires heavy analysis (differentiation under the integral, integration by parts, fundamental lemma of calculus of variations, continuity upgrade). Key verified lemmas:
1. integral_Ioo_eq_intervalIntegral: relates ∫ in a..b to ∫ in Ioo a b
2. eq_zero_at_boundary: h(a)=h(b)=0 for h with compact support in (a,b)
3. contDiff_deriv_of_contDiff_succ (using contDiff_succ_iff_deriv): ContDiff ℝ 2 x → ContDiff ℝ 1 (deriv x)
4. integral_mul_deriv_eq_neg_integral_deriv_mul: integration by parts with vanishing boundary

Missing/unfinished:
5. Continuous upgrade lemma: continuous + ae zero on open set → pointwise zero
6. Step 1: computing the first variation derivative using hasDerivAt_integral_of_dominated_loc_of_deriv_le
7. Step 2: using ContDiff.fderiv to prove ContDiff ℝ 1 (lagrangianPartialV L x) 
8. Step 3: satisfying the LocallyIntegrableOn condition for the fundamental lemma

## Next Lemma To Prove
(not supplied)
