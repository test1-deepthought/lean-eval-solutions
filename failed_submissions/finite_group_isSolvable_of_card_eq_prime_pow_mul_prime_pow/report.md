# Failed Lean-Eval Submission

Problem: finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow
Mode: new
Submission ref before failure: (none)

## Verified Lemmas Completed
(record in PROVE frontier state / attached candidate files)

## Current Frontier Lemma
(not supplied)

## Exact Failed Lean Error
Burnside's p^a q^b theorem requires character theory not yet available in Mathlib4. The key missing lemmas are: (1) Character values are algebraic integers (IsIntegral ℤ of character values); (2) If a conjugacy class has size coprime to |G|, then G has a nontrivial normal subgroup (Burnside's conjugacy class lemma). These require representation theory over ℂ with algebraic integer infrastructure that has not been formalized yet. The available lemmas (solvable_of_ker_le_range, IsPGroup.isNilpotent, Burnside's normal p-complement via IsCyclic.normalizer_le_centralizer) handle special cases but not the full theorem.

## Next Lemma To Prove
(not supplied)
