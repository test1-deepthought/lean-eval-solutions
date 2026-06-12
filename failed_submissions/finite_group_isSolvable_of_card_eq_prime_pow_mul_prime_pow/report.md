# Failed Lean-Eval Submission

Problem: finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow
Mode: new
Submission ref before failure: (none)

## Verified Lemmas Completed
(record in PROVE frontier state / attached candidate files)

## Current Frontier Lemma
conjClass_mul_char_div_charOne_is_algebraicInt - prove that |K|·χ(g)/χ(1) is an algebraic integer using the class sum in MonoidAlgebra ℂ G

## Exact Failed Lean Error
The Burnside p^a q^b theorem requires deep character theory (algebraic integers from character values, class sum centrality, Burnside's conjugacy class lemma) which is not yet available in Mathlib. The FDRep character theory infrastructure exists (char_orthonormal, char_conj, char_one) but the following key lemmas needed for Burnside's theorem are missing and need to be constructed:
1. |K|·χ(g)/χ(1) is an algebraic integer (requires class sum in group algebra, Schur's lemma for FDRep)
2. Burnside's lemma: a conjugacy class of prime-power size > 1 implies a nontrivial normal subgroup
3. A group of order p^a*q^b with a,b>0 has a conjugacy class of prime-power size > 1 (requires Sylow theory + center of p-group)

The easy cases (a=0 or b=0, i.e., G is a p-group) are handled: p-group -> nilpotent -> solvable via IsPGroup.isNilpotent and IsNilpotent.to_isSolvable.

## Next Lemma To Prove
conjClass_mul_char_div_charOne_is_algebraicInt - prove that |K|·χ(g)/χ(1) is an algebraic integer using the class sum in MonoidAlgebra ℂ G
