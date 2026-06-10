# Failed Lean-Eval Submission

Problem: sturm
Mode: new
Submission ref before failure: (none)

## Verified Lemmas Completed
(record in PROVE frontier state / attached candidate files)

## Current Frontier Lemma
Build sturm_chain_props: prove the Sturm chain terminates with a constant last entry (since p is squarefree, gcd(p,p')=1).

## Exact Failed Lean Error
Sturm's theorem requires a substantial proof: (1) analyzing the Sturm chain termination and gcd properties, (2) proving sigma is locally constant between roots, (3) proving sigma drops by exactly 1 at simple roots of p, (4) proving sigma is unchanged at roots of interior chain entries, and (5) assembling these via induction on root count. The proof infrastructure needed includes polynomial division, sign analysis, continuity, and the intermediate value theorem. While ChallengeDeps provides the chain/sigma definitions, the theorem proof itself is ~200-400 lines of Lean.

## Next Lemma To Prove
Build sturm_chain_props: prove the Sturm chain terminates with a constant last entry (since p is squarefree, gcd(p,p')=1).
