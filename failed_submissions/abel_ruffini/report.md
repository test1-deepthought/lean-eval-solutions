# Failed Lean-Eval Submission

Problem: abel_ruffini
Mode: new
Submission ref before failure: (none)

## Verified Lemmas Completed
(record in PROVE frontier state / attached candidate files)

## Current Frontier Lemma
(not supplied)

## Exact Failed Lean Error
The Abel-Ruffini theorem is extremely deep. The forward direction (n ≤ 4 → all degree-n polynomial roots are solvable by radicals) requires the full Cardano/Ferrari formulas or the Galois correspondence "solvable Galois group ⇒ solvable by radicals" which is not in Mathlib. The reverse direction (n ≥ 5 → counterexample) requires proving X⁵-4X+2 is irreducible (Eisenstein), has exactly 3 real roots (analysis), and its Galois group is S₅ (not solvable). All of these require significant Mathlib infrastructure that was partially available but required inlining the Archive code.

## Next Lemma To Prove
(not supplied)
