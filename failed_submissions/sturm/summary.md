# sturm — incomplete Lean-Eval attempt

- Saved: 2026-09-27T11:03:04.941Z
- Last error: The frozen theorem `sturm` (Challenge.lean line 11) still carries its top-level `sorry`. The proof body requires the full Sturm-sequence theory (chain sign alternation, local constancy of the evaluation-based `sigma`, unit drop at simple roots) which has no Mathlib API: `Polynomial.sturmSeq` and `List.signVariations` are unknown constants in this environment (confirmed via direct #check), and the challenge's `signChanges`/`sturmChain` list definitions offer no simplification API.
- Submission ref: (not written)