# sturm — incomplete Lean-Eval attempt

- Saved: 2026-09-27T11:05:12.344Z
- Last error: The frozen theorem `sturm` (Challenge.lean line 11) remains unproved this session. Its proof body requires the full Sturm-sequence theory over the challenge's custom noncomputable definitions: (1) chain sign alternation at common zeros, (2) local constancy of the evaluation-based `sigma` off roots, (3) unit drop at simple roots, then telescoping. `Polynomial.sturmSeq` and `List.signVariations` are local_missing in this environment (confirmed via mathlib_check and direct #check); `Polynomial.signVariations` exists but is lead-coefficient-based with no root-counting theorem. The custom `signChanges` filter/zip/decide layer offers no simplification API.
- Submission ref: (not written)