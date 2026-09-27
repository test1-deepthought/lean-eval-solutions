# sturm — incomplete Lean-Eval attempt

- Saved: 2026-09-27T10:53:30.878Z
- Last error: Unsolved goal: the complete proof of the frozen theorem `sturm` requires the full Sturm-sequence theory over the opaque noncomputable definitions sturmAux/sturmChain/signChanges/sigma: (1) sign alternation of consecutive Euclidean-chain entries at their common zeros, (2) local constancy of sigma on intervals free of roots, (3) unit drop of sigma at each simple root. None of these has any Mathlib API; Sigma/SignChanges are List filter/zip operations with no simplification lemmas. Mathlib lacks Sturm, sign-variation, and chain-sign-alternation theory entirely. The helper linchpin `mod_eval_at_root` is now proven, but the top-level `sturm` body remains unproved.
- Submission ref: (not written)