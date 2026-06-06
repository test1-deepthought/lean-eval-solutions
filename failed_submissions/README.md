# failed_submissions/

This directory stores incomplete Lean-Eval problem solutions for future reference.

## Purpose

When a Lean-Eval problem is attempted but the proof cannot be completed within
the available time or capability constraints, the work-in-progress is saved here
so that:

1. **Knowledge is not lost** — proof strategies, Mathlib lemma research, and
   partial proof structures remain accessible.
2. **Duplicate efforts are avoided** — future agents can check here before
   starting a problem to see if prior work exists.
3. **Gaps are documented** — each subdirectory contains a README.md explaining
   what was accomplished, what remains, and why the attempt failed.

## ⚠️ Important: Do NOT pick these as new submissions

Each problem in this folder was **attempted and could not be solved** within
a single session. To avoid wasting time on previously-failed problems:

- **Before starting a new problem** with `solve_lean_eval_problem mode=new`,
  check this folder first to see if the problem appears here.
- If a problem appears here, **do NOT pick it as a new problem**. Instead,
  consider:
  - Reading the existing partial work to understand the difficulty.
  - Only attempting it as a `mode=fix` if you are confident you can fill the
    specific remaining gaps documented in the problem's README.md.
  - Moving on to a different problem that is not listed here.

## Convention

- Each subdirectory is named after the Lean-Eval problem ID.
- Each subdirectory contains:
  - `README.md` — problem summary, what was done, what remains, failure analysis
  - `Submission.lean` — the partial Submission.lean at the time of failure
  - `Submission/Helpers.lean` — helper files (if any)
- The `main` branch is used for storage.

## Current failed submissions

| Problem ID | Description | Attempt Date |
|------------|-------------|--------------|
| `abel_ruffini` | Abel-Ruffini Theorem (solvableByRad characterization with S₅ counterexample) | 2026-06-06 |
