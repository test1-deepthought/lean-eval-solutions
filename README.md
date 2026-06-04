# Lean Eval Benchmark — EVO Solutions

**Model:** EVO  
**Submission Repo:** https://github.com/test1-deepthought/lean-eval-solutions  
**Final Submission:** [Issue #198](https://github.com/leanprover/lean-eval-submissions/issues/198) ✅ **All 4/4 problems passed!**

---

## Evaluation Results

**Status:** ✅ **All 4/4 problems solved and verified by CI!**  
**Submission Issue:** [#198](https://github.com/leanprover/lean-eval-submissions/issues/198)  
**CI Run:** Triggered by issue #198 with `submission` label

### Per-Problem Results

| Problem | Status | Proof Used | Notes |
|---------|--------|-----------|-------|
| `ci_regenerate_main_check` | ✅ **Pass** | `trivial` | Proves `True` |
| `def_hole_example` | ✅ **Pass** | `rfl` | Proves `foo = 37` |
| `list_append_singleton_length` | ✅ **Pass** | `simp` | Replaced `native_decide` with `simp` |
| `two_plus_two` | ✅ **Pass** | `rfl` | Replaced `native_decide` with `rfl` |

---

## Submission History

| Attempt | Issue | Result | Notes |
|---------|-------|--------|-------|
| 1 | [#194](https://github.com/leanprover/lean-eval-submissions/issues/194) | ❌ Not evaluated | API-created issue — missing `submission` label |
| 2 | [#196](https://github.com/leanprover/lean-eval-submissions/issues/196) | ⚠️ 2/4 passed | Web form submission. `native_decide` proofs failed due to landrun sandbox |
| 3 | [#197](https://github.com/leanprover/lean-eval-submissions/issues/197) | ⚠️ Never triggered | Couldn't get `submission` label applied programmatically (needs org admin) |
| 4 | [#198](https://github.com/leanprover/lean-eval-submissions/issues/198) | ✅ **4/4 passed** | Resubmitted with `simp`/`rfl` fixes. All problems passed! |

---

## Root Cause Analysis: Why `native_decide` Failed in CI

### The Problem

The two failing problems (`list_append_singleton_length` and `two_plus_two`) used `native_decide`. This tactic:

1. Generates C code for the decidable proposition
2. Compiles it with `leanc` into an executable binary  
3. Executes the binary to compute the truth value

### The Sandbox Restriction

The comparator runs `lake build` inside a **landrun sandbox** with `--ro /` (read-only root filesystem). Only `.lake/` is writable. The `native_decide` tactic attempts to write temp files (C source, compiled binary) to system temp directories like `/tmp`, which are blocked by the sandbox.

### The Fix

Replace `native_decide` with tactics that don't require native code compilation:

| Original | Fixed | Works because |
|----------|-------|--------------|
| `native_decide` | `simp` | List reduction via `simp` is purely symbolic |
| `native_decide` | `rfl` | `2+2` is definitionally `4` in `Nat` |

---

## Unsolved Problems

This repository contains solutions to the **4 solved problems** listed above. The remaining **~146 problems** in the [lean-eval benchmark](https://github.com/leanprover/lean-eval) are unsolved and documented in the [`unsolved/`](./unsolved/) directory.

These are research-level formal mathematics theorems spanning:
- **Algebra:** Abel-Ruffini, Baer-Suzuki, Brauer-Fowler, Feit-Thompson, Golod-Shafarevich
- **Analysis:** Brouwer fixed point, Darboux theorem, Cauchy-Kovalevskaya, Sobolev embedding
- **Geometry:** Darboux theorem, Fáry-Milnor, Poincaré conjectures, Whitney embedding
- **Number Theory:** Fermat's Last Theorem, Green-Tao, Thue-Siegel-Roth, Baker-Wüstholz
- **Topology:** Conway knots, Jordan curve, Schoenflies, classification of surfaces
- **Combinatorics:** Szemerédi theorem, Ramsey theory, upper bound theorem
- **And many more...**

These problems require deep mathematical expertise and extensive Mathlib formalization work far beyond the scope of this initial submission effort.

---

## Process Documentation

### How to Submit Fixes

1. Clone the remote repo as a **separate, self-contained workspace** (not as a subdirectory of lean-eval)
2. Create the directory and `lakefile.toml` matching the generated workspace structure
3. Write `Submission.lean` filling the proof hole(s)
4. Verify locally with `lean4_exec` (e.g., via the EVO sandbox)
5. Create a submission issue at https://github.com/leanprover/lean-eval-submissions/issues/new/choose using the **web form** (which applies the `submission` label)
6. Wait for CI to evaluate (~2-5 minutes)
7. Check results in the issue comments

### The `submission` Label

- **Required** for CI to trigger. Without it, the issue just sits there.
- **Cannot be applied via the GitHub API** on the `leanprover` org (requires admin write access or a PAT with `org:write` scope).
- **Can be applied** by: (a) the web form at `issues/new/choose`, or (b) a maintainer with write access to the repo.
- The web form auto-applies the label. API-created issues do not get it.

### Avoiding `native_decide` in Sandboxed CI

- `native_decide` requires C compilation which fails under `landrun --ro /`
- Use `simp`, `rfl`, `norm_num`, `omega`, `dec_trivial` where applicable
- These tactics do not require native code execution

---

## Repository Structure

```
lean-eval-solutions/
├── README.md              # This file
├── unsolved/              # List of unsolved benchmark problems
│   └── README.md
├── ci_regenerate_main_check/
│   ├── lakefile.toml
│   ├── lean-toolchain
│   └── Submission.lean
├── def_hole_example/
│   ├── lakefile.toml
│   ├── lean-toolchain
│   └── Submission.lean
├── list_append_singleton_length/
│   ├── lakefile.toml
│   ├── lean-toolchain
│   └── Submission.lean
└── two_plus_two/
    ├── lakefile.toml
    ├── lean-toolchain
    └── Submission.lean
```
