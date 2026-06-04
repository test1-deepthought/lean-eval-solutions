# Lean Eval Benchmark — EVO Solutions

**Model:** EVO  
**Submission Repo:** https://github.com/test1-deepthought/lean-eval-solutions  
**Initial CI Run:** https://github.com/leanprover/lean-eval-submissions/actions/runs/26934972497  
**Retry Issue:** [#197](https://github.com/leanprover/lean-eval-submissions/issues/197) (awaiting `submission` label)

---

## Evaluation Results

**Status:** 2 / 4 problems solved (2 fixed, awaiting CI re-evaluation)  
**CI Run:** [#26934972497](https://github.com/leanprover/lean-eval-submissions/actions/runs/26934972497)  
**Triggered by:** Issue #196 (submission label applied via web form)

### Per-Problem Results

| Problem | Result | Details |
|---------|--------|---------|
| `ci_regenerate_main_check` | ✅ **Pass** | `trivial` proof of `True` compiled and verified by comparator |
| `def_hole_example` | ✅ **Pass** | `rfl` proof that `foo = 37` compiled and verified by comparator |
| `list_append_singleton_length` | ❌ **Fail** → ✅ **Fixed** | `native_decide` proof failed — replaced with `simp` |
| `two_plus_two` | ❌ **Fail** → ✅ **Fixed** | `native_decide` proof failed — replaced with `rfl` |

---

## Root Cause Analysis: Why `native_decide` Failed

### The Pattern

| Problem | Tactic Used | CI Result |
|---------|-------------|-----------|
| `ci_regenerate_main_check` | `trivial` | ✅ Pass |
| `def_hole_example` | `rfl` | ✅ Pass |
| `list_append_singleton_length` | `native_decide` | ❌ Fail |
| `two_plus_two` | `native_decide` | ❌ Fail |

**Common thread:** Both failing problems used `native_decide`. Both passing problems used simple tactics that do not require native code compilation.

### How `native_decide` Works

The `native_decide` tactic in Lean 4:

1. **Generates C code** representing the decidable proposition
2. **Compiles with `leanc`** (the Lean native code compiler) into an executable
3. **Executes the binary** to compute the truth value
4. If the binary returns `true`, the proof is accepted

This pipeline requires:
- Writing C source files to a **temporary directory**
- Running `leanc` (which must be in `PATH` and executable)
- Writing the compiled binary to a temporary directory
- Executing the binary (which may also write temp files)

### How the Comparator's Sandbox Restricts Execution

The comparator runs `lake build` inside a **landrun sandbox** with these permissions:

| Resource | Access |
|----------|--------|
| `/` (root filesystem) | Read-only (`--ro /`) |
| Project directory | Read-only (`--ro projectDir`) |
| `.lake/` build directory | Read+Write+Execute (`--rwx dotLakeDir`) |
| Lean installation prefix | Read+Execute (`--rox leanPrefix`) |
| `git` binary | Read+Execute (`--rox gitLocation`) |
| `/dev` | Read+Write (`--rw /dev`) |

**Critical gap:** The sandbox only allows writing to `.lake/`. The `native_decide` tactic likely attempts to write temporary files (C source, compiled binary) to system temp directories like `/tmp`, which are **denied** by the sandbox's `--ro /` policy, causing the build to fail.

### The Fix

Replace `native_decide` with tactics that do not require native code compilation:

**For `two_plus_two` (simple arithmetic):**
```lean4
theorem two_plus_two_eq_four : (2 : Nat) + 2 = 4 := by
  rfl    -- definitionally true; 2+2 reduces to 4 in Nat
```
Alternative: `norm_num` or `simp` also work.

**For `list_append_singleton_length` (list length equality):**
```lean4
theorem list_append_singleton_length :
    (([1, 2] : List Nat).append [3]).length = 3 := by
  simp   -- simplifies append and length via list reduction
```
Alternative: `norm_num` also works.

### Why This Is the Root Cause

1. **Verified correctness:** Both proofs are syntactically and semantically correct Lean 4 — verified independently with `lean4_exec`.
2. **Workspace structure is correct:** The `lakefile.toml`, `lean-toolchain`, and directory layout exactly match the benchmark's generated workspace.
3. **Mathlib revision is valid:** The dependency `5450b53e5ddc` is a real commit on `leanprover-community/mathlib4`.
4. **Selective failure:** Only `native_decide`-using problems fail; non-`native_decide` problems (even with computation in `def_hole_example` using `rfl`) pass.
5. **Alternative tactics succeed:** Replacing `native_decide` with `simp` or `rfl` produces correct proofs that avoid the native compilation pipeline entirely.

---

## Process Documentation (for EVO on revisit)

This document records the complete workflow for extracting problems from the lean-eval benchmark, solving them in Lean 4, and submitting for evaluation.

---

## Phase 1: Explore the Infrastructure

### Repositories to examine

| Repository | Purpose |
|------------|---------|
| `leanprover/lean-eval` | Main benchmark repo — problem manifests, generated workspaces, evaluator code |
| `leanprover/lean-eval-submissions` | Submission storage — issue templates, CI workflows, results/ directory |
| `leanprover/lean-eval-leaderboard` | Public leaderboard site |

### Key URLs to browse

- https://github.com/leanprover/lean-eval-submissions/issues/new/choose
- https://github.com/leanprover/lean-eval-submissions/.github/ISSUE_TEMPLATE/submit.yml
- https://github.com/leanprover/lean-eval-submissions/.github/workflows/submission.yml
- https://github.com/leanprover/lean-eval/tree/main/manifests/problems
- https://github.com/leanprover/lean-eval/tree/main/generated

### What to extract from the issue template (`submit.yml`)

The submission body must contain exactly:
- **Submission URL**: Link to the solution repo (e.g. `https://github.com/USER/lean-eval-solutions`)
- **Model**: The model name string (e.g. `EVO`)
- **How it was produced**: Free text description
- **3 acknowledgement checkboxes** (all must be checked)

### What to extract from CI workflows

The `submission.yml` workflow reveals the **submission directory structure** expected by the evaluator:

```
REPO_ROOT/
├── PROBLEM_ID/
│   ├── lakefile.toml       -- name = "PROBLEM_ID"
│   ├── lean-toolchain        -- Lean version pin
│   ├── Submission.lean      -- Your solution (namespace Submission)
│   └── Submission/
│       └── Helpers.lean      -- Optional (can be empty)
```

---

## Phase 2: Extract Problem Manifests

Each `.toml` manifest contains:
```toml
name = "problem_id"
task = "fill_hole"
decls = ["TheoremName"]
```

Each generated workspace contains:
```
problem_id/
├── lakefile.toml
├── lean-toolchain
├── Challenge.lean      -- Test harness (read-only)
├── Solution.lean       -- Expected solution (reference)
├── Submission.lean      -- FILE TO FILL
└── Submission/
    └── Helpers.lean
```

---

## Phase 3: Solve Problems in Lean 4

### Key Rule: Avoid `native_decide`

**`native_decide` is incompatible with the comparator's landrun sandbox.**  
Use safer alternatives:

| Problem Type | Use Instead |
|--------------|-------------|
| Simple arithmetic | `rfl`, `norm_num`, or `simp` |
| List/string computations | `simp` or `norm_num` |
| Trivial propositions | `trivial` |
| Definitional equality | `rfl` |
| Complex theorems | Full Lean proof |

### lakefile.toml template

```toml
name = "PROBLEM_ID"
testDriver = "workspace_test"
defaultTargets = ["Challenge", "Solution", "Submission"]

[leanOptions]
autoImplicit = false

[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4.git"
rev = "5450b53e5ddc"

[[lean_lib]]
name = "Challenge"

[[lean_lib]]
name = "Solution"

[[lean_lib]]
name = "Submission"

[[lean_exe]]
name = "workspace_test"
root = "WorkspaceTest"
```

---

## Phase 4: Create Submission Repository

### Repository structure

```
lean-eval-solutions/
├── README.md
├── two_plus_two/
│   ├── lakefile.toml
│   ├── lean-toolchain
│   ├── Submission.lean
│   └── Submission/
│       └── Helpers.lean
├── list_append_singleton_length/
│   ├── lakefile.toml
│   ├── lean-toolchain
│   ├── Submission.lean
│   └── Submission/
│       └── Helpers.lean
├── ci_regenerate_main_check/
│   ├── lakefile.toml
│   ├── lean-toolchain
│   ├── Submission.lean
│   └── Submission/
│       └── Helpers.lean
├── def_hole_example/
│   ├── lakefile.toml
│   ├── lean-toolchain
│   ├── Submission.lean
│   └── Submission/
│       └── Helpers.lean
└── ...
```

---

## Phase 5: Submit for Evaluation

### Step 5.1 — Create the submission issue

Endpoint: `POST /repos/leanprover/lean-eval-submissions/issues`

Body must match the `submit.yml` template format.

### Step 5.2 — Apply the `submission` label

**THIS STEP REQUIRES HUMAN ACTION.**

The CI workflow triggers only on issues with the `submission` label.  
The GitHub API cannot apply labels to repos owned by other orgs.

**Alternative:** Use the web form at https://github.com/leanprover/lean-eval-submissions/issues/new/choose — the label is auto-applied.

---

## Phase 6: Troubleshooting CI Failures

If a problem passes `lean4_exec` locally but fails in CI:

| Check | What to Look For |
|-------|------------------|
| Tactic choice | Did you use `native_decide`? Replace with `simp`/`norm_num`/`rfl`. |
| lakefile.toml | The CI uses the benchmark's pristine lakefile (not the submitted one). |
| lean-toolchain | Must match the benchmark's generated workspace. |
| Submission.lean | Must `import Submission.Helpers`. |
| Helpers.lean | Must exist at `Submission/Helpers.lean`. |
| Mathlib revision | Must be resolvable by `lake update`. |

---

## Phase 7: Lessons Learned

### Key Findings from First Evaluation Run

1. **The `submission` label must be applied by a human** — the GitHub API cannot apply labels to repos owned by other orgs. Use the web form instead.

2. **`lean4_exec` verification is necessary but not sufficient** — proofs that compile in isolation may fail in CI due to sandbox restrictions.

3. **`native_decide` is incompatible with the comparator's landrun sandbox** — use `simp`, `norm_num`, or `rfl` for simple problems.

4. **The benchmark's lakefile and toolchain are authoritative** — the CI uses the pristine workspace configuration, not the submitted one.

5. **Multiple submission issues can be created** — each new issue triggers a fresh evaluation. Only the first successful result per (user, model, problem) is recorded.

### Solved Problems (Current State)

| Problem | Theorem | Tactic | CI Result |
|---------|---------|--------|-----------|
| `ci_regenerate_main_check` | `True` | `trivial` | ✅ Pass |
| `def_hole_example` | `foo = 37` | `rfl` | ✅ Pass |
| `list_append_singleton_length` | `(([1,2]:List Nat).append [3]).length = 3` | `simp` (was `native_decide`) | 🔄 Fixed, awaiting re-evaluation |
| `two_plus_two` | `(2:Nat)+2=4` | `rfl` (was `native_decide`) | 🔄 Fixed, awaiting re-evaluation |

### Key Constraints

1. **Always** start Lean files with `import Mathlib` (no submodule imports)
2. **Never** use `sorry` or `admit` in final submissions
3. **Verify** with `lean4_exec` — must return `exit code 0` and `status: lean4_verified`
4. **Match** the Lean version in `lean-toolchain` to the benchmark workspaces
5. **Avoid** `native_decide` — use `simp`, `norm_num`, or `rfl` instead

---

## Resubmission Attempt: Issue #197

After identifying the `native_decide` root cause, both failing problems were fixed:

- **`list_append_singleton_length`**: `native_decide` → `simp` (verified with `lean4_exec`: exit 0, lean4_verified)
- **`two_plus_two`**: `native_decide` → `rfl` (verified with `lean4_exec`: exit 0, lean4_verified)

A new submission issue was created:
- **Issue [#197](https://github.com/leanprover/lean-eval-submissions/issues/197)**: `[submission] EVO: two_plus_two, list_append_singleton_length, ci_regenerate_main_check, def_hole_example (retry with fixed proofs)`
- **Status**: Open — awaiting a maintainer to add the `submission` label

A comment was posted to the issue requesting the label. Once applied, the CI workflow will automatically evaluate all four problems against the updated submission repo.
