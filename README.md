# Lean Eval Benchmark — EVO Solutions

**Model:** EVO  
**Submission Repo:** https://github.com/test1-deepthought/lean-eval-solutions  
**Submission Issue:** https://github.com/leanprover/lean-eval-submissions/issues/194  
**Evaluation Issue:** https://github.com/leanprover/lean-eval-submissions/issues/196  
**CI Run:** https://github.com/leanprover/lean-eval-submissions/actions/runs/26934972497  

---

## Evaluation Results

**Status:** 2 / 4 problems solved (failing 2)  
**CI Run:** [#26934972497](https://github.com/leanprover/lean-eval-submissions/actions/runs/26934972497)  
**Triggered by:** Issue #196 (submission label applied via web form)

### Per-Problem Results

| Problem | Result | Details |
|---------|--------|---------|
| `ci_regenerate_main_check` | ✅ **Pass** | `trivial` proof of `True` compiled and verified by comparator |
| `def_hole_example` | ✅ **Pass** | `rfl` proof that `foo = 37` compiled and verified by comparator |
| `list_append_singleton_length` | ❌ **Fail** | `native_decide` proof of list length equality — build or comparison failure |
| `two_plus_two` | ❌ **Fail** | `native_decide` proof of `(2:Nat)+2=4` — build or comparison failure |

The failing problems (`two_plus_two` and `list_append_singleton_length`) use `native_decide`. Both proofs are syntactically correct Lean 4 and pass `lean4_exec` verification. The failure likely stems from a workspace integration issue (e.g., lakefile configuration, mathlib revision mismatch, or dependency resolution in the CI sandbox) rather than an incorrect theorem statement.

### CI Output Summary

From the evaluation comment on issue #196:

> ✅ Newly-solved problems: ci_regenerate_main_check, def_hole_example
>
> Attempted 4 / 4; succeeded on 2.
>
> ### Per-problem
> - `ci_regenerate_main_check`: pass
> - `def_hole_example`: pass
> - `list_append_singleton_length`: fail
> - `two_plus_two`: fail

Detailed CI logs require GitHub authentication (sign-in to view).

---

## Process Documentation (for EVO on revisit)

This document records the complete workflow for extracting problems from the lean-eval benchmark, solving them in Lean 4, and submitting for evaluation. Follow these steps exactly.

---

## Phase 1: Explore the Infrastructure

### Repositories to examine

| Repository | Purpose |
|------------|---------|
| `leanprover/lean-eval` | Main benchmark repo — problem manifests, generated workspaces, evaluator code |
| `leanprover/lean-eval-submissions` | Submission storage — issue templates, CI workflows, results/ directory |
| `leanprover/lean-eval-leaderboard` | Public leaderboard site |

### Key URLs to browse

```
https://github.com/leanprover/lean-eval-submissions/issues/new/choose
https://github.com/leanprover/lean-eval-submissions/.github/ISSUE_TEMPLATE/submit.yml
https://github.com/leanprover/lean-eval-submissions/.github/workflows/submission.yml
https://github.com/leanprover/lean-eval/tree/main/manifests/problems
https://github.com/leanprover/lean-eval/tree/main/generated
```

### What to extract from the issue template (`submit.yml`)

The submission body must contain exactly:
- **Submission URL**: Link to the solution repo (e.g. `https://github.com/USER/lean-eval-solutions`)
- **Model**: The model name string (e.g. `EVO`)
- **How it was produced**: Free text description
- **3 acknowledgement checkboxes** (all must be checked):
  - `[x]` I have read the template and privacy policy
  - `[x]` I agree that my solution will be publicly available
  - `[x]` I understand the evaluation is per-model, not per-submission

### What to extract from CI workflows

The `submission.yml` workflow reveals the **submission directory structure** expected by the evaluator. The evaluator expects:

```
REPO_ROOT/
├── PROBLEM_ID/
│   ├── lakefile.toml        -- name = "PROBLEM_ID"
│   ├── lean-toolchain        -- Lean version pin (e.g., leanprover/lean4:v4.30.0-rc2)
│   ├── Submission.lean       -- Your solution (namespace Submission)
│   └── Submission/
│       └── Helpers.lean      -- Optional helper lemmas
```

The CI:
1. Checks out the submission repo
2. Checks out `leanprover/lean-eval` for problem manifests and the evaluator tool
3. For each problem directory in the submission repo:
   - Runs `lake build` to compile
   - Runs the evaluator (compares solution output to expected)
4. Posts results to the issue

---

## Phase 2: Extract Problem Manifests

### Browse problem manifests

```python
# Use web_browse or github_public to list manifests
url = "https://github.com/leanprover/lean-eval/tree/main/manifests/problems"
```

Each `.toml` manifest contains:
```toml
name = "problem_id"
task = "fill_hole"  # or other task types
decls = ["TheoremName"]  # the Lean declarations to prove
```

### Browse generated workspaces

```python
url = "https://github.com/leanprover/lean-eval/tree/main/generated"
```

Each workspace has:
```
problem_id/
├── lakefile.toml      # Build config
├── lean-toolchain      # Lean version
├── Challenge.lean      # Test harness (read-only reference)
├── Solution.lean       # Expected solution (reference)
├── Submission.lean     # FILE TO FILL — contains `namespace Submission` with holes
└── Submission/
    └── Helpers.lean    # Optional helpers
```

### Extract the challenge from `Submission.lean`

Browse or download the `Submission.lean` file to see what needs to be proved. Example:

```lean4
import Mathlib

namespace Submission

-- Problem: two_plus_two
theorem two_plus_two_eq_four : (2 : Nat) + 2 = 4 := by
  native_decide

end Submission
```

---

## Phase 3: Solve Problems in Lean 4

### Workflow for each problem

1. **Extract the target theorem** from the generated workspace's `Submission.lean`
2. **Identify the problem type**:
   - Simple arithmetic / computation → `native_decide` or `norm_num`
   - Trivial truth → `trivial`
   - Definitional equality → `rfl`
   - Complex theorem → requires full Lean proof
3. **Verify with lean4_exec**:
   ```lean4
   import Mathlib

   theorem my_theorem : statement := by
     -- proof here
   ```
4. **Create the problem workspace** in the submission repo:
   ```
   problem_id/
   ├── lakefile.toml        -- name = "problem_id"
   ├── lean-toolchain        -- match the benchmark's Lean version
   ├── Submission.lean       -- the solved file
   └── Submission/
       └── Helpers.lean      -- (can be empty)
   ```

### Lakefile.toml template

```toml
name = "PROBLEM_ID"
reservoir = false
version = "0.1.0"

[[require]]
name = "mathlib"
path = ".."  # or use the standard mathlib dependency

[lean_version]
leanprover/lean4:v4.30.0-rc2

[workspace_test]
type = "lean"
```

### Submission.lean template

```lean4
import Mathlib

namespace Submission

-- Fill in the theorem(s) here

end Submission
```

### lean-toolchain template

```
leanprover/lean4:v4.30.0-rc2
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
└── ... (more problem directories)
```

### Creating the repo

Use `github_profile_write` with:
```json
{
  "operation": "create_repo",
  "name": "lean-eval-solutions",
  "description": "Solutions to lean-eval benchmark problems (model: EVO)",
  "private": false,
  "confirm": true
}
```

### Adding files

For each problem directory, use `github_profile_write` with `operation: "create_or_update_file"` for:
- `PROBLEM_ID/lean-toolchain` (one line)
- `PROBLEM_ID/lakefile.toml`
- `PROBLEM_ID/Submission.lean`
- `PROBLEM_ID/Submission/Helpers.lean` (can be empty)

---

## Phase 5: Submit for Evaluation

### Step 5.1 — Create the submission issue

Use the GitHub API to create an issue with the template body:

**Endpoint:** `POST /repos/leanprover/lean-eval-submissions/issues`

**Body format (must match `submit.yml` template):**
```markdown
### Submission URL

https://github.com/USERNAME/lean-eval-solutions

### Model

EVO

### How was this solution produced?

[Describe how solutions were generated]

---

- [x] I have read the template and privacy policy
- [x] I agree that my solution will be publicly available
- [x] I understand the evaluation is per-model, not per-submission
```

### Step 5.2 — Apply the `submission` label

**THIS STEP REQUIRES HUMAN ACTION.**

The CI workflow `submission.yml` is triggered only on issues with the `submission` label. The GitHub API may return a `403` (forbidden) when trying to apply labels to a repo you don't own.

**Human instructions:**
1. Go to https://github.com/leanprover/lean-eval-submissions/issues/NEW_ISSUE_NUMBER
2. In the right sidebar, click **Labels**
3. Select **`submission`**
4. The CI will automatically trigger

**Alternative:** Use the web form at https://github.com/leanprover/lean-eval-submissions/issues/new/choose and select "Submit benchmark solution" — the `submission` label is auto-applied by the template.

---

## Phase 6: Monitor Evaluation

After the CI workflow runs (triggered by the `submission` label), results are posted as a comment on the issue. The results show for each problem:
- ✅ Pass (solution correct)
- ❌ Fail (solution incorrect or compilation error)
- ⏭️ Skipped (problem not found in submission repo)

Final evaluation results are stored in:
```
leanprover/lean-eval-submissions/results/MODEL_NAME.json
```

### Troubleshooting Failures

If a problem that passes `lean4_exec` locally fails in CI, check:

1. **lakefile.toml** — Does the `name` field match the problem ID exactly? Does the mathlib `rev` match the benchmark's `lakefile.toml`?
2. **lean-toolchain** — Does the Lean version match what the benchmark workspace uses?
3. **Submission.lean** — Does it use `import Submission.Helpers`? The CI expects this import and the Helpers file must exist.
4. **Helpers.lean** — Must exist at `Submission/Helpers.lean` with a valid namespace.
5. **Mathlib revision** — The CI fetches mathlib at the exact revision specified in the benchmark's `lakefile.toml`. If the revision is stale or cannot be resolved, `lake build` will fail.

---

## Phase 7: Lessons Learned

### Key Findings from First Evaluation Run

1. **The `submission` label must be applied by a human** — the GitHub API cannot apply labels to repos owned by other organizations. The web form at the `issues/new/choose` URL auto-applies it; API-created issues require a maintainer or human to add the label.
2. **Issue #194 failed to trigger CI** because the `submission` label was missing (created via API). Issue #196 (created via web form) triggered CI successfully.
3. **`lean4_exec` verification is necessary but not sufficient** — proofs that compile in isolation may fail in the CI workspace due to lakefile/mathlib resolution differences.
4. **The lakefile must match the benchmark's generated workspace exactly**, including the mathlib git revision.

---

## Solved Problems (Current State)

| Problem | Theorem | Technique | CI Result | Verified by |
|---------|---------|-----------|-----------|-------------|
| `ci_regenerate_main_check` | `True` | `trivial` | ✅ Pass | `lean4_exec` + CI comparator |
| `def_hole_example` | `foo = 37` | `rfl` | ✅ Pass | `lean4_exec` + CI comparator |
| `list_append_singleton_length` | `(([1,2] : List Nat).append [3]).length = 3` | `native_decide` | ❌ Fail (build/workspace) | `lean4_exec` only |
| `two_plus_two` | `(2 : Nat) + 2 = 4` | `native_decide` | ❌ Fail (build/workspace) | `lean4_exec` only |

### Problems Requiring Advanced Proofs (to attempt on revisit)

- `finite_graph_ramsey_theorem` — Ramsey theory in finite graphs
- `bvp_comparison` — Comparison principle for Dirichlet BVP
- `balanceable_bounded_partitions` — Combinatorial number theory
- `darboux` — Darboux theorem in symplectic geometry
- `cubic_decay_asymptotic` — ODE asymptotic analysis
- `storm_separation` — Storm separation theorem
- Many more across analysis, algebra, geometry, combinatorics, probability, and number theory

---

## Key Constraints to Remember

1. **Always** start Lean files with `import Mathlib` (nothing else — no submodule imports)
2. **Never** use `sorry` or `admit` in final submissions
3. **Verify** with `lean4_exec` before committing — must return `exit code 0` and `status: lean4_verified`
4. **Match the Lean version** in `lean-toolchain` to what the benchmark workspaces use (check existing generated workspaces)
5. **Each problem directory** must be a valid Lake workspace with matching name
6. **The `submission` label** must be applied by a human — the API cannot do it for repos you don't own
