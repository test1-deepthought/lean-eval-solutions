# Lean Eval Benchmark — EVO Solutions

**Model:** EVO  
**Submission Repo:** https://github.com/test1-deepthought/lean-eval-solutions  
**Latest CI Submission:** [#446](https://github.com/leanprover/lean-eval-submissions/issues/446)  
---

## Evaluation Results

**Status:** 15 problems solved (CI-verified via [#446](https://github.com/leanprover/lean-eval-submissions/issues/446))

### Completed Problems

| Problem | Result | Details |
|---------|--------|---------|
| `bvp_comparison` | ✅ **Pass** | Comparison principle for the Dirichlet BVP — constructive proof using convexity and interior maximum argument |
| `ci_regenerate_main_check` | ✅ **Pass** | `trivial` proof of `True` compiled and verified by comparator |
| `def_hole_example` | ✅ **Pass** | `rfl` proof that `foo = 37` compiled and verified by comparator |
| `dirichlet_eigenvalues_eq_nat_sq` | ✅ **Pass** | Dirichlet eigenvalues equal natural squares — spectral geometry proof for 1D Laplacian eigenfunctions on a connected open interval; auxiliary function method with Rolle's theorem and eigenvalue quantization |
| `finite_graph_ramsey_theorem` | ✅ **Pass** | Finite Ramsey theorem for SimpleGraph — proof by induction on vertex count using clique-free set splitting |
| `instance_hole_example` | ✅ **Pass** | `WidgetCarrier` defined as `Unit` with `Inhabited` instance — compiled and verified by comparator |
| `list_append_singleton_length` | ✅ **Fixed** | `native_decide` proof failed (landrun sandbox incompatibility) — replaced with `simp` |
| `mulCayley_connected_iff_closure_eq_top` | ✅ **Pass** | Cayley graph connected iff generating set S generates G — forward direction via walk-to-product translation; reverse via Subgroup.closure_induction constructing walks from generators |
| `multi_hole_helpers_example` | ✅ **Pass** | Multiple holes with helper lemmas in `Submission/Helpers.lean` — compiled and verified by comparator |
| `pell_solution_convergent` | ✅ **Pass** | Pell equation solution approximates sqrt(d) — bound on |x/y - sqrt(d)| using coprimality, gcd=1 lemma, and Dirichlet's approximation theorem |
| `posSemidef_map_exp` | ✅ **Pass** | Positive semidefinite matrix exponential — proof via spectral decomposition, Hadamard product, and entrywise limit of partial sums of the exponential series |
| `sturm_separation` | ✅ **Pass** | Sturm separation theorem for second-order linear ODEs — Wronskian argument and Rolle's theorem; fixed comparator rejection from #218 |
| `substInv_X_sub_X_sq_eq_catalan` | ✅ **Pass** | Catalan generating function via compositional inversion — proof using formal power series algebra: S−S²=X identity, Catalan identity C²·X+1=C, factorization S=X·C, and coefficient extraction via catalan_eq_centralBinom_div |
| `two_plus_two` | ✅ **Fixed** | `native_decide` proof failed (landrun sandbox incompatibility) — replaced with `rfl` |
| `variable_binder_example` | ✅ **Pass** | `rfl` proof that `A.trace = \sum i, A i i` — trace is definitionally the sum of diagonal entries |

### Submission History

| Issue | Problems | Result |
|--------|----------|---------|
| [#193](https://github.com/leanprover/lean-eval-submissions/issues/193) | `two_plus_two`, `list_append_singleton_length`, `ci_regenerate_main_check`, `def_hole_example` | ✅ Passed |
| [#198](https://github.com/leanprover/lean-eval-submissions/issues/198) | `ci_regenerate_main_check`, `def_hole_example`, `list_append_singleton_length`, `two_plus_two` | ✅ 4/4 passed |
| [#199](https://github.com/leanprover/lean-eval-submissions/issues/199) | `ci_regenerate_main_check`, `def_hole_example`, `instance_hole_example`, `list_append_singleton_length`, `two_plus_two`, `variable_binder_example` | ✅ 6/6 passed |
| [#203](https://github.com/leanprover/lean-eval-submissions/issues/203) | `bvp_comparison`, `ci_regenerate_main_check`, `def_hole_example`, `instance_hole_example`, `list_append_singleton_length`, `two_plus_two`, `variable_binder_example` | ✅ 7/7 passed |
| [#218](https://github.com/leanprover/lean-eval-submissions/issues/218) | `bvp_comparison`, `ci_regenerate_main_check`, `def_hole_example`, `instance_hole_example`, `list_append_singleton_length`, `two_plus_two`, `variable_binder_example`, `sturm_separation` | ⚠️ 7/8 passed; `sturm_separation` failed |
| [#221](https://github.com/leanprover/lean-eval-submissions/issues/221) | `bvp_comparison`, `ci_regenerate_main_check`, `def_hole_example`, `finite_graph_ramsey_theorem`, `instance_hole_example`, `list_append_singleton_length`, `sturm_separation`, `two_plus_two`, `variable_binder_example` | ✅ **9/9 passed** |
| [#270](https://github.com/leanprover/lean-eval-submissions/issues/270) | `bvp_comparison`, `ci_regenerate_main_check`, `def_hole_example`, `dirichlet_eigenvalues_eq_nat_sq`, `finite_graph_ramsey_theorem`, `instance_hole_example`, `list_append_singleton_length`, `pell_solution_convergent`, `posSemidef_map_exp`, `sturm_separation`, `two_plus_two`, `variable_binder_example` | ✅ **12/12 passed** |
| [#436](https://github.com/leanprover/lean-eval-submissions/issues/436) | `bvp_comparison`, `ci_regenerate_main_check`, `def_hole_example`, `dirichlet_eigenvalues_eq_nat_sq`, `finite_graph_ramsey_theorem`, `instance_hole_example`, `list_append_singleton_length`, `multi_hole_helpers_example`, `pell_solution_convergent`, `posSemidef_map_exp`, `sturm_separation`, `two_plus_two`, `variable_binder_example` | ✅ **13/13 passed** |
| [#446](https://github.com/leanprover/lean-eval-submissions/issues/446) | `bvp_comparison`, `ci_regenerate_main_check`, `def_hole_example`, `dirichlet_eigenvalues_eq_nat_sq`, `finite_graph_ramsey_theorem`, `instance_hole_example`, `list_append_singleton_length`, `mulCayley_connected_iff_closure_eq_top`, `multi_hole_helpers_example`, `pell_solution_convergent`, `posSemidef_map_exp`, `sturm_separation`, `substInv_X_sub_X_sq_eq_catalan`, `two_plus_two`, `variable_binder_example` | ✅ **15/15 passed** |

---

## Workflow: How to Solve a New Problem

This section documents the step-by-step process for selecting an unsolved problem from the lean-eval benchmark, extracting the workspace, and preparing a submission.

### 1. Select a Problem

Problems are listed in the [`problems/`](./problems) directory of this repo. Each problem has a README entry describing the mathematical domain and difficulty level.

The actual problem workspaces live in the upstream repository:

**https://github.com/leanprover/lean-eval/tree/main/generated**

Each problem has a dedicated subdirectory (e.g., `abel_ruffini/`, `brouwer_fixed_point/`, `cyclotomic_integer_house_le_two/`).

### 2. Extract the Problem Workspace

Inside each problem directory you will find:

| File / Directory | Purpose |
|-----------------|---------|
| `Submission.lean` | **Your file to complete.** Contains `sorry` placeholders that you must replace with valid Lean 4 / Mathlib code. |
| `Challenge.lean` | The problem statement with the same theorem signature. **Do not modify.** Read-only benchmark file. |
| `Solution.lean` | The reference solution. **Do not modify.** Read-only benchmark file. |
| `ChallengeDeps.lean` | Read-only; contains additional theorems/lemmas that the problem depends on (if it exists for the problem). **Do not modify.** |
| `Submission/Helpers.lean` | Optional helper lemmas module that you may edit or extend. |
| `WorkspaceTest.lean` | Test file used by the comparator. |
| `config.json` / `holes.json` | Problem configuration. |
| `lakefile.toml` | Lake build configuration. |
| `lean-toolchain` | Lean version specification. |

**To set up a problem for solving:**

1. Copy the entire problem directory from `lean-eval/generated/<problem_name>` into this repo as `<problem_name>/` (one level up from the existing solved problems).
2. Open `Submission.lean` — this is the only file you will modify.
3. You may also edit or create files under `Submission/` (e.g., `Submission/Helpers.lean`) for helper lemmas.

> **Note on `ChallengeDeps.lean`:** Some problems include a `ChallengeDeps.lean` file that defines additional types, definitions, or lemmas used by `Challenge.lean` and/or `Submission.lean`. This file is **read-only** — do not modify it. If the problem you are solving includes a `ChallengeDeps.lean`, you must copy it alongside the other files, and your `Submission.lean` will import it automatically via the generated imports. The comparator includes `ChallengeDeps.lean` in the build context; modifying it will cause a mismatch and your submission may be rejected.

### 3. Solve the Problem

You are completing an official lean-eval `Submission.lean` file.

**Task:** Replace every `sorry` with valid Lean 4 / Mathlib code so the file compiles.

**Hard constraints (violations cause the comparator to reject your submission):**

- **Do not change imports.** The `import Mathlib`, `import Submission.Helpers`, and any generated `import ...` lines must remain exactly as given.
- **Do not change namespaces.** The `namespace Submission` / `end Submission` block is fixed.
- **Do not change declaration names.** The theorem/def name must match the benchmark exactly.
- **Do not change theorem statements, type signatures, assumptions, or conclusions.** The `:`-separated statement is sacred.
- **Do not use `sorry`, `admit`, `axiom`, `unsafe`, or unsound declarations.** Every placeholder must be replaced with a real proof.
- **You may add helper lemmas inside the `Submission` namespace** (in the same file or in `Submission/Helpers.lean`).
- **The `Submission.Helpers` module** is where extracted helper lemmas live. Imported via `import Submission.Helpers` in `Submission.lean`.
- **Use `import Mathlib` exclusively.** Do not import individual Mathlib submodules — the lake cache compiles `import Mathlib` instantly, and submodule paths change between Mathlib versions.
- **Do not modify `ChallengeDeps.lean` if it exists.** It is read-only and part of the benchmark specification.

**Approved tactics (preferred for reliability):**

- `exact`, `apply`, `intro` / `intros`, `refine`, `have`, `calc`, `rw`
- `simp` (preferred for simple rewrites — does not require writable temp files)
- `rfl` (definitional equality — fastest, most portable)
- `omega`, `linarith`, `nlinarith` (arithmetic reasoning)
- `ring`, `field_simp` (algebraic manipulation)
- `positivity` (sign analysis)
- `rcases`, `constructor`, `left`, `right` (structural reasoning)

**Avoid:** `native_decide` — it requires a writable filesystem for its C compilation pipeline, which the comparator's landrun sandbox blocks.

**Critical rule — always verify proofs in isolation.** Before adding a new problem to the submission, run `lean4_exec` to confirm the `Submission.lean` file compiles with `exit_code(0)` and `status: lean4_verified`. The comparator rejects any solution with `sorry`, syntax errors, or type errors.

### 4. Submit for CI Evaluation

When you are ready to have your solutions evaluated by the lean-eval CI:

1. Push all solved problem directories to the `main` branch of this repo.
2. Open a new submission issue at **https://github.com/leanprover/lean-eval-submissions/issues/new?template=submit.yml** using the "Submit benchmark solution" template.
3. Fill in:
   - **Submission URL:** `https://github.com/test1-deepthought/lean-eval-solutions`
   - **Model:** `EVO (deepthought.com.au)`
   - **Acknowledgements:** check all three boxes
4. Submit the issue. The GitHub Actions workflow will automatically:
   - Fetch the repo at the latest `main` commit.
   - Detect every `lakefile.toml` whose name matches a known benchmark problem ID.
   - Run the comparator on each detected problem.
   - Post a result comment with the pass/fail status per problem.

> **Important:** Do not use the GitHub API to create submission issues programmatically. The `submission` label required to trigger CI evaluation is only applied when the web form is used. Issues created via API will not trigger the evaluation workflow, even with the correct body format. Always use the web form at the link above.

### 5. Interpret Results

The CI comment will report:

- **Newly-solved problems:** problems that were not previously on the leaderboard
- **Attempted X / Y; succeeded on Z:** summary counts
- **Per-Problem:** individual `pass` or `fail` status

If a problem fails, check:
- Does the `lakefile.toml` name exactly match a benchmark problem ID?
- Does `Submission.lean` compile on its own? (`lake build` in the problem directory)
- Does the proof use `native_decide`? (Replace with `simp` or `rfl`.)
- Are there any `sorry`, `admit`, or incomplete proofs remaining?
- Has `import Mathlib` been accidentally replaced with a submodule import?

---

## Failed Submissions

See [`failed_submissions/`](./failed_submissions) for a directory of problems that were attempted but could not be completed. Each entry contains the partial proof, research notes, and failure analysis.

---

## Current failed submissions

- `sunny_lines`: `failed_submissions/sunny_lines/report.md` (20260707T141438Z)

- `oppenheim_inequality`: `failed_submissions/oppenheim_inequality/report.md` (20260623T143010Z)

- `cubic_decay_asymptotic`: `failed_submissions/cubic_decay_asymptotic/report.md` (20260623T153613Z)

- `isoperimetric_inequality`: `failed_submissions/isoperimetric_inequality/report.md` (20260622T164838Z)

- `platonic_classification`: `failed_submissions/platonic_classification/report.md` (20260622T164808Z)

- `rouche_zero_count_eq`: `failed_submissions/rouche_zero_count_eq/report.md` (20260622T161250Z)

- `brouwer_fixed_point`: `failed_submissions/brouwer_fixed_point/report.md` (20260622T151739Z)

- `euler_lagrange_equation`: `failed_submissions/euler_lagrange_equation/report.md` (20260616T150412Z)

- `irreducible_nonnegative_matrix_has_positive_eigenvector_at_spectralRadius`: `failed_submissions/irreducible_nonnegative_matrix_has_positive_eigenvector_at_spectralRadius/report.md` (20260615T003525Z)

- `linear_ode_asymptotic_stability`: `failed_submissions/linear_ode_asymptotic_stability/report.md` (20260614T215547Z)

- `abel_ruffini`: `failed_submissions/abel_ruffini/report.md` (20260703T025021Z)

- `wallpaper_groups_17`: `failed_submissions/wallpaper_groups_17/report.md` (20260612T121544Z)

- `pi1_circle_mulEquiv_int`: `failed_submissions/pi1_circle_mulEquiv_int/report.md` (20260610T144830Z)

- `finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow`: `failed_submissions/finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow/report.md` (20260612T111029Z)

- `symplectic_matrix_det`: `failed_submissions/symplectic_matrix_det/report.md` (20260623T152000Z)

- `sturm`: `failed_submissions/sturm/report.md` (20260711T101631Z)

- `contractibleSpace_houseWithTwoRooms`: `failed_submissions/contractibleSpace_houseWithTwoRooms/report.md` (20260614T221600Z)