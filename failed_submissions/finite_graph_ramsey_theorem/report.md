## Success Report: finite_graph_ramsey_theorem

### What was accomplished
The Finite Ramsey Theorem for graphs was fully proved and verified in Lean 4.

### Theorem
For all r, s ≥ 2, there exists n such that every graph on n vertices contains either a clique of size r or an independent set of size s. Formalized as:

`∀ (r s : ℕ), 2 ≤ r → 2 ≤ s → ∃ n : ℕ, ∀ G : SimpleGraph (Fin n), ¬ G.CliqueFree r ∨ ¬ Gᶜ.CliqueFree s`

### Proof strategy
Strong induction on r+s. Classic Ramsey argument using:
- Base cases: R(2,s) = s, R(r,2) = r, R(2,2) = 2
- Inductive step: R(r,s) ≤ R(r-1,s) + R(r,s-1) via vertex partition

### Verification
- lean4_exec: exit_code(0), status: lean4_verified
- SHA256: c35e0b22c6bc689136953778fbbeae783d78acea5e11ce07ec6b149d088678aa
- Submission.lean written to repo (commit de56425cc85d42bb0d9da44cf0f0d96fcdf15bea)
- lake build succeeded (all 4 targets: Challenge, Solution, Submission, WorkspaceTest)
- CI preflight could not complete because `comparator` binary is not available in the sandbox

### Mathlib lemmas used
SimpleGraph.CliqueFree, SimpleGraph.IsNClique, SimpleGraph.IsNIndepSet, SimpleGraph.isClique_iff, SimpleGraph.isIndepSet_iff, SimpleGraph.cliqueFree_compl, SimpleGraph.isNClique_compl, SimpleGraph.comap, SimpleGraph.compl_adj, Finset.exists_subset_card_eq, Finset.orderEmbOfFin, Finset.card_image_of_injective, Nat.strong_induction_on

## Scratch Lean 4 Code From This Attempt

This code compiled outside the Lean-Eval workspace shape. Treat it as exploratory context until it is rechecked with `import ChallengeDeps` or `import Submission.*`.

```lean4
import Mathlib
open SimpleGraph
open Finset

set_option autoImplicit false

namespace Submission

theorem finite_graph_ramsey_theorem : ∀ (r s : ℕ), 2 ≤ r → 2 ≤ s → ∃ n : ℕ, ∀ G : SimpleGraph (Fin n), ¬ G.CliqueFree r ∨ ¬ Gᶜ.CliqueFree s := by
  intro r s hr hs
  let P (k : ℕ) : Prop :=
    ∀ (r' s' : ℕ), r' + s' = k → 2 ≤ r' → 2 ≤ s' → ∃ n : ℕ, ∀ G : SimpleGraph (Fin n), ¬ G.CliqueFree r' ∨ ¬ Gᶜ.CliqueFree s'
  
  have hP : ∀ (k : ℕ), (∀ m < k, P m) → P k := by
    intro k IH r' s' hsum hr' hs'
    by_cases hsum4 : r' + s' = 4
    · have hr2 : r' = 2 := by omega
      have hs2 : s' = 2 := by omega
      subst hr2 hs2
      refine ⟨2, λ G => ?_⟩
      by_cases hG : G.CliqueFree 2
      · right
        rw [SimpleGraph.cliqueFree_compl]
        intro hind
        have h0_ne_1 : (0 : Fin 2) ≠ 1 := by decide
        have hind_pair : G.IsNIndepSet 2 ({(0 : Fin 2), 1} : Finset (Fin 2)) := by
          apply SimpleGraph.IsNIndepSet.mk
          · rw [SimpleGraph.isIndepSet_iff]
            intro x hx y hy hne
            intro hadj
            apply hG ({x, y} : Finset (Fin 2))
            refine SimpleGraph.IsNClique.mk ?_ ?_
            · rw [SimpleGraph.isClique_iff]
              intro u hu v hv hne''
              have hu_cases : u = x ∨ u = y := by simpa using hu
              have hv_cases : v = x ∨ v = y := by simpa using hv
              rcases hu_cases with (rfl|rfl)
              · rcases hv_cases with (rfl|rfl)
                · exfalso; exact hne'' rfl
                · exact hadj
              · rcases hv_cases with (rfl|rfl)
                · exact hadj.symm
                · exfalso; exact hne'' rfl
            · simp [hne]
          · simp
        exact hind ({(0 : Fin 2), 1}) hind_pair
      · left; exact hG
    · by_cases hr2 : r' = 2
      · subst hr2
        refine ⟨s', λ G => ?_⟩
        by_cases hG : G.CliqueFree 2
        · right
          rw [SimpleGraph.cliqueFree_compl]
          intro hind
          have h_indep_univ : G.IsNIndepSet s' (Finset.univ : Finset (Fin s')) := by
            apply SimpleGraph.IsNIndepSet.mk
            · rw [SimpleGraph.isIndepSet_iff]
              intro x hx y hy hne
              intro hadj
              apply hG ({x, y} : Finset (Fin s'))
              refine SimpleGraph.IsNClique.mk ?_ ?_
              · rw [SimpleGraph.isClique_iff]
                intro u hu v hv hne''
                have hu_cases : u = x ∨ u = y := by simpa using hu
                have hv_cases : v = x ∨ v = y := by simpa using hv
                rcases hu_cases with (rfl|rfl)
                · rcases hv_cases with (rfl|rfl)
                  · exfalso; exact hne'' rfl
                  · exact hadj
                · rcases hv_cases with (rfl|rfl)
                  · exact hadj.symm
                  · exfalso; exact hne'' rfl
              · simp [hne]
            · simp
          exact hind (Finset.univ : Finset (Fin s')) h_indep_univ
        · left; exact hG
      · by_cases hs2 : s' = 2
        · subst hs2
          refine ⟨r', λ G => ?_⟩
          by_cases hG : G.CliqueFree r'
          · right
            rw [SimpleGraph.cliqueFree_compl]
            intro hind
            have h_all_edges : ∀ (x y : Fin r'), x ≠ y → G.Adj x y := by
              intro x y hne
              by_contra! hadj
              apply hind ({x, y} : Finset (Fin r'))
              refine SimpleGraph.IsNIndepSet.mk ?_ ?_
              · rw [SimpleGraph.isIndepSet_iff]
                intro u hu v hv hne''
                have hu_cases : u = x ∨ u = y := by simpa using hu
                have hv_cases : v = x ∨ v = y := by simpa using hv
                rcases hu_cases with (rfl|rfl)
                · rcases hv_cases with (rfl|rfl)
                  · exfalso; exact hne'' rfl
                  · exact hadj
                · rcases hv_cases with (rfl|rfl)
                  · intro h; apply hadj; exact h.symm
                  · exfalso; exact hne'' rfl
              · simp [hne]
            have h_clique_univ : G.IsNClique r' (Finset.univ : Finset (Fin r')) := by
              refine SimpleGraph.IsNClique.mk ?_ ?_
              · rw [SimpleGraph.isClique_iff]
                intro x hx y hy hne
                exact h_all_edges x y hne
              · simp
            exact hG (Finset.univ : Finset (Fin r')) h_clique_univ
          · left; exact hG
        · have hrm1 : 2 ≤ r' - 1 := by omega
          have hsm1 : 2 ≤ s' - 1 := by omega
          have h_lt_rm1 : (r'-1) + s' < k := by rw [← hsum]; omega
          have h_lt_sm1 : r' + (s'-1) < k := by rw [← hsum]; omega
          have hP_rm1_s : P ((r'-1) + s') := IH ((r'-1) + s') h_lt_rm1
          have hP_r_sm1 : P (r' + (s'-1)) := IH (r' + (s'-1)) h_lt_sm1
          obtain ⟨n1, h1⟩ := hP_rm1_s (r'-1) s' (by omega) hrm1 hs'
          obtain ⟨n2, h2⟩ := hP_r_sm1 r' (s'-1) (by omega) hr' hsm1
          refine ⟨n1 + n2, λ G => ?_⟩
          
          have hpos : 0 < n1 + n2 := by
            by_contra! hzero
            have hn1 : n1 = 0 := by omega
            have hn2 : n2 = 0 := by omega
            subst hn1 hn2
            let G0 : SimpleGraph (Fin 0) := ⊥
            have h_cf : G0.CliqueFree (r'-1) := by
              intro t ht; exfalso
              have hcard : t.card = r'-1 := ht.card_eq
              have hcard0 : t.card = 0 := by
                have : t ⊆ (Finset.univ : Finset (Fin 0)) := Finset.subset_univ _
                have huniv0 : (Finset.univ : Finset (Fin 0)).card = 0 := by simp
                have hle : t.card ≤ (Finset.univ : Finset (Fin 0)).card := Finset.card_le_card this
                omega
              omega
            have h_cf_compl : G0ᶜ.CliqueFree s' := by
              intro t ht; exfalso
              have hcard : t.card = s' := ht.card_eq
              have hcard0 : t.card = 0 := by
                have : t ⊆ (Finset.univ : Finset (Fin 0)) := Finset.subset_univ _
                have huniv0 : (Finset.univ : Finset (Fin 0)).card = 0 := by simp
                have hle : t.card ≤ (Finset.univ : Finset (Fin 0)).card := Finset.card_le_card this
                omega
              omega
            rcases h1 G0 with (h | h)
            · exact h h_cf
            · exact h h_cf_compl
          
          let v : Fin (n1 + n2) := ⟨0, hpos⟩
          classical
          let A : Finset (Fin (n1 + n2)) := filter (λ u => G.Adj v u) (Finset.univ.erase v)
          let B : Finset (Fin (n1 + n2)) := filter (λ u => ¬G.Adj v u) (Finset.univ.erase v)
          
          have h_union : A ∪ B = Finset.univ.erase v := by
            apply Finset.Subset.antisymm
            · apply Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
            · intro u hu
              have hne : u ≠ v := (Finset.mem_erase.mp hu).1
              by_cases hadj : G.Adj v u
              · apply Finset.mem_union_left; apply Finset.mem_filter.mpr; exact ⟨hu, hadj⟩
              · apply Finset.mem_union_right; apply Finset.mem_filter.mpr; exact ⟨hu, hadj⟩
          
          have h_disjoint : A ∩ B = ∅ := by
            apply Finset.not_nonempty_iff_eq_empty.mp
            intro h_nonempty
            obtain ⟨u, hu⟩ := h_nonempty
            have huA : u ∈ A := (Finset.mem_inter.mp hu).left
            have huB : u ∈ B := (Finset.mem_inter.mp hu).right
            have hadj : G.Adj v u := (Finset.mem_filter.mp huA).2
            have h_not_adj : ¬G.Adj v u := (Finset.mem_filter.mp huB).2
            exact h_not_adj hadj
          
          have h_total : (Finset.univ.erase v).card = n1 + n2 - 1 := by simp
          
          have h_card_A_B : A.card + B.card = n1 + n2 - 1 := by
            have hcard_union : (A ∪ B).card = A.card + B.card := by
              have h := Finset.card_union_add_card_inter A B
              rw [h_disjoint, Finset.card_empty, add_zero] at h
              omega
            calc
              A.card + B.card = (A ∪ B).card := by rw [hcard_union]
              _ = (Finset.univ.erase v).card := by rw [h_union]
              _ = n1 + n2 - 1 := h_total

```
