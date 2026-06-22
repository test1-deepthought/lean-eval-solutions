import Mathlib
import Submission.Helpers

open SimpleGraph

set_option maxHeartbeats 0

namespace Submission

theorem mulCayley_connected_iff_closure_eq_top {G : Type*} [Group G]
    (S : Set G) :
    (SimpleGraph.mulCayley S).Connected ↔ Subgroup.closure S = ⊤ := by
  constructor
  · intro h
    rw [Subgroup.eq_top_iff']
    have hpre : (SimpleGraph.mulCayley S).Preconnected := h.preconnected
    intro g
    have hreach : (SimpleGraph.mulCayley S).Reachable (1 : G) g := hpre 1 g
    rcases hreach with ⟨w⟩
    have hg : (1⁻¹ * g) ∈ Subgroup.closure S := walk_to_product' S 1 g w
    simpa using hg
  · intro h
    have hgen : ∀ (g : G), g ∈ Subgroup.closure S := by
      intro g
      have := (Subgroup.eq_top_iff' (Subgroup.closure S)).mp h g
      exact this
    have h_reach_one : ∀ (g : G), (SimpleGraph.mulCayley S).Reachable (1 : G) g := by
      intro g
      apply Subgroup.closure_induction (p := fun (x : G) (hx : x ∈ Subgroup.closure S) => 
        (SimpleGraph.mulCayley S).Reachable (1 : G) x)
      · intro s hs
        by_cases hs_eq : s ≠ 1
        · refine ⟨Walk.cons ?_ Walk.nil⟩
          rw [SimpleGraph.mulCayley_adj S 1 s]
          refine ⟨Ne.symm hs_eq, ?_⟩
          left
          simpa using hs
        · have hs_eq' : s = 1 := by
            by_contra h; exact hs_eq h
          subst hs_eq'
          exact ⟨Walk.nil⟩
      · exact ⟨Walk.nil⟩
      · intro x y hx hy hx_reach hy_reach
        rcases hx_reach with ⟨wx⟩
        rcases hy_reach with ⟨wy⟩
        have h_wy' : (SimpleGraph.mulCayley S).Walk x (x * y) := by
          have := mulCayley_mul_walk' S x 1 y wy
          simpa [mul_one] using this
        have : (SimpleGraph.mulCayley S).Reachable (1 : G) (x * y) :=
          ⟨Walk.append wx h_wy'⟩
        exact this
      · intro x hx hx_reach
        rcases hx_reach with ⟨wx⟩
        let wx_rev : (SimpleGraph.mulCayley S).Walk x (1 : G) := wx.reverse
        have h_wx_rev' : (SimpleGraph.mulCayley S).Walk (x⁻¹ * x) (x⁻¹ * (1 : G)) :=
          mulCayley_mul_walk' S (x⁻¹) x 1 wx_rev
        have h1 : x⁻¹ * x = (1 : G) := by simp
        have h2 : x⁻¹ * (1 : G) = x⁻¹ := by simp
        have h_walk : (SimpleGraph.mulCayley S).Walk (1 : G) x⁻¹ := by
          simpa [h1, h2] using h_wx_rev'
        exact ⟨h_walk⟩
      · exact hgen g
    refine {
      preconnected := by
        intro a b
        have h_reach_ab : (SimpleGraph.mulCayley S).Reachable (1 : G) (a⁻¹ * b) := h_reach_one (a⁻¹ * b)
        rcases h_reach_ab with ⟨w⟩
        have h_aw : (SimpleGraph.mulCayley S).Walk (a * (1 : G)) (a * (a⁻¹ * b)) :=
          mulCayley_mul_walk' S a 1 (a⁻¹ * b) w
        have h3 : a * (1 : G) = a := by simp
        have h4 : a * (a⁻¹ * b) = b := by simp
        have h_walk : (SimpleGraph.mulCayley S).Walk a b := by
          simpa [h3, h4] using h_aw
        exact ⟨h_walk⟩
      nonempty := by
        infer_instance
    }

end Submission