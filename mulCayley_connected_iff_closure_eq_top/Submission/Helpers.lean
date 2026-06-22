import Mathlib
open SimpleGraph

set_option maxHeartbeats 0

lemma mulCayley_mul_adj {G : Type*} [Group G] (S : Set G) (g : G) (x y : G) :
    (SimpleGraph.mulCayley S).Adj x y → (SimpleGraph.mulCayley S).Adj (g * x) (g * y) := by
  intro hadj
  rw [SimpleGraph.mulCayley_adj S (g * x) (g * y)]
  rcases (SimpleGraph.mulCayley_adj S x y).mp hadj with ⟨h_ne, h_dir⟩
  constructor
  · intro h_eq; apply h_ne; exact mul_left_cancel h_eq
  · rcases h_dir with (h | h)
    · left; simpa [mul_inv, mul_assoc] using h
    · right; simpa [mul_inv, mul_assoc] using h

def mulCayley_mul_walk' {G : Type*} [Group G] (S : Set G) (g : G) : 
    ∀ (a b : G), (SimpleGraph.mulCayley S).Walk a b → (SimpleGraph.mulCayley S).Walk (g * a) (g * b)
  | _, _, Walk.nil => Walk.nil
  | a, b, @Walk.cons _ _ _ v _ h_edge w =>
      let h_edge' : (SimpleGraph.mulCayley S).Adj (g * a) (g * v) := mulCayley_mul_adj S g a v h_edge
      let ih : (SimpleGraph.mulCayley S).Walk (g * v) (g * b) := mulCayley_mul_walk' S g v b w
      Walk.cons h_edge' ih

def walk_to_product' {G : Type*} [Group G] (S : Set G) : 
    ∀ (a b : G), (SimpleGraph.mulCayley S).Walk a b → (a⁻¹ * b) ∈ Subgroup.closure S
  | _, _, Walk.nil => by simp
  | a, b, @Walk.cons _ _ _ v _ h_edge w =>
    have ih : (v⁻¹ * b) ∈ Subgroup.closure S := walk_to_product' S v b w
    by
      rcases (SimpleGraph.mulCayley_adj S a v).mp h_edge with ⟨h_ne, h_dir⟩
      rcases h_dir with (h | h)
      · have h1 : a⁻¹ * b = (a⁻¹ * v) * (v⁻¹ * b) := by
          simp [mul_assoc]
        rw [h1]
        apply Subgroup.mul_mem _ (Subgroup.subset_closure h) ih
      · have h_au : a⁻¹ * v = (v⁻¹ * a)⁻¹ := by
          simp
        have h1 : a⁻¹ * b = (a⁻¹ * v) * (v⁻¹ * b) := by
          simp [mul_assoc]
        rw [h1, h_au]
        apply Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.subset_closure h)) ih