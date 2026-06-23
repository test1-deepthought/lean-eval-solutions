import Mathlib
open PowerSeries

namespace Submission

noncomputable def catQ : ℚ⟦X⟧ := PowerSeries.map (algebraMap ℕ ℚ) catalanSeries

lemma catQ_sq_mul_X_add_one_eq_catQ : catQ ^ 2 * X + 1 = catQ := by
  have h' : (PowerSeries.map (algebraMap ℕ ℚ)) (catalanSeries ^ 2 * X + 1) = 
    (PowerSeries.map (algebraMap ℕ ℚ)) catalanSeries := by
    rw [catalanSeries_sq_mul_X_add_one]
  simpa [catQ, map_add, map_mul, map_pow] using h'

lemma catQ_minus_X_mul_catQ_sq_eq_one : catQ - X * catQ ^ 2 = 1 := by
  have h := catQ_sq_mul_X_add_one_eq_catQ
  calc
    catQ - X * catQ ^ 2 = (catQ ^ 2 * X + 1) - X * catQ ^ 2 := by rw [h]
    _ = catQ ^ 2 * X + 1 - X * catQ ^ 2 := rfl
    _ = (catQ ^ 2 * X - X * catQ ^ 2) + 1 := by ring
    _ = 0 + 1 := by
      have : catQ ^ 2 * X = X * catQ ^ 2 := by ring
      simp [this]
    _ = 1 := by simp

noncomputable def GQ : ℚ⟦X⟧ := X * catQ

lemma GQ_sub_GQ_sq_eq_X : GQ - GQ ^ 2 = X := by
  calc
    GQ - GQ ^ 2 = X * catQ - (X * catQ) ^ 2 := rfl
    _ = X * catQ - X ^ 2 * catQ ^ 2 := by ring
    _ = X * (catQ - X * catQ ^ 2) := by ring
    _ = X * 1 := by rw [catQ_minus_X_mul_catQ_sq_eq_one]
    _ = X := by simp

-- Proof: the compositional inverse of X - X^2 is the Catalan generating function
theorem substInv_X_sub_X_sq_eq_catalan (n : ℕ) :
    haveI : Invertible (coeff 1 ((X : ℚ⟦X⟧) - X ^ 2)) := by
      simp [coeff_X, coeff_X_pow]; exact invertibleOne
    coeff (n + 1) (substInv ((X : ℚ⟦X⟧) - X ^ 2)) =
      (Nat.choose (2 * n) n : ℚ) / (↑n + 1) := by
  haveI : Invertible (coeff 1 ((X : ℚ⟦X⟧) - X ^ 2)) := by
    simp [coeff_X, coeff_X_pow]; exact invertibleOne
  
  have h_const : constantCoeff ((X : ℚ⟦X⟧) - X ^ 2) = 0 := by simp
  have h_subst_eq : subst (substInv ((X : ℚ⟦X⟧) - X ^ 2)) ((X : ℚ⟦X⟧) - X ^ 2) = X :=
    subst_substInv_right ((X : ℚ⟦X⟧) - X ^ 2) h_const
  
  have hG_hasSubst : HasSubst (substInv ((X : ℚ⟦X⟧) - X ^ 2)) :=
    HasSubst.substInv ((X : ℚ⟦X⟧) - X ^ 2)
  
  have h_expand : subst (substInv ((X : ℚ⟦X⟧) - X ^ 2)) ((X : ℚ⟦X⟧) - X ^ 2) =
    (substInv ((X : ℚ⟦X⟧) - X ^ 2)) - (substInv ((X : ℚ⟦X⟧) - X ^ 2)) ^ 2 := by
    calc
      subst (substInv ((X : ℚ⟦X⟧) - X ^ 2)) ((X : ℚ⟦X⟧) - X ^ 2) = 
        subst (substInv ((X : ℚ⟦X⟧) - X ^ 2)) X - subst (substInv ((X : ℚ⟦X⟧) - X ^ 2)) (X ^ 2) :=
        subst_sub hG_hasSubst _ _
      _ = (substInv ((X : ℚ⟦X⟧) - X ^ 2)) - subst (substInv ((X : ℚ⟦X⟧) - X ^ 2)) (X ^ 2) := by
        rw [subst_X hG_hasSubst]
      _ = (substInv ((X : ℚ⟦X⟧) - X ^ 2)) - (subst (substInv ((X : ℚ⟦X⟧) - X ^ 2)) X) ^ 2 := by
        rw [subst_pow hG_hasSubst]
      _ = (substInv ((X : ℚ⟦X⟧) - X ^ 2)) - (substInv ((X : ℚ⟦X⟧) - X ^ 2)) ^ 2 := by
        rw [subst_X hG_hasSubst]
  rw [h_expand] at h_subst_eq
  
  have hG_eq : substInv ((X : ℚ⟦X⟧) - X ^ 2) = X + (substInv ((X : ℚ⟦X⟧) - X ^ 2)) ^ 2 := by
    calc
      substInv ((X : ℚ⟦X⟧) - X ^ 2) = 
        ((substInv ((X : ℚ⟦X⟧) - X ^ 2)) - (substInv ((X : ℚ⟦X⟧) - X ^ 2)) ^ 2) + 
        (substInv ((X : ℚ⟦X⟧) - X ^ 2)) ^ 2 := by ring
      _ = X + (substInv ((X : ℚ⟦X⟧) - X ^ 2)) ^ 2 := by rw [h_subst_eq]
  
  have hGQ_eq : GQ = X + GQ ^ 2 := by
    calc
      GQ = (GQ - GQ ^ 2) + GQ ^ 2 := by ring
      _ = X + GQ ^ 2 := by rw [GQ_sub_GQ_sq_eq_X]
  
  have h_coeff0_G : coeff 0 (substInv ((X : ℚ⟦X⟧) - X ^ 2)) = 0 := by
    have h := constantCoeff_substInv ((X : ℚ⟦X⟧) - X ^ 2)
    simpa [constantCoeff] using h
  
  have h_coeff0_GQ : coeff 0 GQ = 0 := by
    simp [GQ, catQ]
  
  have h_coeff_eq : ∀ n : ℕ, coeff n (substInv ((X : ℚ⟦X⟧) - X ^ 2)) = coeff n GQ := by
    intro n
    induction' n using Nat.strong_induction_on with n ih
    set G := substInv ((X : ℚ⟦X⟧) - X ^ 2) with hG
    
    have h_coeff_G : coeff n G = coeff n X + coeff n (G ^ 2) := by
      have h := congrArg (coeff n) hG_eq
      rw [h, (coeff n).map_add]
    
    have h_coeff_GQ : coeff n GQ = coeff n X + coeff n (GQ ^ 2) := by
      have h := congrArg (coeff n) hGQ_eq
      rw [h, (coeff n).map_add]
    
    have h_sq_eq : coeff n (G ^ 2) = coeff n (GQ ^ 2) := by
      have hG_sum := coeff_mul n G G
      have hGQ_sum := coeff_mul n GQ GQ
      simpa [pow_two] using calc
        coeff n (G * G) = ∑ p ∈ Finset.antidiagonal n, coeff p.1 G * coeff p.2 G := hG_sum
        _ = ∑ p ∈ Finset.antidiagonal n, coeff p.1 GQ * coeff p.2 GQ := by
          apply Finset.sum_congr rfl
          intro p hp
          rw [Finset.mem_antidiagonal] at hp
          by_cases h1 : p.1 = 0
          · simp [h1, h_coeff0_GQ, hG]
          · by_cases h2 : p.2 = 0
            · simp [h2, h_coeff0_GQ, hG]
            · have hp1_lt_n : p.1 < n := by
                have hp_sum : p.1 + p.2 = n := hp
                have hp2_pos : p.2 > 0 := Nat.pos_of_ne_zero h2
                omega
              have hp2_lt_n : p.2 < n := by
                have hp_sum : p.1 + p.2 = n := hp
                have hp1_pos : p.1 > 0 := Nat.pos_of_ne_zero h1
                omega
              rw [ih p.1 hp1_lt_n, ih p.2 hp2_lt_n]
        _ = coeff n (GQ * GQ) := by symm; exact hGQ_sum
    
    rw [h_coeff_G, h_coeff_GQ, h_sq_eq]
  
  have h_coeff_GQ_val : coeff (n + 1) GQ = (catalan n : ℚ) := by
    calc
      coeff (n + 1) GQ = coeff (n + 1) (X * catQ) := rfl
      _ = coeff n catQ := by
        rw [mul_comm]
        simpa [add_comm] using coeff_mul_X_pow (p := catQ) (n := 1) (d := n)
      _ = (catalan n : ℚ) := by
        calc
          coeff n catQ = coeff n ((map (algebraMap ℕ ℚ)) catalanSeries) := rfl
          _ = (algebraMap ℕ ℚ) (coeff n catalanSeries) := by rw [coeff_map]
          _ = (algebraMap ℕ ℚ) (catalan n) := by rw [catalanSeries_coeff n]
          _ = (catalan n : ℚ) := rfl
  
  have h_formula : (catalan n : ℚ) = (Nat.choose (2 * n) n : ℚ) / (↑n + 1) := by
    have h_nat : (n + 1) * catalan n = n.centralBinom := succ_mul_catalan_eq_centralBinom n
    have h_nat_cast : (n + 1 : ℚ) * (catalan n : ℚ) = (n.centralBinom : ℚ) := by exact_mod_cast h_nat
    have h_eq : (n + 1 : ℚ) * (catalan n : ℚ) = (Nat.choose (2 * n) n : ℚ) := by
      simpa [Nat.centralBinom] using h_nat_cast
    field_simp
    nlinarith
  
  have h := h_coeff_eq (n+1)
  convert h.trans ?_ using 1
  · have h_inst_eq : (by simp [coeff_X, coeff_X_pow]; exact invertibleOne : Invertible (coeff 1 ((X : ℚ⟦X⟧) - X ^ 2))) = this := by
      apply Subsingleton.elim
    subst h_inst_eq
    rfl
  · rw [h_coeff_GQ_val, h_formula]

end Submission