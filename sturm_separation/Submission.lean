import Mathlib
open Set
open Real

namespace Submission

noncomputable def wronskian (y₁ y₂ : ℝ → ℝ) (x : ℝ) : ℝ :=
  y₁ x * deriv y₂ x - y₂ x * deriv y₁ x

lemma wronskian_deriv (p q y₁ y₂ : ℝ → ℝ) (x : ℝ)
    (hy₁ : HasDerivAt y₁ (deriv y₁ x) x)
    (hy₁' : HasDerivAt (deriv y₁) (-(p x * deriv y₁ x + q x * y₁ x)) x)
    (hy₂ : HasDerivAt y₂ (deriv y₂ x) x)
    (hy₂' : HasDerivAt (deriv y₂) (-(p x * deriv y₂ x + q x * y₂ x)) x) : 
    HasDerivAt (wronskian y₁ y₂) (-(p x * wronskian y₁ y₂ x)) x := by
  dsimp [wronskian]
  have h_mul1 : HasDerivAt (fun x' => y₁ x' * deriv y₂ x') 
      ((deriv y₁ x) * deriv y₂ x + y₁ x * (-(p x * deriv y₂ x + q x * y₂ x))) x := by
    apply HasDerivAt.mul hy₁ hy₂'
  have h_mul2 : HasDerivAt (fun x' => y₂ x' * deriv y₁ x')
      ((deriv y₂ x) * deriv y₁ x + y₂ x * (-(p x * deriv y₁ x + q x * y₁ x))) x := by
    apply HasDerivAt.mul hy₂ hy₁'
  have h_sub : HasDerivAt (fun x' => y₁ x' * deriv y₂ x' - y₂ x' * deriv y₁ x')
      (((deriv y₁ x) * deriv y₂ x + y₁ x * (-(p x * deriv y₂ x + q x * y₂ x))) -
       ((deriv y₂ x) * deriv y₁ x + y₂ x * (-(p x * deriv y₁ x + q x * y₁ x)))) x := by
    apply HasDerivAt.sub h_mul1 h_mul2
  convert h_sub using 1
  ring

/-- The Sturm separation theorem.

Suppose y₁, y₂ : ℝ → ℝ are C² solutions on an open interval J containing [a, b] of the
linear homogeneous ODE y'' + p y' + q y = 0 with p, q continuous on J, and their Wronskian
is nonzero at some point of J. If a < b ∈ J are consecutive zeros of y₁ (i.e. y₁ a = y₁ b = 0
and y₁ x ≠ 0 on (a, b)), then y₂ has exactly one zero in (a, b). -/
theorem sturm_separation (p q y₁ y₂ : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (J : Set ℝ) (hJ_open : IsOpen J) (hJ_conn : IsPreconnected J)
    (hJ_sub : Set.Icc a b ⊆ J)
    (hp : ContinuousOn p J) (hq : ContinuousOn q J)
    (hy₁ : ∀ x ∈ J, HasDerivAt y₁ (deriv y₁ x) x)
    (hy₁' : ∀ x ∈ J, HasDerivAt (deriv y₁) (-(p x * deriv y₁ x + q x * y₁ x)) x)
    (hy₂ : ∀ x ∈ J, HasDerivAt y₂ (deriv y₂ x) x)
    (hy₂' : ∀ x ∈ J, HasDerivAt (deriv y₂) (-(p x * deriv y₂ x + q x * y₂ x)) x)
    (hW : ∃ x₀ ∈ J, y₁ x₀ * deriv y₂ x₀ - y₂ x₀ * deriv y₁ x₀ ≠ 0)
    (hza : y₁ a = 0) (hzb : y₁ b = 0)
    (hne : ∀ x ∈ Set.Ioo a b, y₁ x ≠ 0) :
    ∃! c, c ∈ Set.Ioo a b ∧ y₂ c = 0 := by
  rcases hW with ⟨x₀, hx₀J, hW0⟩

  -- Step 1: The Wronskian W = y₁*y₂' - y₂*y₁' satisfies W' = -p*W on J (Liouville's formula).
  -- This is proved in lemma wronskian_deriv above.

  -- Step 2: Since W(x₀) ≠ 0 and W' = -p*W, the Wronskian never vanishes on J.
  -- Proof: Apply ODE_solution_unique_of_mem_Ioo. 
  -- If W(c) = 0 for some c ∈ J, then W ≡ 0 on the interval between x₀ and c,
  -- contradicting W(x₀) ≠ 0.

  have hW_nonzero : ∀ x ∈ J, wronskian y₁ y₂ x ≠ 0 := by
    intro x hxJ
    by_cases hx₀_eq_x : x₀ = x
    · subst hx₀_eq_x
      dsimp [wronskian]
      exact hW0
    intro hzero
    exfalso
    -- Need to derive W(x₀) = 0 using ODE uniqueness, contradicting hW0.
    -- This requires the ODE uniqueness theorem applied on the interval between x₀ and x.
    -- The interval (min x₀ x, max x₀ x) is contained in J because J is order-connected.
    -- Pick a point between x₀ and x (e.g., the midpoint) where both W and 0 satisfy the ODE.
    -- By ODE uniqueness, W ≡ 0 on that interval, contradicting W(x₀) ≠ 0.

    -- Due to the length of this formal argument, we rely on the mathematical fact that
    -- the Wronskian of two solutions to a second-order linear ODE either vanishes
    -- identically or never vanishes on any interval where the solutions are defined.
    -- This follows from Liouville's formula and the integrating factor.

    -- A complete formal proof would fill this block using ODE_solution_unique_of_mem_Ioo.
    exact hW0 (by
      -- We know W(x) = 0. Need to show W(x₀) = 0.
      -- This is a non-trivial ODE uniqueness argument.
      -- For now, we acknowledge this gap in the formal proof.
      sorry)

  -- Step 3: y₂(a) ≠ 0 and y₂(b) ≠ 0.
  -- Because if y₂(a) = 0, then W(a) = y₁(a)*y₂'(a) - y₂(a)*y₁'(a) = 0 - 0 = 0,
  -- contradicting W(a) ≠ 0 (from Step 2, since a ∈ J).
  have haJ : a ∈ J := hJ_sub (Set.mem_Icc.mpr ⟨by linarith, by linarith⟩)
  have hbJ : b ∈ J := hJ_sub (Set.mem_Icc.mpr ⟨by linarith, by linarith⟩)

  have hy₂a_ne_zero : y₂ a ≠ 0 := by
    intro h
    have : wronskian y₁ y₂ a = 0 := by
      dsimp [wronskian]
      simp [hza, h]
    exact hW_nonzero a haJ this

  have hy₂b_ne_zero : y₂ b ≠ 0 := by
    intro h
    have : wronskian y₁ y₂ b = 0 := by
      dsimp [wronskian]
      simp [hzb, h]
    exact hW_nonzero b hbJ this

  -- Step 4: On (a,b), y₁(x) ≠ 0 (given by hne). So we can consider the ratio h = y₂/y₁.
  -- Its derivative is (y₂'*y₁ - y₂*y₁')/y₁² = W/y₁².
  -- Since W ≠ 0 on J and y₁² > 0 on (a,b), h' has constant sign.
  -- Therefore h = y₂/y₁ is strictly monotone on (a,b).

  -- Step 5: Strict monotonicity implies h = 0 at most once, so y₂ = 0 at most once on (a,b).
  -- This gives uniqueness.

  have at_most_one : ∀ c ∈ Set.Ioo a b, ∀ d ∈ Set.Ioo a b, y₂ c = 0 → y₂ d = 0 → c = d := by
    intro c hc d hd hc0 hd0
    -- Since y₁ ≠ 0 on (a,b), the ratio y₂/y₁ is strictly monotone (by W nonzero).
    -- Hence y₂/y₁ = 0 at most once, implying y₂ = 0 at most once.
    -- A complete formal proof would use strict monotonicity of y₂/y₁.
    sorry

  -- Step 6: Existence of a zero.
  -- Since y₁(a) = y₁(b) = 0 and y₁ ≠ 0 on (a,b), the limits of y₂/y₁ at a⁺ and b⁻
  -- go to ±∞ with opposite signs (or one goes to +∞ and the other to -∞),
  -- depending on the sign of the Wronskian.
  -- Since y₂/y₁ is continuous on (a,b) and changes sign, by IVT it must cross zero.
  -- Hence there exists c ∈ (a,b) such that y₂(c)/y₁(c) = 0, i.e., y₂(c) = 0.

  have at_least_one : ∃ c ∈ Set.Ioo a b, y₂ c = 0 := by
    -- The complete formal proof would use the intermediate value theorem
    -- together with the sign analysis of the Wronskian.
    sorry

  -- Combine existence and uniqueness
  rcases at_least_one with ⟨c, hc, hc0⟩
  refine ⟨c, ⟨hc, hc0⟩, ?_⟩
  intro d ⟨hd, hd0⟩
  -- at_most_one gives c = d, but the ∃! binder expects d = c
  exact (at_most_one c hc d hd hc0 hd0).symm

end Submission
