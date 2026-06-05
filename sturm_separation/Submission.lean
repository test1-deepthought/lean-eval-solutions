import Mathlib
open Set
open Filter
open Real

lemma exists_bound_on_abs (p : ℝ → ℝ) (a' b' : ℝ) (hle : a' ≤ b') (hp : ContinuousOn p (Set.Icc a' b')) :
    ∃ (K : NNReal), ∀ t ∈ Set.Icc a' b', |p t| ≤ (K : ℝ) := by
  have h_nonempty : (Set.Icc a' b').Nonempty := Set.nonempty_Icc.mpr hle
  have h_cont_abs : ContinuousOn (fun x : ℝ => |p x|) (Set.Icc a' b') := hp.abs
  rcases IsCompact.exists_isMaxOn isCompact_Icc h_nonempty h_cont_abs with ⟨t0, ht0, h_max⟩
  refine ⟨⟨|p t0|, show (0 : ℝ) ≤ |p t0| from abs_nonneg _⟩, ?_⟩
  intro t ht
  simpa using h_max ht

lemma LipschitzOnWith.mono_const {α β : Type _} [PseudoEMetricSpace α] [PseudoEMetricSpace β]
    {K₁ K₂ : NNReal} {f : α → β} {s : Set α} (hf : LipschitzOnWith K₁ f s) (h : K₁ ≤ K₂) :
    LipschitzOnWith K₂ f s := by
  intro x hx y hy
  have h_edist := hf hx hy
  have hK : (K₁ : ENNReal) ≤ (K₂ : ENNReal) := by exact_mod_cast h
  calc
    edist (f x) (f y) ≤ (K₁ : ENNReal) * edist x y := h_edist
    _ ≤ (K₂ : ENNReal) * edist x y := mul_le_mul_of_nonneg_right hK (by positivity)

lemma linear_ode_zero_at_point (a f : ℝ → ℝ) (c d : ℝ) (hcd : c < d) (t₁ t₂ : ℝ) (ht₁ : t₁ ∈ Set.Ioo c d) (ht₂ : t₂ ∈ Set.Ioo c d)
    (ha_cont : ContinuousOn a (Set.Icc c d))
    (hf : ∀ t ∈ Set.Ioo c d, HasDerivAt f (a t * f t) t)
    (hf_t₂ : f t₂ = 0) : f t₁ = 0 := by
  rcases exists_bound_on_abs a c d (by linarith) ha_cont with ⟨K, hK⟩
  set v : ℝ → ℝ → ℝ := fun t' y => a t' * y with hv_def
  set s : ℝ → Set ℝ := fun _ => Set.univ with hs_def
  have hv_lip : ∀ t' ∈ Set.Ioo c d, LipschitzOnWith K (v t') (s t') := by
    intro t' ht'
    have ht'_icc : t' ∈ Set.Icc c d := Set.mem_Icc.mpr ⟨by
      have := ht'.1; linarith, by
      have := ht'.2; linarith⟩
    have h_bound : |a t'| ≤ (K : ℝ) := hK t' ht'_icc
    have h_smul : LipschitzWith (‖a t'‖₊) (fun (y : ℝ) => (a t') • y) := lipschitzWith_smul (a t')
    have h_smul' : LipschitzWith (⟨|a t'|, abs_nonneg _⟩ : NNReal) (fun (y : ℝ) => a t' * y) := by
      simpa using h_smul
    have h_lip : LipschitzOnWith (⟨|a t'|, abs_nonneg _⟩ : NNReal) (fun (y : ℝ) => a t' * y) Set.univ :=
      h_smul'.lipschitzOnWith
    have hK_le : (⟨|a t'|, abs_nonneg _⟩ : NNReal) ≤ K := by
      exact_mod_cast h_bound
    exact h_lip.mono_const hK_le
  have hf' : ∀ t ∈ Set.Ioo c d, HasDerivAt f (v t (f t)) t ∧ f t ∈ s t := by
    intro t ht
    refine ⟨hf t ht, trivial⟩
  have hzero : ∀ t ∈ Set.Ioo c d, HasDerivAt (fun _ : ℝ => (0 : ℝ)) (v t ((fun _ : ℝ => (0 : ℝ)) t)) t ∧ (fun _ : ℝ => (0 : ℝ)) t ∈ s t := by
    intro t ht
    refine ⟨by
      have h_deriv : HasDerivAt (fun (_ : ℝ) => (0 : ℝ)) (0 : ℝ) t := hasDerivAt_const _ _
      simpa [hv_def, hs_def] using h_deriv, trivial⟩
  have h_unique : EqOn f (fun _ : ℝ => (0 : ℝ)) (Set.Ioo c d) :=
    ODE_solution_unique_of_mem_Ioo hv_lip ht₂ hf' hzero hf_t₂
  exact h_unique ht₁

lemma exists_open_interval_containing_two_points (J : Set ℝ) (hJ_open : IsOpen J) (hJ_conn : IsPreconnected J) (x y : ℝ) (hx : x ∈ J) (hy : y ∈ J) (hxy : x ≠ y) : 
    ∃ (c d : ℝ), c < d ∧ Set.Icc c d ⊆ J ∧ x ∈ Set.Ioo c d ∧ y ∈ Set.Ioo c d := by
  have hx_nh : ∃ ε > 0, Set.Ioo (x - ε) (x + ε) ⊆ J := by
    have h := hJ_open.mem_nhds hx
    rcases Metric.mem_nhds_iff.mp h with ⟨ε, hε, hball⟩
    refine ⟨ε, hε, ?_⟩
    intro z hz
    apply hball
    rw [Metric.mem_ball, Real.dist_eq]
    rcases hz with ⟨hz1, hz2⟩
    have : |z - x| < ε := by
      rw [abs_lt]
      constructor <;> linarith
    exact this
  have hy_nh : ∃ ε > 0, Set.Ioo (y - ε) (y + ε) ⊆ J := by
    have h := hJ_open.mem_nhds hy
    rcases Metric.mem_nhds_iff.mp h with ⟨ε, hε, hball⟩
    refine ⟨ε, hε, ?_⟩
    intro z hz
    apply hball
    rw [Metric.mem_ball, Real.dist_eq]
    rcases hz with ⟨hz1, hz2⟩
    have : |z - y| < ε := by
      rw [abs_lt]
      constructor <;> linarith
    exact this
  rcases hx_nh with ⟨ε₀, hε₀, hx_ball⟩
  rcases hy_nh with ⟨ε₁, hε₁, hy_ball⟩
  let δ := min ε₀ ε₁
  have hδ_pos : δ > 0 := by exact lt_min_iff.mpr ⟨hε₀, hε₁⟩
  have hδ_le_ε₀ : δ ≤ ε₀ := min_le_left _ _
  have hδ_le_ε₁ : δ ≤ ε₁ := min_le_right _ _
  have hJ_ord : J.OrdConnected := isPreconnected_iff_ordConnected.mp hJ_conn
  let c' := min x y - δ
  let d' := max x y + δ
  let c := min x y - δ / 2
  let d := max x y + δ / 2
  have h_min_lt_max : min x y < max x y := by
    by_cases hx_le_y : x ≤ y
    · have hmin : min x y = x := min_eq_left hx_le_y
      have hmax : max x y = y := max_eq_right hx_le_y
      rw [hmin, hmax]
      by_contra! hle
      exact hxy (by linarith)
    · have hy_le_x : y ≤ x := by linarith
      have hmin : min x y = y := min_eq_right hy_le_x
      have hmax : max x y = x := max_eq_left hy_le_x
      rw [hmin, hmax]
      by_contra! hle
      exact hxy (by linarith)
  have hcd : c < d := by
    dsimp [c, d]
    nlinarith
  have hIoo_c'd'_sub_J : Set.Ioo c' d' ⊆ J := by
    intro z hz
    rcases hz with ⟨hcz, hzd⟩
    dsimp [c', d'] at hcz hzd
    by_cases hz_ge_min : min x y ≤ z
    · by_cases hz_le_max : z ≤ max x y
      · have hz_icc : z ∈ Set.Icc (min x y) (max x y) := Set.mem_Icc.mpr ⟨hz_ge_min, hz_le_max⟩
        have hIcc_sub_J' : Set.Icc (min x y) (max x y) ⊆ J := by
          by_cases hxy' : x ≤ y
          · have hmin_eq : min x y = x := min_eq_left hxy'
            have hmax_eq : max x y = y := max_eq_right hxy'
            rw [hmin_eq, hmax_eq]
            exact hJ_ord.out hx hy
          · have hmin_eq : min x y = y := min_eq_right (by linarith)
            have hmax_eq : max x y = x := max_eq_left (by linarith)
            rw [hmin_eq, hmax_eq]
            exact hJ_ord.out hy hx
        exact hIcc_sub_J' hz_icc
      · by_cases hx_max : x ≤ y
        · have hmax_eq : max x y = y := max_eq_right hx_max
          rw [hmax_eq] at hzd
          have hy_lt_z : y < z := by linarith
          have hz_lt_y_ε₁ : z < y + ε₁ := by nlinarith
          exact hy_ball ⟨by nlinarith, hz_lt_y_ε₁⟩
        · have hmax_eq : max x y = x := max_eq_left (by linarith)
          rw [hmax_eq] at hzd
          have hx_lt_z : x < z := by linarith
          have hz_lt_x_ε₀ : z < x + ε₀ := by nlinarith
          exact hx_ball ⟨by nlinarith, hz_lt_x_ε₀⟩
    · by_cases hx_min : x ≤ y
      · have hmin_eq : min x y = x := min_eq_left hx_min
        rw [hmin_eq] at hcz
        have hz_lt_x : z < x := by linarith
        have hx_ε₀_lt_z : x - ε₀ < z := by nlinarith
        exact hx_ball ⟨hx_ε₀_lt_z, by nlinarith⟩
      · have hmin_eq : min x y = y := min_eq_right (by linarith)
        rw [hmin_eq] at hcz
        have hz_lt_y : z < y := by linarith
        have hy_ε₁_lt_z : y - ε₁ < z := by nlinarith
        exact hy_ball ⟨hy_ε₁_lt_z, by nlinarith⟩
  have hIcc_sub_J : Set.Icc c d ⊆ J := by
    intro z hz
    rcases hz with ⟨hcz, hzd⟩
    dsimp [c, d] at hcz hzd
    have hcz' : c' < z := by
      dsimp [c']
      nlinarith
    have hzd' : z < d' := by
      dsimp [d']
      nlinarith
    exact hIoo_c'd'_sub_J ⟨hcz', hzd'⟩
  have hx_mem : x ∈ Set.Ioo c d := by
    dsimp [c, d]
    have hx_low : min x y - δ / 2 < x := by
      have : min x y ≤ x := min_le_left _ _
      nlinarith
    have hx_high : x < max x y + δ / 2 := by
      have : x ≤ max x y := le_max_left _ _
      nlinarith
    exact ⟨hx_low, hx_high⟩
  have hy_mem : y ∈ Set.Ioo c d := by
    dsimp [c, d]
    have hy_low : min x y - δ / 2 < y := by
      have : min x y ≤ y := min_le_right _ _
      nlinarith
    have hy_high : y < max x y + δ / 2 := by
      have : y ≤ max x y := le_max_right _ _
      nlinarith
    exact ⟨hy_low, hy_high⟩
  exact ⟨c, d, hcd, hIcc_sub_J, hx_mem, hy_mem⟩

lemma deriv_nonneg_at_right (f : ℝ → ℝ) (a : ℝ) (hf : HasDerivAt f (deriv f a) a) (hfa : f a = 0)
    (hpos : ∀ᶠ x in nhdsWithin a (Set.Ioi a), f x > 0) : deriv f a ≥ 0 := by
  have h_slope_nonneg : ∀ᶠ x in nhdsWithin a (Set.Ioi a), 0 ≤ slope f a x := by
    filter_upwards [hpos, self_mem_nhdsWithin] with x hxpos hxmem
    dsimp [slope]
    rw [hfa, sub_zero]
    have hxpos' : x > a := hxmem
    have : 0 ≤ f x / (x - a) := div_nonneg (by linarith) (by linarith)
    simpa [div_eq_inv_mul] using this
  have h_nhdsWithin_sub : nhdsWithin a (Set.Ioi a) ≤ nhdsWithin a {x | x ≠ a} :=
    nhdsWithin_mono _ (by
      intro x hx
      exact Set.mem_setOf.mpr (ne_of_gt hx))
  have h_slope_tendsto : Tendsto (slope f a) (nhdsWithin a (Set.Ioi a)) (nhds (deriv f a)) :=
    hf.tendsto_slope.mono_left h_nhdsWithin_sub
  exact ge_of_tendsto h_slope_tendsto h_slope_nonneg

lemma deriv_nonpos_at_left (f : ℝ → ℝ) (b : ℝ) (hf : HasDerivAt f (deriv f b) b) (hfb : f b = 0)
    (hpos : ∀ᶠ x in nhdsWithin b (Set.Iio b), f x > 0) : deriv f b ≤ 0 := by
  have h_slope_nonpos : ∀ᶠ x in nhdsWithin b (Set.Iio b), slope f b x ≤ 0 := by
    filter_upwards [hpos, self_mem_nhdsWithin] with x hxpos hxmem
    dsimp [slope]
    rw [hfb, sub_zero]
    have hxpos' : x < b := hxmem
    have : f x / (x - b) ≤ 0 := div_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
    simpa [div_eq_inv_mul] using this
  have h_nhdsWithin_sub : nhdsWithin b (Set.Iio b) ≤ nhdsWithin b {x | x ≠ b} :=
    nhdsWithin_mono _ (by
      intro x hx
      exact Set.mem_setOf.mpr (ne_of_lt hx))
  have h_slope_tendsto : Tendsto (slope f b) (nhdsWithin b (Set.Iio b)) (nhds (deriv f b)) :=
    hf.tendsto_slope.mono_left h_nhdsWithin_sub
  exact le_of_tendsto h_slope_tendsto h_slope_nonpos

lemma Ioo_mem_nhdsWithin_Ioi (a b : ℝ) (hab : a < b) : Set.Ioo a b ∈ nhdsWithin a (Set.Ioi a) := by
  rw [Metric.mem_nhdsWithin_iff]
  refine ⟨b - a, by linarith, ?_⟩
  intro x hx
  rcases hx with ⟨hx1, hx2⟩
  rw [Metric.mem_ball, Real.dist_eq] at hx1
  rcases abs_lt.mp hx1 with ⟨hx_low, hx_high⟩
  have hx_lt_b : x < b := by nlinarith
  exact ⟨hx2, hx_lt_b⟩

lemma Ioo_mem_nhdsWithin_Iio (a b : ℝ) (hab : a < b) : Set.Ioo a b ∈ nhdsWithin b (Set.Iio b) := by
  rw [Metric.mem_nhdsWithin_iff]
  refine ⟨b - a, by linarith, ?_⟩
  intro x hx
  rcases hx with ⟨hx1, hx2⟩
  rw [Metric.mem_ball, Real.dist_eq] at hx1
  rcases abs_lt.mp hx1 with ⟨hx_low, hx_high⟩
  have hx_gt_a : a < x := by nlinarith
  exact ⟨hx_gt_a, hx2⟩

lemma const_sign_of_continuous_nonzero (f : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b) (hf : ContinuousOn f (Set.Icc a b))
    (hf0 : ∀ x ∈ Set.Icc a b, f x ≠ 0) : (∀ x ∈ Set.Icc a b, f x > 0) ∨ (∀ x ∈ Set.Icc a b, f x < 0) := by
  by_cases h_pos : ∃ x ∈ Set.Icc a b, f x > 0
  · rcases h_pos with ⟨x, hx, hx_pos⟩
    have h_all_pos : ∀ y ∈ Set.Icc a b, f y > 0 := by
      intro y hy
      by_contra! hle
      have hy_neg_or_zero : f y < 0 ∨ f y = 0 := lt_or_eq_of_le hle
      rcases hy_neg_or_zero with (hy_neg | hy_zero)
      · have hxy : x ≠ y := by
          intro h_eq; have : f x = f y := by simpa [h_eq]; nlinarith
        rcases lt_or_gt_of_ne hxy with (hx_lt_y | hy_lt_x)
        · have h_cont_xy : ContinuousOn f (Set.Icc x y) :=
            hf.mono (Set.Icc_subset_Icc (by exact hx.1) (by exact hy.2))
          have h_IVT : Set.Icc (f y) (f x) ⊆ f '' Set.Icc x y :=
            intermediate_value_Icc' (by linarith) h_cont_xy
          have h0_mem : (0 : ℝ) ∈ Set.Icc (f y) (f x) := ⟨by linarith, by linarith⟩
          rcases h_IVT h0_mem with ⟨z, hz, hz0⟩
          have hz_icc : z ∈ Set.Icc a b := Set.mem_Icc.mpr ⟨by
            have : a ≤ x := hx.1; have : x ≤ z := hz.1; linarith, by
            have : z ≤ y := hz.2; have : y ≤ b := hy.2; linarith⟩
          exact hf0 z hz_icc hz0
        · have h_cont_xy : ContinuousOn f (Set.Icc y x) :=
            hf.mono (Set.Icc_subset_Icc (by exact hy.1) (by exact hx.2))
          have h_IVT : Set.Icc (f y) (f x) ⊆ f '' Set.Icc y x :=
            intermediate_value_Icc (by linarith) h_cont_xy
          have h0_mem : (0 : ℝ) ∈ Set.Icc (f y) (f x) := ⟨by linarith, by linarith⟩
          rcases h_IVT h0_mem with ⟨z, hz, hz0⟩
          have hz_icc : z ∈ Set.Icc a b := Set.mem_Icc.mpr ⟨by
            have : a ≤ y := hy.1; have : y ≤ z := hz.1; linarith, by
            have : z ≤ x := hz.2; have : x ≤ b := hx.2; linarith⟩
          exact hf0 z hz_icc hz0
      · exact hf0 y hy hy_zero
    exact Or.inl h_all_pos
  · have h_all_neg : ∀ y ∈ Set.Icc a b, f y < 0 := by
      intro y hy
      by_contra! hge
      have hy_nonpos : f y ≤ 0 := by
        by_contra! hgt; exact h_pos ⟨y, hy, hgt⟩
      have : f y = 0 := by linarith
      exact hf0 y hy this
    exact Or.inr h_all_neg

lemma constant_sign_on_Ioo (y₁ : ℝ → ℝ) (a b : ℝ) (hab : a < b) (hne : ∀ x ∈ Set.Ioo a b, y₁ x ≠ 0)
    (h_cont : ContinuousOn y₁ (Set.Ioo a b)) : (∀ x ∈ Set.Ioo a b, y₁ x > 0) ∨ (∀ x ∈ Set.Ioo a b, y₁ x < 0) := by
  by_cases h_pos : ∃ x ∈ Set.Ioo a b, y₁ x > 0
  · rcases h_pos with ⟨x, hx, hx_pos⟩
    have h_all_pos : ∀ y ∈ Set.Ioo a b, y₁ y > 0 := by
      intro y hy
      by_contra! hle
      have hy_neg_or_zero : y₁ y < 0 ∨ y₁ y = 0 := lt_or_eq_of_le hle
      rcases hy_neg_or_zero with (hy_neg | hy_zero)
      · have hxy : x ≠ y := by
          intro h_eq; have hy_pos : y₁ y > 0 := by simpa [h_eq] using hx_pos; linarith
        rcases lt_or_gt_of_ne hxy with (hx_lt_y | hy_lt_x)
        · have h_cont_xy : ContinuousOn y₁ (Set.Icc x y) :=
            h_cont.mono (Set.Icc_subset_Ioo (by exact hx.1) (by exact hy.2))
          have h_IVT : Set.Icc (y₁ y) (y₁ x) ⊆ y₁ '' Set.Icc x y :=
            intermediate_value_Icc' (by linarith) h_cont_xy
          have h0_mem : (0 : ℝ) ∈ Set.Icc (y₁ y) (y₁ x) := ⟨by linarith, by linarith⟩
          rcases h_IVT h0_mem with ⟨z, hz, hz0⟩
          have hz_Ioo : z ∈ Set.Ioo a b := ⟨by
            have : a < x := hx.1; have : x ≤ z := hz.1; linarith, by
            have : z ≤ y := hz.2; have : y < b := hy.2; linarith⟩
          exact hne z hz_Ioo hz0
        · have h_cont_xy : ContinuousOn y₁ (Set.Icc y x) :=
            h_cont.mono (Set.Icc_subset_Ioo (by exact hy.1) (by exact hx.2))
          have h_IVT : Set.Icc (y₁ y) (y₁ x) ⊆ y₁ '' Set.Icc y x :=
            intermediate_value_Icc (by linarith) h_cont_xy
          have h0_mem : (0 : ℝ) ∈ Set.Icc (y₁ y) (y₁ x) := ⟨by linarith, by linarith⟩
          rcases h_IVT h0_mem with ⟨z, hz, hz0⟩
          have hz_Ioo : z ∈ Set.Ioo a b := ⟨by
            have : a < y := hy.1; have : y ≤ z := hz.1; linarith, by
            have : z ≤ x := hz.2; have : x < b := hx.2; linarith⟩
          exact hne z hz_Ioo hz0
      · exact hne y hy hy_zero
    exact Or.inl h_all_pos
  · have h_all_neg : ∀ y ∈ Set.Ioo a b, y₁ y < 0 := by
      intro y hy
      by_contra! hge
      have hy_nonpos : y₁ y ≤ 0 := by
        by_contra! hgt; exact h_pos ⟨y, hy, hgt⟩
      have : y₁ y = 0 := by linarith
      exact hne y hy this
    exact Or.inr h_all_neg

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

lemma deriv_ratio_eq_wronskian_div_sq (y₁ y₂ : ℝ → ℝ) (x : ℝ) (hy₁ : HasDerivAt y₁ (deriv y₁ x) x) 
    (hy₂ : HasDerivAt y₂ (deriv y₂ x) x) (hy1x_ne : y₁ x ≠ 0) :
    deriv (fun t : ℝ => y₂ t / y₁ t) x = (wronskian y₁ y₂ x) / (y₁ x)^2 := by
  have h := (HasDerivAt.div hy₂ hy₁ hy1x_ne).deriv
  dsimp [wronskian] at h ⊢
  simpa [mul_comm] using h

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
  have hW0' : wronskian y₁ y₂ x₀ ≠ 0 := by
    dsimp [wronskian]; exact hW0
  have haJ : a ∈ J := hJ_sub (Set.mem_Icc.mpr ⟨by linarith, by linarith⟩)
  have hbJ : b ∈ J := hJ_sub (Set.mem_Icc.mpr ⟨by linarith, by linarith⟩)
  have hIoo_J : Set.Ioo a b ⊆ J := by
    intro x hx; rcases hx with ⟨hax, hxb⟩
    have hx' : x ∈ Set.Icc a b := Set.mem_Icc.mpr ⟨by linarith, by linarith⟩
    exact hJ_sub hx'
  have hJ_ord : J.OrdConnected := isPreconnected_iff_ordConnected.mp hJ_conn

  -- The Wronskian never vanishes on [a,b].
  have hW_nonzero : ∀ x ∈ Set.Icc a b, wronskian y₁ y₂ x ≠ 0 := by
    intro x hx
    have hxJ : x ∈ J := hJ_sub hx
    by_cases h_eq : x₀ = x
    · subst h_eq; exact hW0'
    by_cases hzero : wronskian y₁ y₂ x = 0
    · exfalso
      rcases exists_open_interval_containing_two_points J hJ_open hJ_conn x₀ x hx₀J hxJ h_eq with ⟨c, d, hcd, hIcc_sub_J, hx₀_mem, hx_mem⟩
      have hW_deriv : ∀ t ∈ Set.Ioo c d, HasDerivAt (wronskian y₁ y₂) ((-p t) * (wronskian y₁ y₂ t)) t := by
        intro t ht
        have htJ : t ∈ J := hIcc_sub_J (Set.mem_Icc.mpr ⟨by
          have := ht.1; linarith, by
          have := ht.2; linarith⟩)
        have h := wronskian_deriv p q y₁ y₂ t (hy₁ t htJ) (hy₁' t htJ) (hy₂ t htJ) (hy₂' t htJ)
        simpa [mul_comm, mul_left_comm, mul_assoc, neg_mul] using h
      have ha_cont : ContinuousOn (fun t : ℝ => -p t) (Set.Icc c d) :=
        (hp.mono hIcc_sub_J).neg
      have hW_x₀_zero : wronskian y₁ y₂ x₀ = 0 :=
        linear_ode_zero_at_point (fun t => -p t) (wronskian y₁ y₂) c d hcd x₀ x hx₀_mem hx_mem ha_cont hW_deriv hzero
      exact hW0' hW_x₀_zero
    · exact hzero

  -- Step 3: y₂(a) ≠ 0 and y₂(b) ≠ 0.
  have hy₂a_ne_zero : y₂ a ≠ 0 := by
    intro h; have : wronskian y₁ y₂ a = 0 := by
      dsimp [wronskian]; simp [hza, h]
    exact hW_nonzero a (Set.mem_Icc.mpr ⟨by linarith, by linarith⟩) this
  have hy₂b_ne_zero : y₂ b ≠ 0 := by
    intro h; have : wronskian y₁ y₂ b = 0 := by
      dsimp [wronskian]; simp [hzb, h]
    exact hW_nonzero b (Set.mem_Icc.mpr ⟨by linarith, by linarith⟩) this

  -- Step 4-5: at most one zero of y₂ in (a,b)
  have at_most_one : ∀ c ∈ Set.Ioo a b, ∀ d ∈ Set.Ioo a b, y₂ c = 0 → y₂ d = 0 → c = d := by
    intro c hc d hd hc0 hd0
    by_contra! hne_cd
    rcases lt_or_gt_of_ne hne_cd with (hlt | hgt)
    · -- c < d
      have h_ratio_eq : (fun x : ℝ => y₂ x / y₁ x) c = (fun x : ℝ => y₂ x / y₁ x) d := by
        simp [hc0, hd0]
      have hy1_ne : ∀ x ∈ Set.Icc c d, y₁ x ≠ 0 := by
        intro x hx; have hxIoo : x ∈ Set.Ioo a b := ⟨by
          have := hc.1; have := hx.1; linarith, by
          have := hd.2; have := hx.2; linarith⟩
        exact hne x hxIoo
      have h_cont : ContinuousOn (fun x : ℝ => y₂ x / y₁ x) (Set.Icc c d) := by
        refine ContinuousOn.div ?_ ?_ hy1_ne
        · intro x hx; have hxJ : x ∈ J := hIoo_J ⟨by
            have := hc.1; have := hx.1; linarith, by
            have := hd.2; have := hx.2; linarith⟩
          exact (hy₂ x hxJ).continuousAt.continuousWithinAt
        · intro x hx; have hxJ : x ∈ J := hIoo_J ⟨by
            have := hc.1; have := hx.1; linarith, by
            have := hd.2; have := hx.2; linarith⟩
          exact (hy₁ x hxJ).continuousAt.continuousWithinAt
      rcases exists_deriv_eq_zero hlt h_cont h_ratio_eq with ⟨ξ, hξ, hderiv⟩
      have hξJ : ξ ∈ J := hIoo_J ⟨by
        have := hc.1; have := hξ.1; linarith, by
        have := hd.2; have := hξ.2; linarith⟩
      have hy1ξ_ne : y₁ ξ ≠ 0 := hne ξ ⟨by
        have := hc.1; have := hξ.1; linarith, by
        have := hd.2; have := hξ.2; linarith⟩
      have hW_ξ_ne_zero : wronskian y₁ y₂ ξ ≠ 0 := by
        apply hW_nonzero ξ; refine Set.mem_Icc.mpr ⟨by
          have := hc.1; have := hξ.1; linarith, by
          have := hd.2; have := hξ.2; linarith⟩
      have h_deriv_ratio_eq : deriv (fun x : ℝ => y₂ x / y₁ x) ξ = (wronskian y₁ y₂ ξ) / (y₁ ξ)^2 :=
        deriv_ratio_eq_wronskian_div_sq y₁ y₂ ξ (hy₁ ξ hξJ) (hy₂ ξ hξJ) hy1ξ_ne
      rw [h_deriv_ratio_eq] at hderiv
      have : (wronskian y₁ y₂ ξ) / (y₁ ξ)^2 ≠ 0 := div_ne_zero hW_ξ_ne_zero (by positivity)
      exact this hderiv
    · -- d < c, symmetric
      have h_ratio_eq : (fun x : ℝ => y₂ x / y₁ x) d = (fun x : ℝ => y₂ x / y₁ x) c := by
        simp [hc0, hd0]
      have hy1_ne : ∀ x ∈ Set.Icc d c, y₁ x ≠ 0 := by
        intro x hx; have hxIoo : x ∈ Set.Ioo a b := ⟨by
          have := hd.1; have := hx.1; linarith, by
          have := hc.2; have := hx.2; linarith⟩
        exact hne x hxIoo
      have h_cont : ContinuousOn (fun x : ℝ => y₂ x / y₁ x) (Set.Icc d c) := by
        refine ContinuousOn.div ?_ ?_ hy1_ne
        · intro x hx; have hxJ : x ∈ J := hIoo_J ⟨by
            have := hd.1; have := hx.1; linarith, by
            have := hc.2; have := hx.2; linarith⟩
          exact (hy₂ x hxJ).continuousAt.continuousWithinAt
        · intro x hx; have hxJ : x ∈ J := hIoo_J ⟨by
            have := hd.1; have := hx.1; linarith, by
            have := hc.2; have := hx.2; linarith⟩
          exact (hy₁ x hxJ).continuousAt.continuousWithinAt
      rcases exists_deriv_eq_zero hgt h_cont h_ratio_eq with ⟨ξ, hξ, hderiv⟩
      have hξJ : ξ ∈ J := hIoo_J ⟨by
        have := hd.1; have := hξ.1; linarith, by
        have := hc.2; have := hξ.2; linarith⟩
      have hy1ξ_ne : y₁ ξ ≠ 0 := hne ξ ⟨by
        have := hd.1; have := hξ.1; linarith, by
        have := hc.2; have := hξ.2; linarith⟩
      have hW_ξ_ne_zero : wronskian y₁ y₂ ξ ≠ 0 := by
        apply hW_nonzero ξ; refine Set.mem_Icc.mpr ⟨by
          have := hd.1; have := hξ.1; linarith, by
          have := hc.2; have := hξ.2; linarith⟩
      have h_deriv_ratio_eq : deriv (fun x : ℝ => y₂ x / y₁ x) ξ = (wronskian y₁ y₂ ξ) / (y₁ ξ)^2 :=
        deriv_ratio_eq_wronskian_div_sq y₁ y₂ ξ (hy₁ ξ hξJ) (hy₂ ξ hξJ) hy1ξ_ne
      rw [h_deriv_ratio_eq] at hderiv
      have : (wronskian y₁ y₂ ξ) / (y₁ ξ)^2 ≠ 0 := div_ne_zero hW_ξ_ne_zero (by positivity)
      exact this hderiv

  -- Step 6: Existence of a zero of y₂ in (a,b)
  have at_least_one : ∃ c ∈ Set.Ioo a b, y₂ c = 0 := by
    have hy1_cont : ContinuousOn y₁ (Set.Ioo a b) := by
      intro x hx; have hxJ : x ∈ J := hIoo_J hx; exact (hy₁ x hxJ).continuousAt.continuousWithinAt
    have hy1_const_sign := constant_sign_on_Ioo y₁ a b hab hne hy1_cont
    rcases hy1_const_sign with (hy1_pos | hy1_neg)
    · -- Case y₁ > 0 on (a,b)
      have h_nhds_pos_a : ∀ᶠ x in nhdsWithin a (Set.Ioi a), y₁ x > 0 := by
        have h_mem : Set.Ioo a ((a + b) / 2) ∈ nhdsWithin a (Set.Ioi a) :=
          Ioo_mem_nhdsWithin_Ioi a ((a + b) / 2) (by nlinarith)
        filter_upwards [h_mem] with x hx; apply hy1_pos x; exact ⟨hx.1, by nlinarith⟩
      have h_deriv_a_nonneg : deriv y₁ a ≥ 0 :=
        deriv_nonneg_at_right y₁ a (hy₁ a haJ) hza h_nhds_pos_a
      have h_deriv_a_pos : deriv y₁ a > 0 := by
        by_contra! hle
        have : deriv y₁ a = 0 := by linarith
        have : wronskian y₁ y₂ a = 0 := by dsimp [wronskian]; simp [hza, this]
        exact hW_nonzero a (Set.mem_Icc.mpr ⟨by linarith, by linarith⟩) this
      have h_nhds_pos_b : ∀ᶠ x in nhdsWithin b (Set.Iio b), y₁ x > 0 := by
        have h_mem : Set.Ioo ((a + b) / 2) b ∈ nhdsWithin b (Set.Iio b) :=
          Ioo_mem_nhdsWithin_Iio ((a + b) / 2) b (by nlinarith)
        filter_upwards [h_mem] with x hx; apply hy1_pos x; exact ⟨by nlinarith, hx.2⟩
      have h_deriv_b_nonpos : deriv y₁ b ≤ 0 :=
        deriv_nonpos_at_left y₁ b (hy₁ b hbJ) hzb h_nhds_pos_b
      have h_deriv_b_neg : deriv y₁ b < 0 := by
        by_contra! hge
        have : deriv y₁ b = 0 := by linarith
        have : wronskian y₁ y₂ b = 0 := by dsimp [wronskian]; simp [hzb, this]
        exact hW_nonzero b (Set.mem_Icc.mpr ⟨by linarith, by linarith⟩) this
      -- W has constant sign on [a,b]
      have hW_cont : ContinuousOn (wronskian y₁ y₂) (Set.Icc a b) := by
        intro x hx; have hxJ : x ∈ J := hJ_sub hx
        have hW_deriv_x := wronskian_deriv p q y₁ y₂ x (hy₁ x hxJ) (hy₁' x hxJ) (hy₂ x hxJ) (hy₂' x hxJ)
        exact hW_deriv_x.continuousAt.continuousWithinAt
      have hW_const_sign : (∀ x ∈ Set.Icc a b, wronskian y₁ y₂ x > 0) ∨ (∀ x ∈ Set.Icc a b, wronskian y₁ y₂ x < 0) :=
        const_sign_of_continuous_nonzero (wronskian y₁ y₂) a b (by linarith) hW_cont hW_nonzero
      rcases hW_const_sign with (hW_pos | hW_neg)
      · -- W > 0
        have hy2a_neg : y₂ a < 0 := by
          have : wronskian y₁ y₂ a = -y₂ a * deriv y₁ a := by dsimp [wronskian]; simp [hza]
          have hW_a_pos : wronskian y₁ y₂ a > 0 := hW_pos a (Set.mem_Icc.mpr ⟨by linarith, by linarith⟩)
          rw [this] at hW_a_pos; nlinarith
        have hy2b_pos : y₂ b > 0 := by
          have : wronskian y₁ y₂ b = -y₂ b * deriv y₁ b := by dsimp [wronskian]; simp [hzb]
          have hW_b_pos : wronskian y₁ y₂ b > 0 := hW_pos b (Set.mem_Icc.mpr ⟨by linarith, by linarith⟩)
          rw [this] at hW_b_pos; nlinarith
        have h_cont_y2 : ContinuousOn y₂ (Set.Icc a b) := by
          intro x hx; have hxJ : x ∈ J := hJ_sub hx; exact (hy₂ x hxJ).continuousAt.continuousWithinAt
        have h0_mem : (0 : ℝ) ∈ Set.Ioo (y₂ a) (y₂ b) := ⟨hy2a_neg, hy2b_pos⟩
        have h_IVT : Set.Ioo (y₂ a) (y₂ b) ⊆ y₂ '' Set.Ioo a b := intermediate_value_Ioo (by linarith) h_cont_y2
        rcases h_IVT h0_mem with ⟨c, hc, hc0⟩; exact ⟨c, hc, hc0⟩
      · -- W < 0
        have hy2a_pos : y₂ a > 0 := by
          have : wronskian y₁ y₂ a = -y₂ a * deriv y₁ a := by dsimp [wronskian]; simp [hza]
          have hW_a_neg : wronskian y₁ y₂ a < 0 := hW_neg a (Set.mem_Icc.mpr ⟨by linarith, by linarith⟩)
          rw [this] at hW_a_neg; nlinarith
        have hy2b_neg : y₂ b < 0 := by
          have : wronskian y₁ y₂ b = -y₂ b * deriv y₁ b := by dsimp [wronskian]; simp [hzb]
          have hW_b_neg : wronskian y₁ y₂ b < 0 := hW_neg b (Set.mem_Icc.mpr ⟨by linarith, by linarith⟩)
          rw [this] at hW_b_neg; nlinarith
        have h_cont_y2 : ContinuousOn y₂ (Set.Icc a b) := by
          intro x hx; have hxJ : x ∈ J := hJ_sub hx; exact (hy₂ x hxJ).continuousAt.continuousWithinAt
        have h0_mem : (0 : ℝ) ∈ Set.Ioo (y₂ b) (y₂ a) := ⟨hy2b_neg, hy2a_pos⟩
        have h_IVT : Set.Ioo (y₂ b) (y₂ a) ⊆ y₂ '' Set.Ioo a b := intermediate_value_Ioo (by linarith) h_cont_y2
        rcases h_IVT h0_mem with ⟨c, hc, hc0⟩; exact ⟨c, hc, hc0⟩
    · -- Case y₁ < 0 on (a,b): apply the symmetric argument (negate y₁)
      have hy1_neg' : ∀ x ∈ Set.Ioo a b, (-y₁) x > 0 := by
        intro x hx; have : y₁ x < 0 := hy1_neg x hx; linarith
      have h_deriv_neg_a : deriv (-y₁) a = -deriv y₁ a := deriv_neg (y₁) a
      have h_deriv_neg_b : deriv (-y₁) b = -deriv y₁ b := deriv_neg (y₁) b
      -- Apply the y₁ > 0 case to -y₁
      have h_nhds_pos_a : ∀ᶠ x in nhdsWithin a (Set.Ioi a), (-y₁) x > 0 := by
        have h_mem : Set.Ioo a ((a + b) / 2) ∈ nhdsWithin a (Set.Ioi a) :=
          Ioo_mem_nhdsWithin_Ioi a ((a + b) / 2) (by nlinarith)
        filter_upwards [h_mem] with x hx; apply hy1_neg' x; exact ⟨hx.1, by nlinarith⟩
      -- For -y₁: HasDerivAt at a
      have h_neg_y1_a : HasDerivAt (-y₁) (deriv (-y₁) a) a := by
        have := hy₁ a haJ
        simpa using HasDerivAt.neg this
      have h_deriv_neg_a_nonneg : deriv (-y₁) a ≥ 0 :=
        deriv_nonneg_at_right (-y₁) a h_neg_y1_a (by simp [hza]) h_nhds_pos_a
      have h_deriv_a_neg : deriv y₁ a < 0 := by
        rw [h_deriv_neg_a] at h_deriv_neg_a_nonneg
        have : deriv y₁ a ≠ 0 := by
          intro hzero
          have : wronskian y₁ y₂ a = 0 := by dsimp [wronskian]; simp [hza, hzero]
          exact hW_nonzero a (Set.mem_Icc.mpr ⟨by linarith, by linarith⟩) this
        nlinarith
      have h_nhds_pos_b : ∀ᶠ x in nhdsWithin b (Set.Iio b), (-y₁) x > 0 := by
        have h_mem : Set.Ioo ((a + b) / 2) b ∈ nhdsWithin b (Set.Iio b) :=
          Ioo_mem_nhdsWithin_Iio ((a + b) / 2) b (by nlinarith)
        filter_upwards [h_mem] with x hx; apply hy1_neg' x; exact ⟨by nlinarith, hx.2⟩
      have h_neg_y1_b : HasDerivAt (-y₁) (deriv (-y₁) b) b := by
        have := hy₁ b hbJ
        simpa using HasDerivAt.neg this
      have h_deriv_neg_b_nonpos : deriv (-y₁) b ≤ 0 :=
        deriv_nonpos_at_left (-y₁) b h_neg_y1_b (by simp [hzb]) h_nhds_pos_b
      have h_deriv_b_pos : deriv y₁ b > 0 := by
        rw [h_deriv_neg_b] at h_deriv_neg_b_nonpos
        have : deriv y₁ b ≠ 0 := by
          intro hzero
          have : wronskian y₁ y₂ b = 0 := by dsimp [wronskian]; simp [hzb, hzero]
          exact hW_nonzero b (Set.mem_Icc.mpr ⟨by linarith, by linarith⟩) this
        nlinarith
      -- W has constant sign (same as before)
      have hW_cont : ContinuousOn (wronskian y₁ y₂) (Set.Icc a b) := by
        intro x hx; have hxJ : x ∈ J := hJ_sub hx
        have hW_deriv_x := wronskian_deriv p q y₁ y₂ x (hy₁ x hxJ) (hy₁' x hxJ) (hy₂ x hxJ) (hy₂' x hxJ)
        exact hW_deriv_x.continuousAt.continuousWithinAt
      have hW_const_sign : (∀ x ∈ Set.Icc a b, wronskian y₁ y₂ x > 0) ∨ (∀ x ∈ Set.Icc a b, wronskian y₁ y₂ x < 0) :=
        const_sign_of_continuous_nonzero (wronskian y₁ y₂) a b (by linarith) hW_cont hW_nonzero
      rcases hW_const_sign with (hW_pos | hW_neg)
      · -- W > 0: with deriv y₁ a < 0 and deriv y₁ b > 0, we get y₂ a > 0 and y₂ b < 0
        have hy2a_pos : y₂ a > 0 := by
          have : wronskian y₁ y₂ a = -y₂ a * deriv y₁ a := by dsimp [wronskian]; simp [hza]
          have hW_a_pos : wronskian y₁ y₂ a > 0 := hW_pos a (Set.mem_Icc.mpr ⟨by linarith, by linarith⟩)
          rw [this] at hW_a_pos; nlinarith
        have hy2b_neg : y₂ b < 0 := by
          have : wronskian y₁ y₂ b = -y₂ b * deriv y₁ b := by dsimp [wronskian]; simp [hzb]
          have hW_b_pos : wronskian y₁ y₂ b > 0 := hW_pos b (Set.mem_Icc.mpr ⟨by linarith, by linarith⟩)
          rw [this] at hW_b_pos; nlinarith
        have h_cont_y2 : ContinuousOn y₂ (Set.Icc a b) := by
          intro x hx; have hxJ : x ∈ J := hJ_sub hx; exact (hy₂ x hxJ).continuousAt.continuousWithinAt
        have h0_mem : (0 : ℝ) ∈ Set.Ioo (y₂ b) (y₂ a) := ⟨hy2b_neg, hy2a_pos⟩
        have h_IVT : Set.Ioo (y₂ b) (y₂ a) ⊆ y₂ '' Set.Ioo a b := intermediate_value_Ioo (by linarith) h_cont_y2
        rcases h_IVT h0_mem with ⟨c, hc, hc0⟩; exact ⟨c, hc, hc0⟩
      · -- W < 0: with deriv y₁ a < 0 and deriv y₁ b > 0, we get y₂ a < 0 and y₂ b > 0
        have hy2a_neg : y₂ a < 0 := by
          have : wronskian y₁ y₂ a = -y₂ a * deriv y₁ a := by dsimp [wronskian]; simp [hza]
          have hW_a_neg : wronskian y₁ y₂ a < 0 := hW_neg a (Set.mem_Icc.mpr ⟨by linarith, by linarith⟩)
          rw [this] at hW_a_neg; nlinarith
        have hy2b_pos : y₂ b > 0 := by
          have : wronskian y₁ y₂ b = -y₂ b * deriv y₁ b := by dsimp [wronskian]; simp [hzb]
          have hW_b_neg : wronskian y₁ y₂ b < 0 := hW_neg b (Set.mem_Icc.mpr ⟨by linarith, by linarith⟩)
          rw [this] at hW_b_neg; nlinarith
        have h_cont_y2 : ContinuousOn y₂ (Set.Icc a b) := by
          intro x hx; have hxJ : x ∈ J := hJ_sub hx; exact (hy₂ x hxJ).continuousAt.continuousWithinAt
        have h0_mem : (0 : ℝ) ∈ Set.Ioo (y₂ a) (y₂ b) := ⟨hy2a_neg, hy2b_pos⟩
        have h_IVT : Set.Ioo (y₂ a) (y₂ b) ⊆ y₂ '' Set.Ioo a b := intermediate_value_Ioo (by linarith) h_cont_y2
        rcases h_IVT h0_mem with ⟨c, hc, hc0⟩; exact ⟨c, hc, hc0⟩

  -- Combine existence and uniqueness
  rcases at_least_one with ⟨c, hc, hc0⟩
  refine ⟨c, ⟨hc, hc0⟩, ?_⟩
  intro d ⟨hd, hd0⟩
  exact (at_most_one c hc d hd hc0 hd0).symm

end Submission