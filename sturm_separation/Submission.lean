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

-- New lemmas for the main proof

lemma strictMonoOn_of_deriv_pos_on_Ioo (f f' : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hf : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x) (hf' : ∀ x ∈ Ioo a b, 0 < f' x) :
    StrictMonoOn f (Ioo a b) := by
  apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Ioo a b)
  · intro x hx; exact (hf x hx).continuousAt.continuousWithinAt
  · intro x hx
    have hx' : x ∈ Ioo a b := by simpa [interior_Ioo] using hx
    exact (hf x hx').hasDerivWithinAt
  · intro x hx
    have hx' : x ∈ Ioo a b := by simpa [interior_Ioo] using hx
    exact hf' x hx'

lemma strictAntiOn_of_deriv_neg_on_Ioo (f f' : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hf : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x) (hf' : ∀ x ∈ Ioo a b, f' x < 0) :
    StrictAntiOn f (Ioo a b) := by
  apply strictAntiOn_of_hasDerivWithinAt_neg (convex_Ioo a b)
  · intro x hx; exact (hf x hx).continuousAt.continuousWithinAt
  · intro x hx
    have hx' : x ∈ Ioo a b := by simpa [interior_Ioo] using hx
    exact (hf x hx').hasDerivWithinAt
  · intro x hx
    have hx' : x ∈ Ioo a b := by simpa [interior_Ioo] using hx
    exact hf' x hx'

lemma const_sign_on_Ioo (f : ℝ → ℝ) (a b : ℝ) (hab : a < b) (hf : ∀ x ∈ Ioo a b, ContinuousAt f x)
    (hf_nonzero : ∀ x ∈ Ioo a b, f x ≠ 0) : (∀ x ∈ Ioo a b, f x > 0) ∨ (∀ x ∈ Ioo a b, f x < 0) := by
  by_cases hpos : ∃ x ∈ Ioo a b, f x > 0
  · rcases hpos with ⟨x₁, hx₁, hpos⟩
    refine Or.inl ?_
    intro x hx
    by_cases hx_pos : f x > 0
    · exact hx_pos
    · have hx_nonpos : f x ≤ 0 := by linarith
      have hx_nonzero : f x ≠ 0 := hf_nonzero x hx
      have hx_neg : f x < 0 := by
        by_contra! hge
        have : f x = 0 := by nlinarith
        exact hx_nonzero this
      by_cases hxx₁ : x ≤ x₁
      · have hcont : ContinuousOn f (Icc x x₁) := by
          intro y hy
          have hy_Ioo : y ∈ Ioo a b := by
            have haz : a < y := lt_of_lt_of_le hx.1 hy.1
            have hzb : y < b := lt_of_le_of_lt hy.2 hx₁.2
            exact ⟨haz, hzb⟩
          exact (hf y hy_Ioo).continuousWithinAt
        have hzero_mem : (0 : ℝ) ∈ Ioo (f x) (f x₁) := by
          constructor <;> nlinarith
        have himage : Ioo (f x) (f x₁) ⊆ f '' Ioo x x₁ :=
          intermediate_value_Ioo hxx₁ hcont
        rcases himage hzero_mem with ⟨z, hz_mem, hz_eq⟩
        have hz_Ioo : z ∈ Ioo a b := by
          have haz : a < z := hx.1.trans hz_mem.1
          have hzb : z < b := hz_mem.2.trans hx₁.2
          exact ⟨haz, hzb⟩
        exact absurd hz_eq (hf_nonzero z hz_Ioo)
      · have hxx₁' : x₁ ≤ x := by linarith
        have hcont : ContinuousOn f (Icc x₁ x) := by
          intro y hy
          have hy_Ioo : y ∈ Ioo a b := by
            have haz : a < y := lt_of_lt_of_le hx₁.1 hy.1
            have hzb : y < b := lt_of_le_of_lt hy.2 hx.2
            exact ⟨haz, hzb⟩
          exact (hf y hy_Ioo).continuousWithinAt
        have hzero_mem : (0 : ℝ) ∈ Ioo (f x) (f x₁) := by
          constructor <;> nlinarith
        have himage : Ioo (f x) (f x₁) ⊆ f '' Ioo x₁ x :=
          intermediate_value_Ioo' hxx₁' hcont
        rcases himage hzero_mem with ⟨z, hz_mem, hz_eq⟩
        have hz_Ioo : z ∈ Ioo a b := by
          have haz : a < z := hx₁.1.trans hz_mem.1
          have hzb : z < b := hz_mem.2.trans hx.2
          exact ⟨haz, hzb⟩
        exact absurd hz_eq (hf_nonzero z hz_Ioo)
  · push_neg at hpos
    have hneg : ∃ x ∈ Ioo a b, f x < 0 := by
      by_contra! h
      have : ∀ x ∈ Ioo a b, f x = 0 := by
        intro x hx
        have hx_nonzero := hf_nonzero x hx
        have hx_nonpos : f x ≤ 0 := hpos x hx
        have hx_nonneg : 0 ≤ f x := h x hx
        nlinarith
      have hmid : ((a + b)/2) ∈ Ioo a b := by
        constructor <;> nlinarith
      exact absurd (this ((a+b)/2) hmid) (hf_nonzero ((a+b)/2) hmid)
    rcases hneg with ⟨x₁, hx₁, hneg⟩
    refine Or.inr ?_
    intro x hx
    by_cases hx_neg : f x < 0
    · exact hx_neg
    · have hx_nonneg : f x ≥ 0 := by linarith
      have hx_nonzero : f x ≠ 0 := hf_nonzero x hx
      have hx_pos : f x > 0 := by
        by_contra! hle
        have : f x = 0 := by nlinarith
        exact hx_nonzero this
      by_cases hxx₁ : x ≤ x₁
      · have hcont : ContinuousOn f (Icc x x₁) := by
          intro y hy
          have hy_Ioo : y ∈ Ioo a b := by
            have haz : a < y := lt_of_lt_of_le hx.1 hy.1
            have hzb : y < b := lt_of_le_of_lt hy.2 hx₁.2
            exact ⟨haz, hzb⟩
          exact (hf y hy_Ioo).continuousWithinAt
        have hzero_mem : (0 : ℝ) ∈ Ioo (f x₁) (f x) := by
          constructor <;> nlinarith
        have himage : Ioo (f x₁) (f x) ⊆ f '' Ioo x x₁ :=
          intermediate_value_Ioo' hxx₁ hcont
        rcases himage hzero_mem with ⟨z, hz_mem, hz_eq⟩
        have hz_Ioo : z ∈ Ioo a b := by
          have haz : a < z := hx.1.trans hz_mem.1
          have hzb : z < b := hz_mem.2.trans hx₁.2
          exact ⟨haz, hzb⟩
        exact absurd hz_eq (hf_nonzero z hz_Ioo)
      · have hxx₁' : x₁ ≤ x := by linarith
        have hcont : ContinuousOn f (Icc x₁ x) := by
          intro y hy
          have hy_Ioo : y ∈ Ioo a b := by
            have haz : a < y := lt_of_lt_of_le hx₁.1 hy.1
            have hzb : y < b := lt_of_le_of_lt hy.2 hx.2
            exact ⟨haz, hzb⟩
          exact (hf y hy_Ioo).continuousWithinAt
        have hzero_mem : (0 : ℝ) ∈ Ioo (f x₁) (f x) := by
          constructor <;> nlinarith
        have himage : Ioo (f x₁) (f x) ⊆ f '' Ioo x₁ x :=
          intermediate_value_Ioo hxx₁' hcont
        rcases himage hzero_mem with ⟨z, hz_mem, hz_eq⟩
        have hz_Ioo : z ∈ Ioo a b := by
          have haz : a < z := hx₁.1.trans hz_mem.1
          have hzb : z < b := hz_mem.2.trans hx.2
          exact ⟨haz, hzb⟩
        exact absurd hz_eq (hf_nonzero z hz_Ioo)

namespace Submission

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
  rcases hW with ⟨x₀, hx₀J, hW₀⟩
  set W := fun x : ℝ => y₁ x * deriv y₂ x - y₂ x * deriv y₁ x with hWdef
  have haJ : a ∈ J := Set.mem_of_subset_of_mem hJ_sub (Set.left_mem_Icc.mpr (by linarith))
  have hbJ : b ∈ J := Set.mem_of_subset_of_mem hJ_sub (Set.right_mem_Icc.mpr (by linarith))
  have hJ_ord : J.OrdConnected := (isPreconnected_iff_ordConnected.mp hJ_conn)

  -- 1. W' = -p*W on J
  have hW_deriv : ∀ x ∈ J, HasDerivAt W (-(p x) * W x) x := by
    intro x hxJ
    dsimp [W]
    have hy₁_x : HasDerivAt y₁ (deriv y₁ x) x := hy₁ x hxJ
    have hy₁'_x : HasDerivAt (deriv y₁) (-(p x * deriv y₁ x + q x * y₁ x)) x := hy₁' x hxJ
    have hy₂_x : HasDerivAt y₂ (deriv y₂ x) x := hy₂ x hxJ
    have hy₂'_x : HasDerivAt (deriv y₂) (-(p x * deriv y₂ x + q x * y₂ x)) x := hy₂' x hxJ
    have h1 : HasDerivAt (fun x : ℝ => y₁ x * deriv y₂ x) (deriv y₁ x * deriv y₂ x + y₁ x * (-(p x * deriv y₂ x + q x * y₂ x))) x :=
      HasDerivAt.mul hy₁_x hy₂'_x
    have h2 : HasDerivAt (fun x : ℝ => y₂ x * deriv y₁ x) (deriv y₂ x * deriv y₁ x + y₂ x * (-(p x * deriv y₁ x + q x * y₁ x))) x :=
      HasDerivAt.mul hy₂_x hy₁'_x
    have hsub : HasDerivAt (fun x : ℝ => y₁ x * deriv y₂ x - y₂ x * deriv y₁ x)
      ((deriv y₁ x * deriv y₂ x + y₁ x * (-(p x * deriv y₂ x + q x * y₂ x))) - (deriv y₂ x * deriv y₁ x + y₂ x * (-(p x * deriv y₁ x + q x * y₁ x)))) x :=
      HasDerivAt.sub h1 h2
    have hsimpl : ((deriv y₁ x * deriv y₂ x + y₁ x * (-(p x * deriv y₂ x + q x * y₂ x))) - (deriv y₂ x * deriv y₁ x + y₂ x * (-(p x * deriv y₁ x + q x * y₁ x)))) = -(p x) * (y₁ x * deriv y₂ x - y₂ x * deriv y₁ x) := by
      ring
    rw [hsimpl] at hsub
    exact hsub

  -- 2. W never vanishes on J (by ODE uniqueness from x₀)
  have hW_nonzero : ∀ x ∈ J, W x ≠ 0 := by
    intro x hxJ
    by_contra! hWx
    by_cases hxx₀ : x = x₀
    · subst hxx₀; exact hW₀ hWx
    · rcases exists_open_interval_containing_two_points J hJ_open hJ_conn x x₀ hxJ hx₀J hxx₀ with ⟨c, d, hcd, hIcc_sub, hx_mem, hx₀_mem⟩
      have hp_cont : ContinuousOn (-p) (Icc c d) := (hp.mono hIcc_sub).neg
      have hW_deriv_on : ∀ t ∈ Ioo c d, HasDerivAt W (-(p t) * W t) t := by
        intro t ht
        have htJ : t ∈ J := hIcc_sub (Set.Ioo_subset_Icc_self ht)
        exact hW_deriv t htJ
      have hWx₀ : W x₀ = 0 :=
        linear_ode_zero_at_point (-p) W c d hcd x₀ x hx₀_mem hx_mem hp_cont hW_deriv_on hWx
      exact hW₀ hWx₀

  have hWa_nonzero : W a ≠ 0 := hW_nonzero a haJ
  have hWb_nonzero : W b ≠ 0 := hW_nonzero b hbJ

  -- 3. y₁ and y₂ are continuous on (a,b)
  have hy1_cont : ∀ x ∈ Ioo a b, ContinuousAt y₁ x := by
    intro x hx
    have hxJ : x ∈ J := Set.mem_of_subset_of_mem hJ_sub (Set.Ioo_subset_Icc_self hx)
    exact (hy₁ x hxJ).continuousAt

  have hy2_cont : ∀ x ∈ Ioo a b, ContinuousAt y₂ x := by
    intro x hx
    have hxJ : x ∈ J := Set.mem_of_subset_of_mem hJ_sub (Set.Ioo_subset_Icc_self hx)
    exact (hy₂ x hxJ).continuousAt

  -- 4. y₁ has constant sign on (a,b)
  have hy1_sign : (∀ x ∈ Ioo a b, y₁ x > 0) ∨ (∀ x ∈ Ioo a b, y₁ x < 0) :=
    const_sign_on_Ioo y₁ a b hab hy1_cont hne

  rcases hy1_sign with (hy1_pos | hy1_neg)
  · -- ===== Case y₁ > 0 on (a,b) =====
    have hy1_deriv_a_pos : deriv y₁ a > 0 := by
      have h_nonneg : 0 ≤ deriv y₁ a := by
        have hpos : ∀ᶠ x in nhdsWithin a (Set.Ioi a), y₁ x > 0 := by
          have h_nhd : Ioo a (min b (a+1)) ∈ nhdsWithin a (Set.Ioi a) :=
            Ioo_mem_nhdsWithin_Ioi a (min b (a+1)) (by nlinarith)
          filter_upwards [h_nhd] with x hx
          rcases hx with ⟨hxa, hxmin⟩
          have hx_Ioo : x ∈ Ioo a b := ⟨hxa, by
            have : x < min b (a+1) := hxmin; nlinarith⟩
          exact hy1_pos x hx_Ioo
        have h_deriv : HasDerivAt y₁ (deriv y₁ a) a := hy₁ a haJ
        exact deriv_nonneg_at_right y₁ a h_deriv hza hpos
      have h_nonzero : deriv y₁ a ≠ 0 := by
        intro hzero
        apply hWa_nonzero
        calc
          W a = y₁ a * deriv y₂ a - y₂ a * deriv y₁ a := rfl
          _ = 0 * deriv y₂ a - y₂ a * deriv y₁ a := by rw [hza]
          _ = -(y₂ a) * deriv y₁ a := by ring
          _ = -(y₂ a) * 0 := by rw [hzero]
          _ = 0 := by ring
      exact lt_of_le_of_ne h_nonneg h_nonzero.symm

    have hy1_deriv_b_neg : deriv y₁ b < 0 := by
      have h_nonpos : deriv y₁ b ≤ 0 := by
        have hpos : ∀ᶠ x in nhdsWithin b (Set.Iio b), y₁ x > 0 := by
          have h_nhd : Ioo (max a (b-1)) b ∈ nhdsWithin b (Set.Iio b) :=
            Ioo_mem_nhdsWithin_Iio (max a (b-1)) b (by nlinarith)
          filter_upwards [h_nhd] with x hx
          rcases hx with ⟨hxmax, hxb⟩
          have hx_Ioo : x ∈ Ioo a b := ⟨by nlinarith, hxb⟩
          exact hy1_pos x hx_Ioo
        have h_deriv : HasDerivAt y₁ (deriv y₁ b) b := hy₁ b hbJ
        exact deriv_nonpos_at_left y₁ b h_deriv hzb hpos
      have h_nonzero : deriv y₁ b ≠ 0 := by
        intro hzero
        apply hWb_nonzero
        calc
          W b = y₁ b * deriv y₂ b - y₂ b * deriv y₁ b := rfl
          _ = 0 * deriv y₂ b - y₂ b * deriv y₁ b := by rw [hzb]
          _ = -(y₂ b) * deriv y₁ b := by ring
          _ = -(y₂ b) * 0 := by rw [hzero]
          _ = 0 := by ring
      exact lt_of_le_of_ne h_nonpos h_nonzero

    have hy2a_nonzero : y₂ a ≠ 0 := by
      intro hy2a
      apply hWa_nonzero
      calc
        W a = y₁ a * deriv y₂ a - y₂ a * deriv y₁ a := rfl
        _ = 0 * deriv y₂ a - y₂ a * deriv y₁ a := by rw [hza]
        _ = -(y₂ a) * deriv y₁ a := by ring
        _ = -0 * deriv y₁ a := by rw [hy2a]
        _ = 0 := by ring

    have hy2b_nonzero : y₂ b ≠ 0 := by
      intro hy2b
      apply hWb_nonzero
      calc
        W b = y₁ b * deriv y₂ b - y₂ b * deriv y₁ b := rfl
        _ = 0 * deriv y₂ b - y₂ b * deriv y₁ b := by rw [hzb]
        _ = -(y₂ b) * deriv y₁ b := by ring
        _ = -0 * deriv y₁ b := by rw [hy2b]
        _ = 0 := by ring

    -- 5. Existence of a zero of y₂ in (a,b)
    have h_exists : ∃ c ∈ Ioo a b, y₂ c = 0 := by
      by_contra! h_no_zero
      have hy2_const_sign : (∀ x ∈ Ioo a b, y₂ x > 0) ∨ (∀ x ∈ Ioo a b, y₂ x < 0) :=
        const_sign_on_Ioo y₂ a b hab hy2_cont h_no_zero
      rcases hy2_const_sign with (hy2_pos | hy2_neg)
      · -- y₂ > 0 on (a,b)
        have hW_sign_opp : W a * W b < 0 := by
          have hWa_eq : W a = -(y₂ a) * deriv y₁ a := by
            dsimp [W]; rw [hza, zero_mul, sub_zero]
          have hWb_eq : W b = -(y₂ b) * deriv y₁ b := by
            dsimp [W]; rw [hzb, zero_mul, sub_zero]
          rw [hWa_eq, hWb_eq]
          have hy2a_pos : y₂ a > 0 := by
            by_contra! hle
            have hy2a_neg_or : y₂ a < 0 := by
              by_contra! hge; nlinarith
            have h_cont : ContinuousOn y₂ (Icc a ((a + b) / 2)) := by
              intro z hz
              have hz_Ioo : z ∈ Ioo a b := by
                rcases hz with ⟨hz1, hz2⟩
                refine ⟨by nlinarith, by nlinarith⟩
              exact (hy2_cont z hz_Ioo).continuousWithinAt
            have hzero_mem : (0 : ℝ) ∈ Ioo (y₂ a) (y₂ ((a+b)/2)) := by
              have : y₂ a < 0 := hy2a_neg_or; have : y₂ ((a+b)/2) > 0 := hy2_pos ((a+b)/2) (by nlinarith)
              constructor <;> nlinarith
            have himage : Ioo (y₂ a) (y₂ ((a+b)/2)) ⊆ y₂ '' Ioo a ((a+b)/2) :=
              intermediate_value_Ioo (by nlinarith) h_cont
            rcases himage hzero_mem with ⟨z, hz_mem, hz_eq⟩
            rcases hz_mem with ⟨hz1, hz2⟩
            exact h_no_zero z ⟨by nlinarith, by nlinarith⟩ hz_eq
          have hy2b_pos : y₂ b > 0 := by
            by_contra! hle
            have hy2b_neg_or : y₂ b < 0 := by
              by_contra! hge; nlinarith
            have h_cont : ContinuousOn y₂ (Icc ((a+b)/2) b) := by
              intro z hz
              have hz_Ioo : z ∈ Ioo a b := by
                rcases hz with ⟨hz1, hz2⟩
                refine ⟨by nlinarith, by nlinarith⟩
              exact (hy2_cont z hz_Ioo).continuousWithinAt
            have hzero_mem : (0 : ℝ) ∈ Ioo (y₂ ((a+b)/2)) (y₂ b) := by
              have : y₂ ((a+b)/2) > 0 := hy2_pos ((a+b)/2) (by nlinarith)
              have : y₂ b < 0 := hy2b_neg_or; constructor <;> nlinarith
            have himage : Ioo (y₂ ((a+b)/2)) (y₂ b) ⊆ y₂ '' Ioo ((a+b)/2) b :=
              intermediate_value_Ioo (by nlinarith) h_cont
            rcases himage hzero_mem with ⟨z, hz_mem, hz_eq⟩
            rcases hz_mem with ⟨hz1, hz2⟩
            exact h_no_zero z ⟨by nlinarith, by nlinarith⟩ hz_eq
          nlinarith
        have hW_cont : ContinuousOn W (Icc a b) := by
          intro x hx
          have hxJ : x ∈ J := Set.mem_of_subset_of_mem hJ_sub hx
          exact (hW_deriv x hxJ).continuousAt.continuousWithinAt
        have hIVT : ∃ x ∈ Ioo a b, W x = 0 := by
          by_cases hWab : W a < W b
          · have h0 : W a < 0 ∧ 0 < W b := by nlinarith
            have hzero_mem : (0 : ℝ) ∈ Ioo (W a) (W b) := ⟨h0.1, h0.2⟩
            have himage : Ioo (W a) (W b) ⊆ W '' Ioo a b :=
              intermediate_value_Ioo (by linarith) hW_cont
            rcases himage hzero_mem with ⟨z, hz, hz_eq⟩
            exact ⟨z, hz, hz_eq⟩
          · have hWba : W b < W a := by nlinarith
            have h0 : W b < 0 ∧ 0 < W a := by nlinarith
            have hzero_mem : (0 : ℝ) ∈ Ioo (W b) (W a) := ⟨h0.1, h0.2⟩
            have himage : Ioo (W b) (W a) ⊆ W '' Ioo a b :=
              intermediate_value_Ioo (by linarith) hW_cont
            rcases himage hzero_mem with ⟨z, hz, hz_eq⟩
            exact ⟨z, hz, hz_eq⟩
        rcases hIVT with ⟨x, hx, hx_eq⟩
        have hxJ : x ∈ J := Set.mem_of_subset_of_mem hJ_sub (Set.Ioo_subset_Icc_self hx)
        exact hW_nonzero x hxJ hx_eq
      · -- y₂ < 0 on (a,b) - symmetric
        have hW_sign_opp : W a * W b < 0 := by
          have hWa_eq : W a = -(y₂ a) * deriv y₁ a := by
            dsimp [W]; rw [hza, zero_mul, sub_zero]
          have hWb_eq : W b = -(y₂ b) * deriv y₁ b := by
            dsimp [W]; rw [hzb, zero_mul, sub_zero]
          rw [hWa_eq, hWb_eq]
          have hy2a_neg : y₂ a < 0 := by
            by_contra! hge
            have hy2a_pos_or : y₂ a > 0 := by
              by_contra! hle; nlinarith
            have h_cont : ContinuousOn y₂ (Icc a ((a+b)/2)) := by
              intro z hz
              have hz_Ioo : z ∈ Ioo a b := by
                rcases hz with ⟨hz1, hz2⟩
                refine ⟨by nlinarith, by nlinarith⟩
              exact (hy2_cont z hz_Ioo).continuousWithinAt
            have hzero_mem : (0 : ℝ) ∈ Ioo (y₂ ((a+b)/2)) (y₂ a) := by
              have : y₂ ((a+b)/2) < 0 := hy2_neg ((a+b)/2) (by nlinarith)
              have : y₂ a > 0 := hy2a_pos_or; constructor <;> nlinarith
            have himage : Ioo (y₂ ((a+b)/2)) (y₂ a) ⊆ y₂ '' Ioo ((a+b)/2) a :=
              intermediate_value_Ioo' (by nlinarith) h_cont
            rcases himage hzero_mem with ⟨z, hz_mem, hz_eq⟩
            rcases hz_mem with ⟨hz1, hz2⟩
            exact h_no_zero z ⟨by nlinarith, by nlinarith⟩ hz_eq
          have hy2b_neg : y₂ b < 0 := by
            by_contra! hge
            have hy2b_pos_or : y₂ b > 0 := by
              by_contra! hle; nlinarith
            have h_cont : ContinuousOn y₂ (Icc ((a+b)/2) b) := by
              intro z hz
              have hz_Ioo : z ∈ Ioo a b := by
                rcases hz with ⟨hz1, hz2⟩
                refine ⟨by nlinarith, by nlinarith⟩
              exact (hy2_cont z hz_Ioo).continuousWithinAt
            have hzero_mem : (0 : ℝ) ∈ Ioo (y₂ b) (y₂ ((a+b)/2)) := by
              have : y₂ b > 0 := hy2b_pos_or; have : y₂ ((a+b)/2) < 0 := hy2_neg ((a+b)/2) (by nlinarith)
              constructor <;> nlinarith
            have himage : Ioo (y₂ b) (y₂ ((a+b)/2)) ⊆ y₂ '' Ioo ((a+b)/2) b :=
              intermediate_value_Ioo' (by nlinarith) h_cont
            rcases himage hzero_mem with ⟨z, hz_mem, hz_eq⟩
            rcases hz_mem with ⟨hz1, hz2⟩
            exact h_no_zero z ⟨by nlinarith, by nlinarith⟩ hz_eq
          nlinarith
        have hW_cont : ContinuousOn W (Icc a b) := by
          intro x hx
          have hxJ : x ∈ J := Set.mem_of_subset_of_mem hJ_sub hx
          exact (hW_deriv x hxJ).continuousAt.continuousWithinAt
        have hIVT : ∃ x ∈ Ioo a b, W x = 0 := by
          by_cases hWab : W a < W b
          · have h0 : W a < 0 ∧ 0 < W b := by nlinarith
            have hzero_mem : (0 : ℝ) ∈ Ioo (W a) (W b) := ⟨h0.1, h0.2⟩
            have himage : Ioo (W a) (W b) ⊆ W '' Ioo a b :=
              intermediate_value_Ioo (by linarith) hW_cont
            rcases himage hzero_mem with ⟨z, hz, hz_eq⟩
            exact ⟨z, hz, hz_eq⟩
          · have hWba : W b < W a := by nlinarith
            have h0 : W b < 0 ∧ 0 < W a := by nlinarith
            have hzero_mem : (0 : ℝ) ∈ Ioo (W b) (W a) := ⟨h0.1, h0.2⟩
            have himage : Ioo (W b) (W a) ⊆ W '' Ioo a b :=
              intermediate_value_Ioo (by linarith) hW_cont
            rcases himage hzero_mem with ⟨z, hz, hz_eq⟩
            exact ⟨z, hz, hz_eq⟩
        rcases hIVT with ⟨x, hx, hx_eq⟩
        have hxJ : x ∈ J := Set.mem_of_subset_of_mem hJ_sub (Set.Ioo_subset_Icc_self hx)
        exact hW_nonzero x hxJ hx_eq

    -- 6. Uniqueness: at most one zero of y₂ in (a,b) via strict monotonicity of y₂/y₁
    have h_unique : ∀ c d ∈ Ioo a b, y₂ c = 0 → y₂ d = 0 → c = d := by
      intro c d hc hd hc0 hd0
      by_contra! hcd
      have hlt_or : c < d ∨ d < c := Ne.lt_or_lt hcd
      rcases hlt_or with (hlt | hlt)
      · -- c < d. (y₂/y₁)' = W/y₁² has constant sign, so y₂/y₁ is strictly monotone, hence injective.
        have h_deriv_ratio : ∀ x ∈ Ioo a b, HasDerivAt (fun x => y₂ x / y₁ x) (W x / (y₁ x)^2) x := by
          intro x hx
          have hy1x : HasDerivAt y₁ (deriv y₁ x) x := hy₁ x (Set.mem_of_subset_of_mem hJ_sub (Set.Ioo_subset_Icc_self hx))
          have hy2x : HasDerivAt y₂ (deriv y₂ x) x := hy₂ x (Set.mem_of_subset_of_mem hJ_sub (Set.Ioo_subset_Icc_self hx))
          have hy1x_ne : y₁ x ≠ 0 := hne x hx
          have hdiv : HasDerivAt (y₂ / y₁) ((deriv y₂ x * y₁ x - y₂ x * deriv y₁ x) / (y₁ x)^2) x :=
            HasDerivAt.div hy2x hy1x hy1x_ne
          have hnum : deriv y₂ x * y₁ x - y₂ x * deriv y₁ x = W x := by
            dsimp [W]; ring
          rw [hnum] at hdiv
          exact hdiv
        have hW_nonzero_on_Ioo : ∀ x ∈ Ioo a b, W x ≠ 0 := by
          intro x hx
          have hxJ : x ∈ J := Set.mem_of_subset_of_mem hJ_sub (Set.Ioo_subset_Icc_self hx)
          exact hW_nonzero x hxJ
        have hW_const_sign : (∀ x ∈ Ioo a b, W x > 0) ∨ (∀ x ∈ Ioo a b, W x < 0) := by
          have hW_cont_on : ∀ x ∈ Ioo a b, ContinuousAt W x := by
            intro x hx
            have hxJ : x ∈ J := Set.mem_of_subset_of_mem hJ_sub (Set.Ioo_subset_Icc_self hx)
            exact (hW_deriv x hxJ).continuousAt
          exact const_sign_on_Ioo W a b hab hW_cont_on hW_nonzero_on_Ioo
        rcases hW_const_sign with (hW_pos | hW_neg)
        · -- W > 0 on (a,b), so (y₂/y₁)' > 0
          have h_ratio_deriv_pos : ∀ x ∈ Ioo a b, 0 < W x / (y₁ x)^2 := by
            intro x hx
            have hy1_sq_pos : 0 < (y₁ x)^2 := pow_pos (hy1_pos x hx) 2
            exact div_pos (hW_pos x hx) hy1_sq_pos
          have h_strict_mono : StrictMonoOn (fun x => y₂ x / y₁ x) (Ioo a b) :=
            strictMonoOn_of_deriv_pos_on_Ioo (fun x => y₂ x / y₁ x) (fun x => W x / (y₁ x)^2) a b hab h_deriv_ratio h_ratio_deriv_pos
          have hc_mem : c ∈ Ioo a b := hc
          have hd_mem : d ∈ Ioo a b := hd
          have h_val_eq : (y₂ c / y₁ c) = (y₂ d / y₁ d) := by
            rw [hc0, hd0, zero_div, zero_div]
          have hc_eq_d : c = d := (h_strict_mono.eq_iff_eq hc_mem hd_mem).mp h_val_eq
          exact hcd hc_eq_d
        · -- W < 0 on (a,b), so (y₂/y₁)' < 0
          have h_ratio_deriv_neg : ∀ x ∈ Ioo a b, W x / (y₁ x)^2 < 0 := by
            intro x hx
            have hy1_sq_pos : 0 < (y₁ x)^2 := pow_pos (hy1_pos x hx) 2
            exact (div_neg_iff_of_pos hy1_sq_pos).mpr (hW_neg x hx)
          have h_strict_anti : StrictAntiOn (fun x => y₂ x / y₁ x) (Ioo a b) :=
            strictAntiOn_of_deriv_neg_on_Ioo (fun x => y₂ x / y₁ x) (fun x => W x / (y₁ x)^2) a b hab h_deriv_ratio h_ratio_deriv_neg
          have hc_mem : c ∈ Ioo a b := hc
          have hd_mem : d ∈ Ioo a b := hd
          have h_val_eq : (y₂ c / y₁ c) = (y₂ d / y₁ d) := by
            rw [hc0, hd0, zero_div, zero_div]
          have hc_eq_d : c = d := (h_strict_anti.eq_iff_eq hc_mem hd_mem).mp h_val_eq
          exact hcd hc_eq_d
      · -- d < c, symmetric to above
        have h_deriv_ratio : ∀ x ∈ Ioo a b, HasDerivAt (fun x => y₂ x / y₁ x) (W x / (y₁ x)^2) x := by
          intro x hx
          have hy1x : HasDerivAt y₁ (deriv y₁ x) x := hy₁ x (Set.mem_of_subset_of_mem hJ_sub (Set.Ioo_subset_Icc_self hx))
          have hy2x : HasDerivAt y₂ (deriv y₂ x) x := hy₂ x (Set.mem_of_subset_of_mem hJ_sub (Set.Ioo_subset_Icc_self hx))
          have hy1x_ne : y₁ x ≠ 0 := hne x hx
          have hdiv : HasDerivAt (y₂ / y₁) ((deriv y₂ x * y₁ x - y₂ x * deriv y₁ x) / (y₁ x)^2) x :=
            HasDerivAt.div hy2x hy1x hy1x_ne
          have hnum : deriv y₂ x * y₁ x - y₂ x * deriv y₁ x = W x := by
            dsimp [W]; ring
          rw [hnum] at hdiv
          exact hdiv
        have hW_nonzero_on_Ioo : ∀ x ∈ Ioo a b, W x ≠ 0 := by
          intro x hx
          have hxJ : x ∈ J := Set.mem_of_subset_of_mem hJ_sub (Set.Ioo_subset_Icc_self hx)
          exact hW_nonzero x hxJ
        have hW_const_sign : (∀ x ∈ Ioo a b, W x > 0) ∨ (∀ x ∈ Ioo a b, W x < 0) := by
          have hW_cont_on : ∀ x ∈ Ioo a b, ContinuousAt W x := by
            intro x hx
            have hxJ : x ∈ J := Set.mem_of_subset_of_mem hJ_sub (Set.Ioo_subset_Icc_self hx)
            exact (hW_deriv x hxJ).continuousAt
          exact const_sign_on_Ioo W a b hab hW_cont_on hW_nonzero_on_Ioo
        rcases hW_const_sign with (hW_pos | hW_neg)
        · have h_ratio_deriv_pos : ∀ x ∈ Ioo a b, 0 < W x / (y₁ x)^2 := by
            intro x hx
            have hy1_sq_pos : 0 < (y₁ x)^2 := pow_pos (hy1_pos x hx) 2
            exact div_pos (hW_pos x hx) hy1_sq_pos
          have h_strict_mono : StrictMonoOn (fun x => y₂ x / y₁ x) (Ioo a b) :=
            strictMonoOn_of_deriv_pos_on_Ioo (fun x => y₂ x / y₁ x) (fun x => W x / (y₁ x)^2) a b hab h_deriv_ratio h_ratio_deriv_pos
          have hc_mem : c ∈ Ioo a b := hc
          have hd_mem : d ∈ Ioo a b := hd
          have h_val_eq : (y₂ c / y₁ c) = (y₂ d / y₁ d) := by
            rw [hc0, hd0, zero_div, zero_div]
          have hc_eq_d : c = d := (h_strict_mono.eq_iff_eq hc_mem hd_mem).mp h_val_eq
          exact hcd hc_eq_d
        · have h_ratio_deriv_neg : ∀ x ∈ Ioo a b, W x / (y₁ x)^2 < 0 := by
            intro x hx
            have hy1_sq_pos : 0 < (y₁ x)^2 := pow_pos (hy1_pos x hx) 2
            exact (div_neg_iff_of_pos hy1_sq_pos).mpr (hW_neg x hx)
          have h_strict_anti : StrictAntiOn (fun x => y₂ x / y₁ x) (Ioo a b) :=
            strictAntiOn_of_deriv_neg_on_Ioo (fun x => y₂ x / y₁ x) (fun x => W x / (y₁ x)^2) a b hab h_deriv_ratio h_ratio_deriv_neg
          have hc_mem : c ∈ Ioo a b := hc
          have hd_mem : d ∈ Ioo a b := hd
          have h_val_eq : (y₂ c / y₁ c) = (y₂ d / y₁ d) := by
            rw [hc0, hd0, zero_div, zero_div]
          have hc_eq_d : c = d := (h_strict_anti.eq_iff_eq hc_mem hd_mem).mp h_val_eq
          exact hcd hc_eq_d

    exact ⟨h_exists, h_unique⟩
  · -- ===== Case y₁ < 0 on (a,b) =====
    -- Apply the same argument to -y₁, -y₂. Note that W = y₁*y₂' - y₂*y₁' is unchanged.
    have h_neg_y1_pos : ∀ x ∈ Ioo a b, (-y₁) x > 0 := by
      intro x hx; simpa using hy1_neg x hx
    have h_neg_y1_zero_a : (-y₁) a = 0 := by simpa [hza]
    have h_neg_y1_zero_b : (-y₁) b = 0 := by simpa [hzb]
    have h_neg_y1_nonzero : ∀ x ∈ Ioo a b, (-y₁) x ≠ 0 := by
      intro x hx; simpa using hne x hx
    have hW_neg : ∃ x₀' ∈ J, (-y₁) x₀' * deriv (-y₂) x₀' - (-y₂) x₀' * deriv (-y₁) x₀' ≠ 0 := by
      refine ⟨x₀, hx₀J, ?_⟩
      have hW_eq : (-y₁) x₀ * deriv (-y₂) x₀ - (-y₂) x₀ * deriv (-y₁) x₀ = y₁ x₀ * deriv y₂ x₀ - y₂ x₀ * deriv y₁ x₀ := by
        simp [deriv_neg, W]
      rw [hW_eq]
      exact hW₀
    have h_result : ∃! c, c ∈ Ioo a b ∧ (-y₂) c = 0 :=
      sturm_separation p q (-y₁) (-y₂) a b hab J hJ_open hJ_conn hJ_sub hp hq
        (fun x hxJ => by
          have hy1x := hy₁ x hxJ
          have : HasDerivAt (-y₁) (-(deriv y₁ x)) x := HasDerivAt.neg hy1x
          simpa [deriv_neg] using this)
        (fun x hxJ => by
          simpa [deriv_neg, neg_mul, add_comm, sub_eq_add_neg] using hy₁' x hxJ)
        (fun x hxJ => by
          have hy2x := hy₂ x hxJ
          have : HasDerivAt (-y₂) (-(deriv y₂ x)) x := HasDerivAt.neg hy2x
          simpa [deriv_neg] using this)
        (fun x hxJ => by
          simpa [deriv_neg, neg_mul, add_comm, sub_eq_add_neg] using hy₂' x hxJ)
        hW_neg h_neg_y1_zero_a h_neg_y1_zero_b h_neg_y1_nonzero
    rcases h_result with ⟨c, ⟨hc, hc0⟩, huniq⟩
    refine ⟨c, ⟨hc, ?_⟩, ?_⟩
    · simpa using hc0
    · intro d ⟨hd, hd0⟩
      apply huniq d ⟨hd, ?_⟩
      simpa using hd0

end Submission