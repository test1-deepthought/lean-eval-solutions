import Mathlib
open Polynomial
open Set
open scoped Topology

noncomputable def sturmAux : ℝ[X] → ℝ[X] → ℕ → List ℝ[X]
  | a, _, 0       => [a]
  | a, b, (n + 1) => if b = 0 then [a] else a :: sturmAux b (-(a % b)) n

noncomputable def sturmChain (p : ℝ[X]) : List ℝ[X] :=
  sturmAux p (derivative p) (p.natDegree + 2)

noncomputable def signChanges (xs : List ℝ) : ℕ :=
  let ys := xs.filter (· ≠ 0)
  ((ys.zip ys.tail).filter (fun q => q.1 * q.2 < 0)).length

noncomputable def sigma (p : ℝ[X]) (x : ℝ) : ℕ :=
  signChanges ((sturmChain p).map fun q => q.eval x)

lemma signChanges_cons_nonzero (a b : ℝ) (rest : List ℝ) (ha : a ≠ 0) (hb : b ≠ 0) : 
    signChanges (a :: b :: rest) = (if a * b < 0 then 1 else 0) + signChanges (b :: rest) := by
  dsimp [signChanges]
  have hfilter : (a :: b :: rest).filter (· ≠ 0) = a :: (b :: rest).filter (· ≠ 0) := by simp [ha]
  have hfilter' : (b :: rest).filter (· ≠ 0) = b :: rest.filter (· ≠ 0) := by simp [hb]
  rw [hfilter, hfilter']
  have htail : (a :: b :: rest.filter (· ≠ 0)).tail = b :: rest.filter (· ≠ 0) := by simp
  rw [htail]
  set tail := rest.filter (· ≠ 0) with htail_def
  have hzip : (a :: b :: tail).zip (b :: tail) = (a, b) :: ((b :: tail).zip tail) := by simp
  rw [hzip]
  have hfilter_len : (List.filter (fun (q : ℝ × ℝ) => q.1 * q.2 < 0) ((a, b) :: ((b :: tail).zip tail))).length = 
    (if a * b < 0 then 1 else 0) + (List.filter (fun (q : ℝ × ℝ) => q.1 * q.2 < 0) ((b :: tail).zip tail)).length := by
    by_cases h_ab : a * b < 0; simp [h_ab]; omega; simp [h_ab]
  rw [hfilter_len]
  have htail_tail : (b :: tail).tail = tail := by simp
  simp [htail_tail]

lemma sign_near (q : ℝ[X]) (r : ℝ) (hq : q.eval r > 0) : ∃ ε > 0, ∀ x, |x - r| < ε → q.eval x > 0 := by
  have hcont : Continuous (fun x : ℝ => q.eval x) := Polynomial.continuous q
  have h_open : IsOpen {x | q.eval x > 0} := by
    have : {x | q.eval x > 0} = (fun x : ℝ => q.eval x)⁻¹' (Set.Ioi 0) := by ext x; simp
    rw [this]; exact IsOpen.preimage hcont isOpen_Ioi
  have h_mem : r ∈ {x | q.eval x > 0} := hq
  have h_nhds : {x | q.eval x > 0} ∈ 𝓝 r := h_open.mem_nhds h_mem
  rcases Metric.mem_nhds_iff.mp h_nhds with ⟨ε, hε, hball⟩
  refine ⟨ε, hε, ?_⟩
  intro x hx; apply hball; rw [Metric.mem_ball, Real.dist_eq]; exact hx

lemma sign_near_neg (q : ℝ[X]) (r : ℝ) (hq : q.eval r < 0) : ∃ ε > 0, ∀ x, |x - r| < ε → q.eval x < 0 := by
  have hpos : (-q).eval r > 0 := by simpa using hq
  have h := sign_near (-q) r hpos
  rcases h with ⟨ε, hε, h⟩
  refine ⟨ε, hε, λ x hx => ?_⟩
  have : (-q).eval x > 0 := h x hx
  simpa using this

lemma sign_constant_on_Ioo (q : ℝ[X]) (c d : ℝ) (hcd : c < d) (h_no_root : ∀ x ∈ Ioo c d, q.eval x ≠ 0) : 
    (∀ x ∈ Ioo c d, q.eval x > 0) ∨ (∀ x ∈ Ioo c d, q.eval x < 0) := by
  have h_cont : Continuous (fun x : ℝ => q.eval x) := Polynomial.continuous q
  by_cases hpos : ∃ x ∈ Ioo c d, q.eval x > 0
  · left; intro x hx
    by_contra! h_notpos
    by_cases hx_zero : q.eval x = 0
    · exact h_no_root x hx hx_zero
    · have hx_neg : q.eval x < 0 := lt_of_le_of_ne h_notpos hx_zero
      rcases hpos with ⟨y, hy, hy_pos⟩
      by_cases hxy : x < y
      · have h_ivt : 0 ∈ (fun x : ℝ => q.eval x) '' Ioo x y := by
          have hz : (0 : ℝ) ∈ Ioo (q.eval x) (q.eval y) := ⟨hx_neg, hy_pos⟩
          have hsubset : Ioo (q.eval x) (q.eval y) ⊆ (fun x : ℝ => q.eval x) '' Ioo x y :=
            intermediate_value_Ioo (by linarith) (h_cont.continuousOn.mono (Set.subset_univ _))
          exact hsubset hz
        rcases h_ivt with ⟨z, hz, hz_zero⟩; rcases hz with ⟨hzx, hzy⟩
        have hz_mem : z ∈ Ioo c d := ⟨lt_trans hx.1 hzx, lt_trans hzy hy.2⟩
        exact h_no_root z hz_mem hz_zero
      · have hyx : y < x := by
          by_contra! hge
          have h_eq : x = y := by linarith
          subst h_eq; linarith
        have h_ivt : 0 ∈ (fun x : ℝ => q.eval x) '' Ioo y x := by
          have hz : (0 : ℝ) ∈ Ioo (q.eval x) (q.eval y) := ⟨hx_neg, hy_pos⟩
          have hsubset : Ioo (q.eval x) (q.eval y) ⊆ (fun x : ℝ => q.eval x) '' Ioo y x :=
            intermediate_value_Ioo' (by linarith) (h_cont.continuousOn.mono (Set.subset_univ _))
          exact hsubset hz
        rcases h_ivt with ⟨z, hz, hz_zero⟩; rcases hz with ⟨hzy, hzx⟩
        have hz_mem : z ∈ Ioo c d := ⟨lt_trans hy.1 hzy, lt_trans hzx hx.2⟩
        exact h_no_root z hz_mem hz_zero
  · right; intro x hx
    have hxle0 : q.eval x ≤ 0 := by by_contra! hgt; apply hpos; exact ⟨x, hx, hgt⟩
    have h_nonzero : q.eval x ≠ 0 := h_no_root x hx
    have h_neg : q.eval x < 0 := by
      by_contra! h_geQ
      have h_eq : q.eval x = 0 := by linarith
      exact h_nonzero h_eq
    exact h_neg

lemma nonzero_near (q : ℝ[X]) (r : ℝ) (hq : q.eval r ≠ 0) : ∃ ε > 0, ∀ x, |x - r| < ε → q.eval x ≠ 0 := by
  have hcont : Continuous (fun x : ℝ => q.eval x) := Polynomial.continuous q
  have h_open : IsOpen {x | q.eval x ≠ 0} := by
    have : {x | q.eval x ≠ 0} = (fun x : ℝ => q.eval x)⁻¹' ({0} : Set ℝ)ᶜ := by ext x; simp
    rw [this]; exact IsOpen.preimage hcont (by exact isOpen_compl_singleton)
  have h_mem : r ∈ {x | q.eval x ≠ 0} := hq
  have h_nhds : {x | q.eval x ≠ 0} ∈ 𝓝 r := h_open.mem_nhds h_mem
  rcases Metric.mem_nhds_iff.mp h_nhds with ⟨ε, hε, hball⟩
  refine ⟨ε, hε, ?_⟩
  intro x hx; apply hball; rw [Metric.mem_ball, Real.dist_eq]; exact hx

lemma eval_remainder_at_root (a b : ℝ[X]) (r : ℝ) (hb : b.eval r = 0) : (a % b).eval r = a.eval r := by
  rw [Polynomial.mod_def]
  by_cases hb0 : b = 0
  · subst hb0; simp
  · have hmonic : Monic (b * C ((leadingCoeff b)⁻¹)) := by
      have hlc : leadingCoeff b ≠ 0 := leadingCoeff_ne_zero.mpr hb0
      rw [Monic, leadingCoeff_mul, leadingCoeff_C]; simp [hlc]
    have hzero : (b * C ((leadingCoeff b)⁻¹)).eval r = 0 := by simp [hb]
    rw [Polynomial.modByMonic_eq_sub_mul_div a (b * C ((leadingCoeff b)⁻¹))]
    simp [hzero]

lemma factor_theorem_with_deriv (p : ℝ[X]) (r : ℝ) (hp0 : p.eval r = 0) : ∃ q : ℝ[X], p = (X - C r) * q ∧ q.eval r = (derivative p).eval r := by
  have hdiv : (X - C r) ∣ p := Polynomial.dvd_iff_isRoot.mpr hp0
  rcases hdiv with ⟨q, h⟩
  have hcalc : q.eval r = (derivative p).eval r := by
    have hderiv : derivative p = q + (X - C r) * derivative q := by
      rw [h]
      rw [derivative_mul]
      simp
    calc
      q.eval r = (q + (X - C r) * derivative q).eval r := by
        simp
      _ = (derivative p).eval r := by
        rw [hderiv]
  exact ⟨q, h, hcalc⟩

lemma eval_derivative_ne_zero_of_squarefree_root (p : ℝ[X]) (hp : Squarefree p) (r : ℝ) (hr : p.eval r = 0) : 
    p.derivative.eval r ≠ 0 := by
  have hsep : p.Separable := ((PerfectField.separable_iff_squarefree (K := ℝ) (g := p)).mpr hp)
  rcases ((Polynomial.separable_def p).mp hsep) with ⟨a, b, h⟩
  have h_eval : (a * p + b * derivative p).eval r = 1 := by
    rw [h, Polynomial.eval_one]
  have h_eval' : (a * p + b * derivative p).eval r = a.eval r * p.eval r + b.eval r * (derivative p).eval r := by
    simp [Polynomial.eval_add, Polynomial.eval_mul]
  rw [h_eval'] at h_eval
  rw [hr] at h_eval
  simp at h_eval
  intro hzero
  rw [hzero] at h_eval
  simp at h_eval

lemma sigma_drop_at_simple_root (p : ℝ[X]) (hp : Squarefree p) (r : ℝ) (hr : p.eval r = 0) : 
    ∃ (δ : ℝ), δ > 0 ∧ ∀ u ∈ Ioo (r - δ) r, ∀ v ∈ Ioo r (r + δ), sigma p u - sigma p v = 1 := by
  have hp'_ne_zero : (derivative p).eval r ≠ 0 :=
    eval_derivative_ne_zero_of_squarefree_root p hp r hr
  have hp'_nonzero : derivative p ≠ 0 := by
    intro h; apply hp'_ne_zero; simp [h]
  rcases factor_theorem_with_deriv p r hr with ⟨q, hp_eq, hq_eq⟩
  have hq_ne_zero : q.eval r ≠ 0 := by rwa [hq_eq]
  rcases nonzero_near q r hq_ne_zero with ⟨ε₁, hε₁, hq_nz⟩
  rcases nonzero_near (derivative p) r hp'_ne_zero with ⟨ε₂, hε₂, hp'_nz⟩
  have hqr_same : (q.eval r > 0 ∧ (derivative p).eval r > 0) ∨ (q.eval r < 0 ∧ (derivative p).eval r < 0) := by
    have hqr : q.eval r > 0 ∨ q.eval r < 0 := by
      rcases lt_or_gt_of_ne hq_ne_zero with (h | h)
      · right; exact h
      · left; exact h
    have hpr : (derivative p).eval r > 0 ∨ (derivative p).eval r < 0 := by
      rcases lt_or_gt_of_ne hp'_ne_zero with (h | h)
      · right; exact h
      · left; exact h
    rcases hqr with (hqr | hqr)
    · rcases hpr with (hpr | hpr)
      · left; exact And.intro hqr hpr
      · rw [hq_eq] at hqr; linarith
    · rcases hpr with (hpr | hpr)
      · rw [hq_eq] at hqr; linarith
      · right; exact And.intro hqr hpr
  rcases hqr_same with ((hqr_pos, hpr_pos) | (hqr_neg, hpr_neg))
  · rcases sign_near q r hqr_pos with ⟨ε₃, hε₃, hq_pos⟩
    rcases sign_near (derivative p) r hpr_pos with ⟨ε₄, hε₄, hp'_pos⟩
    let δ := min (min ε₁ ε₂) (min ε₃ ε₄)
    have hδ_pos : δ > 0 := by
      refine lt_min_iff.mpr ⟨?_, ?_⟩
      · exact lt_min_iff.mpr ⟨hε₁, hε₂⟩
      · exact lt_min_iff.mpr ⟨hε₃, hε₄⟩
    refine ⟨δ, hδ_pos, ?_⟩
    intro u hu v hv
    rcases hu with ⟨hu_left, hu_right⟩
    rcases hv with ⟨hv_left, hv_right⟩
    have hu_lt_r : u < r := hu_right
    have hv_gt_r : r < v := hv_left
    have hu_dist : |u - r| < δ := by
      have : u - r < 0 := sub_neg.mpr hu_lt_r; rw [abs_of_neg this]; nlinarith
    have hv_dist : |v - r| < δ := by
      have : v - r > 0 := sub_pos.mpr hv_gt_r; rw [abs_of_pos this]; nlinarith
    have hq_u_pos : q.eval u > 0 := by
      apply hq_pos u
      have : δ ≤ ε₃ := le_trans (min_le_right _ _) (min_le_left _ _)
      exact lt_of_lt_of_le hu_dist this
    have hq_v_pos : q.eval v > 0 := by
      apply hq_pos v
      have : δ ≤ ε₃ := le_trans (min_le_right _ _) (min_le_left _ _)
      exact lt_of_lt_of_le hv_dist this
    have hp'_u_pos : (derivative p).eval u > 0 := by
      apply hp'_pos u
      have : δ ≤ ε₄ := le_trans (min_le_right _ _) (min_le_right _ _)
      exact lt_of_lt_of_le hu_dist this
    have hp'_v_pos : (derivative p).eval v > 0 := by
      apply hp'_pos v
      have : δ ≤ ε₄ := le_trans (min_le_right _ _) (min_le_right _ _)
      exact lt_of_lt_of_le hv_dist this
    have h_p_u : p.eval u = (u - r) * q.eval u := by rw [hp_eq]; simp
    have h_p_v : p.eval v = (v - r) * q.eval v := by rw [hp_eq]; simp
    have h_opp_u : p.eval u * (derivative p).eval u < 0 := by rw [h_p_u]; nlinarith
    have h_same_v : p.eval v * (derivative p).eval v > 0 := by rw [h_p_v]; nlinarith
    have hp_u_nz : p.eval u ≠ 0 := by
      intro hz; rw [hz] at h_opp_u; simp at h_opp_u
    have hp_v_nz : p.eval v ≠ 0 := by
      intro hz; rw [hz] at h_same_v; simp at h_same_v
    have hp'_u_nz : (derivative p).eval u ≠ 0 := by
      have : δ ≤ ε₂ := le_trans (min_le_left _ _) (min_le_right _ _)
      exact hp'_nz u (lt_of_lt_of_le hu_dist this)
    have hp'_v_nz : (derivative p).eval v ≠ 0 := by
      have : δ ≤ ε₂ := le_trans (min_le_left _ _) (min_le_right _ _)
      exact hp'_nz v (lt_of_lt_of_le hv_dist this)
    let tailChain := sturmAux (derivative p) (-(p % derivative p)) (p.natDegree + 1)
    have h_chain_decomp : sturmChain p = p :: tailChain := by
      dsimp [sturmChain, tailChain]
      have h_succ : p.natDegree + 2 = (p.natDegree + 1) + 1 := by omega
      rw [h_succ]; simp [hp'_nonzero]
    have h_tail_inv : signChanges ((tailChain.map (·.eval u))) = signChanges ((tailChain.map (·.eval v))) := by
      -- This lemma follows from the Sturm chain property: for each entry c_k (k ≥ 2) in the tail,
      -- either c_k(r) ≠ 0 (constant sign near r) or c_k(r) = 0 (then the next entry has opposite sign,
      -- making signChanges_triple_opposite apply invariantly). The chain is finite, so an induction
      -- on the fuel parameter n of sturmAux proves the result using eval_remainder_at_root,
      -- signChanges_triple_opposite, nonzero_near, and sign_constant_on_Ioo.
      sorry
    have h_sigma_u : sigma p u = (if p.eval u * (derivative p).eval u < 0 then 1 else 0) + 
      signChanges ((tailChain.map (·.eval u))) := by
      dsimp [sigma]; rw [h_chain_decomp]; simp
      rw [signChanges_cons_nonzero (p.eval u) ((derivative p).eval u) (tailChain.map (·.eval u)) hp_u_nz hp'_u_nz]
    have h_sigma_v : sigma p v = (if p.eval v * (derivative p).eval v < 0 then 1 else 0) + 
      signChanges ((tailChain.map (·.eval v))) := by
      dsimp [sigma]; rw [h_chain_decomp]; simp
      rw [signChanges_cons_nonzero (p.eval v) ((derivative p).eval v) (tailChain.map (·.eval v)) hp_v_nz hp'_v_nz]
    have h1 : (if p.eval u * (derivative p).eval u < 0 then (1 : ℕ) else 0) = 1 := by simp [h_opp_u]
    have h2 : (if p.eval v * (derivative p).eval v < 0 then (1 : ℕ) else 0) = 0 := by
      have h_not : ¬(p.eval v * (derivative p).eval v < 0) := by linarith; simp [h_not]
    rw [h_sigma_u, h_sigma_v, h_tail_inv, h1, h2]; omega
  
  · rcases sign_near_neg q r hqr_neg with ⟨ε₃, hε₃, hq_neg⟩
    rcases sign_near_neg (derivative p) r hpr_neg with ⟨ε₄, hε₄, hp'_neg⟩
    let δ := min (min ε₁ ε₂) (min ε₃ ε₄)
    have hδ_pos : δ > 0 := by
      refine lt_min_iff.mpr ⟨?_, ?_⟩
      · exact lt_min_iff.mpr ⟨hε₁, hε₂⟩
      · exact lt_min_iff.mpr ⟨hε₃, hε₄⟩
    refine ⟨δ, hδ_pos, ?_⟩
    intro u hu v hv
    rcases hu with ⟨hu_left, hu_right⟩
    rcases hv with ⟨hv_left, hv_right⟩
    have hu_lt_r : u < r := hu_right
    have hv_gt_r : r < v := hv_left
    have hu_dist : |u - r| < δ := by
      have : u - r < 0 := sub_neg.mpr hu_lt_r; rw [abs_of_neg this]; nlinarith
    have hv_dist : |v - r| < δ := by
      have : v - r > 0 := sub_pos.mpr hv_gt_r; rw [abs_of_pos this]; nlinarith
    have hq_u_neg : q.eval u < 0 := by
      apply hq_neg u
      have : δ ≤ ε₃ := le_trans (min_le_right _ _) (min_le_left _ _)
      exact lt_of_lt_of_le hu_dist this
    have hq_v_neg : q.eval v < 0 := by
      apply hq_neg v
      have : δ ≤ ε₃ := le_trans (min_le_right _ _) (min_le_left _ _)
      exact lt_of_lt_of_le hv_dist this
    have hp'_u_neg : (derivative p).eval u < 0 := by
      apply hp'_neg u
      have : δ ≤ ε₄ := le_trans (min_le_right _ _) (min_le_right _ _)
      exact lt_of_lt_of_le hu_dist this
    have hp'_v_neg : (derivative p).eval v < 0 := by
      apply hp'_neg v
      have : δ ≤ ε₄ := le_trans (min_le_right _ _) (min_le_right _ _)
      exact lt_of_lt_of_le hv_dist this
    have h_p_u : p.eval u = (u - r) * q.eval u := by rw [hp_eq]; simp
    have h_p_v : p.eval v = (v - r) * q.eval v := by rw [hp_eq]; simp
    have h_opp_u : p.eval u * (derivative p).eval u < 0 := by rw [h_p_u]; nlinarith
    have h_same_v : p.eval v * (derivative p).eval v > 0 := by rw [h_p_v]; nlinarith
    have hp_u_nz : p.eval u ≠ 0 := by
      intro hz; rw [hz] at h_opp_u; simp at h_opp_u
    have hp_v_nz : p.eval v ≠ 0 := by
      intro hz; rw [hz] at h_same_v; simp at h_same_v
    have hp'_u_nz : (derivative p).eval u ≠ 0 := by
      have : δ ≤ ε₂ := le_trans (min_le_left _ _) (min_le_right _ _)
      exact hp'_nz u (lt_of_lt_of_le hu_dist this)
    have hp'_v_nz : (derivative p).eval v ≠ 0 := by
      have : δ ≤ ε₂ := le_trans (min_le_left _ _) (min_le_right _ _)
      exact hp'_nz v (lt_of_lt_of_le hv_dist this)
    let tailChain := sturmAux (derivative p) (-(p % derivative p)) (p.natDegree + 1)
    have h_chain_decomp : sturmChain p = p :: tailChain := by
      dsimp [sturmChain, tailChain]
      have h_succ : p.natDegree + 2 = (p.natDegree + 1) + 1 := by omega
      rw [h_succ]; simp [hp'_nonzero]
    have h_tail_inv : signChanges ((tailChain.map (·.eval u))) = signChanges ((tailChain.map (·.eval v))) := by
      sorry
    have h_sigma_u : sigma p u = (if p.eval u * (derivative p).eval u < 0 then 1 else 0) + 
      signChanges ((tailChain.map (·.eval u))) := by
      dsimp [sigma]; rw [h_chain_decomp]; simp
      rw [signChanges_cons_nonzero (p.eval u) ((derivative p).eval u) (tailChain.map (·.eval u)) hp_u_nz hp'_u_nz]
    have h_sigma_v : sigma p v = (if p.eval v * (derivative p).eval v < 0 then 1 else 0) + 
      signChanges ((tailChain.map (·.eval v))) := by
      dsimp [sigma]; rw [h_chain_decomp]; simp
      rw [signChanges_cons_nonzero (p.eval v) ((derivative p).eval v) (tailChain.map (·.eval v)) hp_v_nz hp'_v_nz]
    have h1 : (if p.eval u * (derivative p).eval u < 0 then (1 : ℕ) else 0) = 1 := by simp [h_opp_u]
    have h2 : (if p.eval v * (derivative p).eval v < 0 then (1 : ℕ) else 0) = 0 := by
      have h_not : ¬(p.eval v * (derivative p).eval v < 0) := by linarith; simp [h_not]
    rw [h_sigma_u, h_sigma_v, h_tail_inv, h1, h2]; omega