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

lemma signChanges_singleton (a : ℝ) : signChanges [a] = 0 := by
  dsimp [signChanges]; by_cases ha : a = 0; subst ha; simp; simp [ha]

lemma signChanges_cons_nonzero (a b : ℝ) (rest : List ℝ) (ha : a ≠ 0) (hb : b ≠ 0) : 
    signChanges (a :: b :: rest) = (if a * b < 0 then 1 else 0) + signChanges (b :: rest) := by
  dsimp [signChanges]
  have hfilter : (a :: b :: rest).filter (· ≠ 0) = a :: (b :: rest).filter (· ≠ 0) := by simp [ha]
  have hfilter' : (b :: rest).filter (· ≠ 0) = b :: rest.filter (· ≠ 0) := by simp [hb]
  rw [hfilter, hfilter']
  have htail : (a :: b :: rest.filter (· ≠ 0)).tail = b :: rest.filter (· ≠ 0) := by simp
  rw [htail]; set tail := rest.filter (· ≠ 0) with htail_def
  have hzip : (a :: b :: tail).zip (b :: tail) = (a, b) :: ((b :: tail).zip tail) := by simp
  rw [hzip]
  have hfilter_len : (List.filter (fun (q : ℝ × ℝ) => q.1 * q.2 < 0) ((a, b) :: ((b :: tail).zip tail))).length = 
    (if a * b < 0 then 1 else 0) + (List.filter (fun (q : ℝ × ℝ) => q.1 * q.2 < 0) ((b :: tail).zip tail)).length := by
    by_cases h_ab : a * b < 0; simp [h_ab]; omega; simp [h_ab]
  rw [hfilter_len]; have htail_tail : (b :: tail).tail = tail := by simp; simp [htail_tail]

lemma signChanges_cons_triple (a b c : ℝ) (rest : List ℝ) (ha : a ≠ 0) (hc : c ≠ 0) (h_ac : a * c < 0) :
    signChanges (a :: b :: c :: rest) = 1 + signChanges (c :: rest) := by
  by_cases hb0 : b = 0
  · subst hb0; calc
      signChanges (a :: 0 :: c :: rest) = signChanges (a :: c :: rest) := by
        dsimp [signChanges]; simp [ha, hc]
      _ = (if a * c < 0 then 1 else 0) + signChanges (c :: rest) := signChanges_cons_nonzero a c rest ha hc
      _ = 1 + signChanges (c :: rest) := by simp [h_ac]
  · have hb : b ≠ 0 := hb0
    have h_triple_val : (if a * b < 0 then (1 : ℕ) else 0) + (if b * c < 0 then (1 : ℕ) else 0) = 1 := by
      have h_sq_pos : b * b > 0 := mul_self_pos.mpr hb; have h_eq : (a * b) * (b * c) = (a * c) * (b * b) := by ring
      by_cases h_ab : a * b < 0
      · have h_not_bc : ¬(b * c < 0) := by
          intro h_bc; have h_pos : (a * b) * (b * c) > 0 := mul_pos_of_neg_of_neg h_ab h_bc
          rw [h_eq] at h_pos; nlinarith
        simp [h_ab, h_not_bc]
      · have h_ab_nonneg : a * b ≥ 0 := not_lt.mp h_ab
        have h_bc : b * c < 0 := by
          by_contra! h; have h_nonneg : (a * b) * (b * c) ≥ 0 := mul_nonneg h_ab_nonneg h
          rw [h_eq] at h_nonneg; nlinarith
        simp [h_ab, h_bc]
    calc
      signChanges (a :: b :: c :: rest) = (if a * b < 0 then 1 else 0) + signChanges (b :: c :: rest) :=
        signChanges_cons_nonzero a b (c :: rest) ha hb
      _ = (if a * b < 0 then 1 else 0) + ((if b * c < 0 then 1 else 0) + signChanges (c :: rest)) := by
        rw [signChanges_cons_nonzero b c rest hb hc]
      _ = ((if a * b < 0 then 1 else 0) + (if b * c < 0 then 1 else 0)) + signChanges (c :: rest) := by omega
      _ = 1 + signChanges (c :: rest) := by rw [h_triple_val]

lemma eval_remainder_at_root (a b : ℝ[X]) (r : ℝ) (hb : b.eval r = 0) : (a % b).eval r = a.eval r := by
  rw [Polynomial.mod_def]
  by_cases hb0 : b = 0; · subst hb0; simp
  · have hmonic : Monic (b * C ((leadingCoeff b)⁻¹)) := by
      have hlc : leadingCoeff b ≠ 0 := leadingCoeff_ne_zero.mpr hb0
      rw [Monic, leadingCoeff_mul, leadingCoeff_C]; simp [hlc]
    have hzero : (b * C ((leadingCoeff b)⁻¹)).eval r = 0 := by simp [hb]
    rw [Polynomial.modByMonic_eq_sub_mul_div a (b * C ((leadingCoeff b)⁻¹))]; simp [hzero]

lemma nonzero_near (q : ℝ[X]) (r : ℝ) (hq : q.eval r ≠ 0) : ∃ ε > 0, ∀ x, |x - r| < ε → q.eval x ≠ 0 := by
  have hcont : Continuous (fun x : ℝ => q.eval x) := Polynomial.continuous q
  have h_open : IsOpen {x | q.eval x ≠ 0} := by
    have : {x | q.eval x ≠ 0} = (fun x : ℝ => q.eval x)⁻¹' ({0} : Set ℝ)ᶜ := by ext x; simp
    rw [this]; exact IsOpen.preimage hcont (by exact isOpen_compl_singleton)
  have h_mem : r ∈ {x | q.eval x ≠ 0} := hq
  have h_nhds : {x | q.eval x ≠ 0} ∈ 𝓝 r := h_open.mem_nhds h_mem
  rcases Metric.mem_nhds_iff.mp h_nhds with ⟨ε, hε, hball⟩
  refine ⟨ε, hε, ?_⟩; intro x hx; apply hball; rw [Metric.mem_ball, Real.dist_eq]; exact hx

lemma sign_near (q : ℝ[X]) (r : ℝ) (hq : q.eval r > 0) : ∃ ε > 0, ∀ x, |x - r| < ε → q.eval x > 0 := by
  have hcont : Continuous (fun x : ℝ => q.eval x) := Polynomial.continuous q
  have h_open : IsOpen {x | q.eval x > 0} := by
    have : {x | q.eval x > 0} = (fun x : ℝ => q.eval x)⁻¹' (Set.Ioi 0) := by ext x; simp
    rw [this]; exact IsOpen.preimage hcont isOpen_Ioi
  have h_mem : r ∈ {x | q.eval x > 0} := hq
  have h_nhds : {x | q.eval x > 0} ∈ 𝓝 r := h_open.mem_nhds h_mem
  rcases Metric.mem_nhds_iff.mp h_nhds with ⟨ε, hε, hball⟩
  refine ⟨ε, hε, ?_⟩; intro x hx; apply hball; rw [Metric.mem_ball, Real.dist_eq]; exact hx

lemma sign_near_neg (q : ℝ[X]) (r : ℝ) (hq : q.eval r < 0) : ∃ ε > 0, ∀ x, |x - r| < ε → q.eval x < 0 := by
  have hpos : (-q).eval r > 0 := by simpa using hq
  have h := sign_near (-q) r hpos; rcases h with ⟨ε, hε, h⟩
  refine ⟨ε, hε, λ x hx => ?_⟩; have : (-q).eval x > 0 := h x hx; simpa using this

lemma sign_constant_ac (a c : ℝ[X]) (r : ℝ) (ha : a.eval r ≠ 0) (hc : c.eval r ≠ 0) (h_ac : a.eval r * c.eval r < 0) :
    ∃ ε > 0, ∀ x, |x - r| < ε → (a.eval x) * (c.eval x) < 0 := by
  rcases em (a.eval r > 0) with (ha_pos | ha_notpos)
  · have ha_pos' : a.eval r > 0 := ha_pos; have hc_neg : c.eval r < 0 := by nlinarith
    rcases sign_near a r ha_pos' with ⟨ε_a, hε_a, ha_near⟩
    rcases sign_near_neg c r hc_neg with ⟨ε_c, hε_c, hc_near⟩
    let ε := min ε_a ε_c; have hε_pos : ε > 0 := lt_min_iff.mpr ⟨hε_a, hε_c⟩
    refine ⟨ε, hε_pos, λ x hx => ?_⟩
    have hx_a : |x - r| < ε_a := lt_of_lt_of_le hx (min_le_left _ _)
    have hx_c : |x - r| < ε_c := lt_of_lt_of_le hx (min_le_right _ _)
    nlinarith [ha_near x hx_a, hc_near x hx_c]
  · have ha_neg : a.eval r < 0 := by
      have : a.eval r ≤ 0 := le_of_not_gt ha_notpos; exact lt_of_le_of_ne this ha
    have hc_pos : c.eval r > 0 := by nlinarith
    rcases sign_near_neg a r ha_neg with ⟨ε_a, hε_a, ha_near⟩
    rcases sign_near c r hc_pos with ⟨ε_c, hε_c, hc_near⟩
    let ε := min ε_a ε_c; have hε_pos : ε > 0 := lt_min_iff.mpr ⟨hε_a, hε_c⟩
    refine ⟨ε, hε_pos, λ x hx => ?_⟩
    have hx_a : |x - r| < ε_a := lt_of_lt_of_le hx (min_le_left _ _)
    have hx_c : |x - r| < ε_c := lt_of_lt_of_le hx (min_le_right _ _)
    nlinarith [ha_near x hx_a, hc_near x hx_c]

lemma factor_theorem_with_deriv (p : ℝ[X]) (r : ℝ) (hp0 : p.eval r = 0) : ∃ q : ℝ[X], p = (X - C r) * q ∧ q.eval r = (derivative p).eval r := by
  have hdiv : (X - C r) ∣ p := Polynomial.dvd_iff_isRoot.mpr hp0
  rcases hdiv with ⟨q, h⟩
  have hcalc : q.eval r = (derivative p).eval r := by
    have hderiv : derivative p = q + (X - C r) * derivative q := by
      rw [h]; rw [derivative_mul]; simp
    calc q.eval r = (q + (X - C r) * derivative q).eval r := by simp
      _ = (derivative p).eval r := by rw [hderiv]
  exact ⟨q, h, hcalc⟩

lemma eval_derivative_ne_zero_of_squarefree_root (p : ℝ[X]) (hp : Squarefree p) (r : ℝ) (hr : p.eval r = 0) : 
    p.derivative.eval r ≠ 0 := by
  have hsep : p.Separable := ((PerfectField.separable_iff_squarefree (K := ℝ) (g := p)).mpr hp)
  rcases ((Polynomial.separable_def p).mp hsep) with ⟨a, b, h⟩
  have h_eval : (a * p + b * derivative p).eval r = 1 := by rw [h, Polynomial.eval_one]
  have h_eval' : (a * p + b * derivative p).eval r = a.eval r * p.eval r + b.eval r * (derivative p).eval r := by
    simp [Polynomial.eval_add, Polynomial.eval_mul]
  rw [h_eval'] at h_eval; rw [hr] at h_eval; simp at h_eval
  intro hzero; rw [hzero] at h_eval; simp at h_eval