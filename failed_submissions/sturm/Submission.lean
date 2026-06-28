import ChallengeDeps
open LeanEval.Algebra
open Polynomial
open Set
open scoped Classical

namespace Submission

-- ============================================================
-- Helper lemmas for signChanges
-- ============================================================

lemma signChanges_nil : signChanges ([] : List ℝ) = 0 := by
  unfold signChanges; simp

lemma signChanges_singleton (a : ℝ) : signChanges [a] = 0 := by
  unfold signChanges; simp

lemma signChanges_cons_nonzero (a b : ℝ) (rest : List ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    signChanges (a :: b :: rest) = (if a * b < 0 then 1 else 0) + signChanges (b :: rest) := by
  unfold signChanges
  have hfilter : (a :: b :: rest).filter (· ≠ 0) = a :: (b :: rest).filter (· ≠ 0) := by simp [ha]
  have hfilter' : (b :: rest).filter (· ≠ 0) = b :: rest.filter (· ≠ 0) := by simp [hb]
  rw [hfilter, hfilter']
  have htail : (a :: b :: rest.filter (· ≠ 0)).tail = b :: rest.filter (· ≠ 0) := by simp
  rw [htail]
  set tail := rest.filter (· ≠ 0) with htail_def
  have hzip : (a :: b :: tail).zip (b :: tail) = (a, b) :: ((b :: tail).zip tail) := by simp
  rw [hzip]
  by_cases h_ab : a * b < 0
  · simp [h_ab]
  · simp [h_ab]

lemma signChanges_cons_cons_nonzero (a b : ℝ) (rest : List ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    signChanges (a :: b :: rest) = (if a * b < 0 then 1 else 0) + signChanges (b :: rest) :=
  signChanges_cons_nonzero a b rest ha hb

lemma signChanges_pair (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) : signChanges [a, b] = if a * b < 0 then 1 else 0 := by
  calc
    signChanges [a, b] = (if a * b < 0 then 1 else 0) + signChanges [b] := by
      simpa using signChanges_cons_cons_nonzero a b [] ha hb
    _ = (if a * b < 0 then 1 else 0) + 0 := by simp [signChanges_singleton]
    _ = if a * b < 0 then 1 else 0 := by simp

lemma signChanges_triple_opposite (a b c : ℝ) (hac : a * c < 0) : signChanges [a, b, c] = 1 := by
  have ha0 : a ≠ 0 := by intro hzero; subst hzero; nlinarith
  have hc0 : c ≠ 0 := by intro hzero; subst hzero; nlinarith
  by_cases hb0 : b = 0
  · subst hb0; simp [ha0, hc0, hac]
  · have hb0' : b ≠ 0 := hb0
    have h1 : signChanges [a, b, c] = (if a * b < 0 then 1 else 0) + signChanges [b, c] := by
      simpa using signChanges_cons_cons_nonzero a b [c] ha0 hb0'
    have h2 : signChanges [b, c] = (if b * c < 0 then 1 else 0) :=
      signChanges_pair b c hb0' hc0
    rw [h1, h2]
    have hsq_pos : b ^ 2 > 0 := sq_pos_of_ne_zero hb0'
    have hprod_lt0 : (a * b) * (b * c) < 0 := by
      calc
        (a * b) * (b * c) = (a * c) * (b ^ 2) := by ring
        _ < 0 := mul_neg_of_neg_of_pos hac hsq_pos
    have h_opp : (a * b < 0 ∧ 0 ≤ b * c) ∨ (0 ≤ a * b ∧ b * c < 0) := by
      by_cases hab : a * b < 0
      · left; refine ⟨hab, ?_⟩; nlinarith
      · have hab' : 0 ≤ a * b := by nlinarith
        have hbc_lt0 : b * c < 0 := by nlinarith
        right; exact ⟨hab', hbc_lt0⟩
    rcases h_opp with (⟨hab, hbc⟩ | ⟨hab, hbc⟩)
    · simp [hab, hbc]
    · simp [hab, hbc]

lemma signChanges_cons_triple (a b c : ℝ) (rest : List ℝ) (ha : a ≠ 0) (hc : c ≠ 0) (h_ac : a * c < 0) :
    signChanges (a :: b :: c :: rest) = 1 + signChanges (c :: rest) := by
  by_cases hb0 : b = 0
  · subst hb0
    calc
      signChanges (a :: 0 :: c :: rest) = signChanges (a :: c :: rest) := by
        dsimp [signChanges]; simp [ha, hc]
      _ = (if a * c < 0 then 1 else 0) + signChanges (c :: rest) :=
        signChanges_cons_nonzero a c rest ha hc
      _ = 1 + signChanges (c :: rest) := by simp [h_ac]
  · have hb : b ≠ 0 := hb0
    calc
      signChanges (a :: b :: c :: rest) = (if a * b < 0 then 1 else 0) + signChanges (b :: c :: rest) :=
        signChanges_cons_nonzero a b (c :: rest) ha hb
      _ = (if a * b < 0 then 1 else 0) + ((if b * c < 0 then 1 else 0) + signChanges (c :: rest)) := by
        rw [signChanges_cons_nonzero b c rest hb hc]
      _ = ((if a * b < 0 then 1 else 0) + (if b * c < 0 then 1 else 0)) + signChanges (c :: rest) := by omega
      _ = 1 + signChanges (c :: rest) := by
        have h_triple : (if a * b < 0 then (1 : ℕ) else 0) + (if b * c < 0 then (1 : ℕ) else 0) = 1 := by
          have h_sq_pos : b * b > 0 := mul_self_pos.mpr hb
          have h_eq : (a * b) * (b * c) = (a * c) * (b * b) := by ring
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
        rw [h_triple]

lemma triple_sign_lemma (a b c : ℝ) (hac : a * c < 0) (hb : b ≠ 0) :
    ((if a * b < 0 then 1 else 0 : ℕ) + (if b * c < 0 then 1 else 0 : ℕ)) = 1 := by
  have ha_ne_zero : a ≠ 0 := by intro hzero; subst hzero; nlinarith
  have hc_ne_zero : c ≠ 0 := by intro hzero; subst hzero; nlinarith
  have ha_sign : a > 0 ∨ a < 0 := lt_or_gt_of_ne ha_ne_zero.symm
  have hb_sign : b > 0 ∨ b < 0 := lt_or_gt_of_ne hb.symm
  rcases ha_sign with (ha_pos | ha_neg)
  · have hc_neg : c < 0 := by nlinarith
    rcases hb_sign with (hb_pos | hb_neg)
    · have h1 : ¬ (a * b < 0) := by nlinarith; have h2 : b * c < 0 := by nlinarith; simp [h1, h2]
    · have h1 : a * b < 0 := by nlinarith; have h2 : ¬ (b * c < 0) := by nlinarith; simp [h1, h2]
  · have hc_pos : c > 0 := by nlinarith
    rcases hb_sign with (hb_pos | hb_neg)
    · have h1 : a * b < 0 := by nlinarith; have h2 : ¬ (b * c < 0) := by nlinarith; simp [h1, h2]
    · have h1 : ¬ (a * b < 0) := by nlinarith; have h2 : b * c < 0 := by nlinarith; simp [h1, h2]

lemma signChanges_flip_first (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (l : List ℝ) :
    |(signChanges (a :: b :: l) : ℤ) - (signChanges ((-a) :: b :: l) : ℤ)| = 1 := by
  have ha' : -a ≠ 0 := by intro h; apply ha; nlinarith
  have h1 : signChanges (a :: b :: l) = (if a * b < 0 then 1 else 0) + signChanges (b :: l) :=
    signChanges_cons_cons_nonzero a b l ha hb
  have h2 : signChanges ((-a) :: b :: l) = (if (-a) * b < 0 then 1 else 0) + signChanges (b :: l) :=
    signChanges_cons_cons_nonzero (-a) b l ha' hb
  rw [h1, h2]
  have hprod : (-a) * b = -(a * b) := by ring; rw [hprod]
  have hz : a * b ≠ 0 := mul_ne_zero ha hb
  by_cases hneg : a * b < 0
  · have hpos : ¬(-(a * b) < 0) := by nlinarith; rw [if_pos hneg, if_neg hpos]; simp
  · have hge : a * b ≥ 0 := by nlinarith
    have hpos : a * b > 0 := lt_of_le_of_ne hge hz.symm
    have hneg' : -(a * b) < 0 := by nlinarith; rw [if_neg hneg, if_pos hneg']; simp

lemma signChanges_filter_eq (xs : List ℝ) : signChanges xs = signChanges (xs.filter (· ≠ 0)) := by
  unfold signChanges; simp

lemma signChanges_cons_zero (a : ℝ) (l : List ℝ) (ha : a ≠ 0) :
    signChanges (a :: 0 :: l) = signChanges (a :: l) := by
  unfold signChanges; simp [ha]

-- ============================================================
-- Polynomial lemmas
-- ============================================================

lemma hp_ne_zero (p : ℝ[X]) (hp : Squarefree p) : p ≠ 0 := by
  haveI : CharZero ℝ := by infer_instance
  haveI : PerfectField ℝ := PerfectField.ofCharZero
  have hsep : Separable p := by rw [PerfectField.separable_iff_squarefree]; exact hp
  exact hsep.ne_zero

lemma squarefree_imp_separable (p : ℝ[X]) (hp : Squarefree p) : Separable p := by
  haveI : CharZero ℝ := by infer_instance
  haveI : PerfectField ℝ := PerfectField.ofCharZero
  rw [PerfectField.separable_iff_squarefree]; exact hp

lemma eval_remainder_at_root (a b : ℝ[X]) (r : ℝ) (hb : b.eval r = 0) : (a % b).eval r = a.eval r := by
  have h := EuclideanDomain.mod_add_div a b
  apply_fun (·.eval r) at h
  simp [eval_add, eval_mul, hb] at h; exact h

lemma next_chain_entry_eval (a b : ℝ[X]) (r : ℝ) (hb : b.eval r = 0) : (-(a % b)).eval r = -(a.eval r) := by
  simp [eval_remainder_at_root a b r hb]

lemma squarefree_no_common_root (p : ℝ[X]) (hp : Squarefree p) (r : ℝ) (hr : p.eval r = 0) :
    (derivative p).eval r ≠ 0 := by
  have hsep : p.Separable := squarefree_imp_separable p hp
  have h_coprime : IsCoprime p (derivative p) := ((Polynomial.separable_def (f := p)).mp hsep)
  rcases h_coprime with ⟨a, b, h⟩
  have h_eval := congrArg (fun q => q.eval r) h
  simp [hr, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_one] at h_eval
  intro hzero; rw [hzero] at h_eval; simp at h_eval

lemma factor_theorem_with_deriv (p : ℝ[X]) (r : ℝ) (hr : p.eval r = 0) :
    ∃ q : ℝ[X], p = (X - C r) * q ∧ q.eval r = p.derivative.eval r := by
  have hroot : IsRoot p r := by rw [IsRoot, hr]
  have hdiv : (X - C r) ∣ p := (Polynomial.dvd_iff_isRoot).mpr hroot
  rcases hdiv with ⟨q, hp_eq⟩
  have hqeval : q.eval r = p.derivative.eval r := by
    calc
      q.eval r = (q + (X - C r) * derivative q).eval r := by simp
      _ = (derivative ((X - C r) * q)).eval r := by
        rw [derivative_mul, derivative_sub, derivative_X, derivative_C]; simp
      _ = (derivative p).eval r := by rw [hp_eq]
  refine ⟨q, hp_eq, hqeval⟩

lemma sturm_adjacent_opposite (f g : ℝ[X]) (r : ℝ) (hg : g.eval r = 0) (hf : f.eval r ≠ 0) :
    f.eval r * (-(f % g)).eval r < 0 := by
  have hmod : (f % g).eval r = f.eval r := eval_remainder_at_root f g r hg
  have hneg : (-(f % g)).eval r = -(f.eval r) := by simp [hmod]
  rw [hneg]
  have hsq : (f.eval r)^2 > 0 := sq_pos_of_ne_zero hf
  nlinarith

-- ============================================================
-- Continuity / sign constancy lemmas
-- ============================================================

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

lemma nonzero_near (q : ℝ[X]) (r : ℝ) (hq : q.eval r ≠ 0) : ∃ ε > 0, ∀ x, |x - r| < ε → q.eval x ≠ 0 := by
  have hcont : Continuous (q.eval : ℝ → ℝ) := Polynomial.continuous q
  have hcont_at : ContinuousAt (q.eval : ℝ → ℝ) r := hcont.continuousAt
  have hevent : ∀ᶠ x in nhds r, q.eval x ≠ 0 := hcont_at.tendsto.eventually_ne hq
  rcases Metric.mem_nhds_iff.mp hevent with ⟨ε, hε, hball⟩
  refine ⟨ε, hε, ?_⟩
  intro x hx_dist; apply hball; rw [Metric.mem_ball, Real.dist_eq]; exact hx_dist

lemma sign_constant_on_Ioo (q : ℝ[X]) (c d : ℝ) (hcd : c < d) (h_no_root : ∀ x ∈ Ioo c d, q.eval x ≠ 0) :
    (∀ x ∈ Ioo c d, q.eval x > 0) ∨ (∀ x ∈ Ioo c d, q.eval x < 0) := by
  have h_cont : Continuous (q.eval : ℝ → ℝ) := Polynomial.continuous q
  by_cases hpos : ∃ x ∈ Ioo c d, q.eval x > 0
  · rcases hpos with ⟨x, hx, hxpos⟩; refine Or.inl ?_
    intro y hy; by_contra! h_notpos
    have hy_nonzero : q.eval y ≠ 0 := h_no_root y hy
    have hy_neg : q.eval y < 0 := by
      have : q.eval y ≤ 0 := h_notpos; exact Ne.lt_of_le hy_nonzero this
    by_cases hxy : x < y
    · have h_cont_on : ContinuousOn (q.eval : ℝ → ℝ) (Icc x y) := h_cont.continuousOn
      have h0_in : (0 : ℝ) ∈ Ioo (q.eval y) (q.eval x) := by constructor <;> linarith
      have h_contains : Ioo (q.eval y) (q.eval x) ⊆ (q.eval : ℝ → ℝ) '' Ioo x y :=
        intermediate_value_Ioo' (by linarith) h_cont_on
      rcases h_contains h0_in with ⟨z, hz, hz0⟩
      apply h_no_root z; · rcases hz with ⟨hzx, hzy⟩; exact ⟨lt_of_lt_of_le hx.1 hzx.le, lt_of_le_of_lt hzy.le hy.2⟩
      · exact hz0
    · have hy_ne_x : y ≠ x := by intro h_eq; subst h_eq; linarith
      have hyx : y < x := by
        have hy_le_x : y ≤ x := by linarith
        exact Ne.lt_of_le hy_ne_x hy_le_x
      have h_cont_on : ContinuousOn (q.eval : ℝ → ℝ) (Icc y x) := h_cont.continuousOn
      have h0_in : (0 : ℝ) ∈ Ioo (q.eval y) (q.eval x) := by constructor <;> linarith
      have h_contains : Ioo (q.eval y) (q.eval x) ⊆ (q.eval : ℝ → ℝ) '' Ioo y x :=
        intermediate_value_Ioo (by linarith) h_cont_on
      rcases h_contains h0_in with ⟨z, hz, hz0⟩
      apply h_no_root z; · rcases hz with ⟨hzy, hzx⟩; exact ⟨lt_of_lt_of_le hy.1 hzy.le, lt_of_le_of_lt hzx.le hx.2⟩
      · exact hz0
  · refine Or.inr ?_
    intro y hy; have hy_nonzero : q.eval y ≠ 0 := h_no_root y hy
    have hy_nonpos : q.eval y ≤ 0 := by
      by_contra! hpos_y; exact hpos ⟨y, hy, hpos_y⟩
    exact Ne.lt_of_le hy_nonzero hy_nonpos

lemma sign_constant_ac (a c : ℝ[X]) (r : ℝ) (ha : a.eval r ≠ 0) (hc : c.eval r ≠ 0) (h_ac : a.eval r * c.eval r < 0) :
    ∃ ε > 0, ∀ x, |x - r| < ε → (a.eval x) * (c.eval x) < 0 := by
  rcases em (a.eval r > 0) with (ha_pos | ha_notpos)
  · have ha_pos' : a.eval r > 0 := ha_pos
    have hc_neg : c.eval r < 0 := by nlinarith
    rcases sign_near a r ha_pos' with ⟨ε_a, hε_a, ha_near⟩
    rcases sign_near_neg c r hc_neg with ⟨ε_c, hε_c, hc_near⟩
    let ε := min ε_a ε_c
    have hε_pos : ε > 0 := lt_min_iff.mpr ⟨hε_a, hε_c⟩
    refine ⟨ε, hε_pos, λ x hx => ?_⟩
    have hx_a : |x - r| < ε_a := lt_of_lt_of_le hx (min_le_left _ _)
    have hx_c : |x - r| < ε_c := lt_of_lt_of_le hx (min_le_right _ _)
    nlinarith [ha_near x hx_a, hc_near x hx_c]
  · have ha_neg : a.eval r < 0 := by
      have : a.eval r ≤ 0 := le_of_not_gt ha_notpos; exact lt_of_le_of_ne this ha
    have hc_pos : c.eval r > 0 := by nlinarith
    rcases sign_near_neg a r ha_neg with ⟨ε_a, hε_a, ha_near⟩
    rcases sign_near c r hc_pos with ⟨ε_c, hε_c, hc_near⟩
    let ε := min ε_a ε_c
    have hε_pos : ε > 0 := lt_min_iff.mpr ⟨hε_a, hε_c⟩
    refine ⟨ε, hε_pos, λ x hx => ?_⟩
    have hx_a : |x - r| < ε_a := lt_of_lt_of_le hx (min_le_left _ _)
    have hx_c : |x - r| < ε_c := lt_of_lt_of_le hx (min_le_right _ _)
    nlinarith [ha_near x hx_a, hc_near x hx_c]

-- ============================================================
-- Main theorem proof sketch
-- ============================================================

theorem sturm (p : ℝ[X]) (hp : Squarefree p) {a b : ℝ} (hab : a < b)
    (ha : p.eval a ≠ 0) (hb : p.eval b ≠ 0) :
    ((p.roots.toFinset).filter (fun x => a < x ∧ x < b)).card =
      sigma p a - sigma p b := by
  -- This is Sturm's theorem. The proof requires:
  -- 1. sigma_drop_at_simple_root: At each root r of p, sigma drops by exactly 1
  -- 2. sigma_constant_at_non_p_root: At points where p ≠ 0, sigma is locally constant
  -- 3. Induction on the number of roots of p in (a,b)
  -- 
  -- The critical lemmas sigma_drop_at_simple_root and sigma_constant_on_rootless_interval
  -- are partially developed in the SupportingLemmas directory.
  -- 
  -- For a complete proof, see the referenced Isabelle/HOL formalization (Eberl, AFP entry Sturm_Sequences)
  -- which formalizes the same theorem in the same distinct-root form.
  sorry

end Submission