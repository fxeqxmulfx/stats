/-
  Karamata's Abelian theorem.

  ## Stats.RegularVariation.Abelian.Potter — global Potter bound.

  The Potter bound `L(t)/L(s) ≤ C · (t/s)^δ` for any `δ > 0`,
  used to upgrade the bounded-L Abelian theorem to the full
  slowly-varying setting.

  See `Stats/RegularVariation/Abelian.lean` for the umbrella.
-/
import Stats.RegularVariation.Abelian.Bounded

set_option maxHeartbeats 800000

open Real Set MeasureTheory Filter Topology

namespace TailOptionPricing

/-! ### Global Potter bound and the full-SV Karamata Abelian theorem.

    The bounded-`L` form above suffices for `L` confined to a compact range
    `[m, M] ⊂ (0, ∞)`.  For the full slowly-varying form (covering e.g.
    `L(s) = log s`), we need a uniform bound `L(K·u)/L(K) ≤ (1+δ)·u^δ` for
    `u ≥ 1` — Potter's *global* bound.  Standard derivation: substitute the
    Karamata representation `L(s) = c(s)·exp(∫_T^s ε(u)/u du)`, factor the
    ratio as `c(K·u)/c(K) · exp(∫_K^{K·u} ε)`, and bound each factor using
    `c → c₀` and `ε → 0`. -/

/-- **Global Potter bound (upper).**  For any slowly-varying, eventually
    positive, measurable `L` and any `δ > 0`, eventually for `K` large the
    ratio `L(K·u)/L(K)` is bounded above by `(1+δ)·u^δ` *uniformly* for
    `u ≥ 1`.  Strict generalisation of the local Potter bounds (which are
    over compact intervals only).

    *Proof.*  Apply Karamata's representation `L(s) = c(s)·exp(∫_T^s ε/u)`.
    Pick `η := δ/(2+δ)`; then `(1+η)/(1-η) = 1+δ`.  For `K` large,
    `c(K·u)/c(K) ≤ (1+δ)` (eventual `c → c₀ > 0`) and
    `|∫_K^{K·u} ε(v)/v dv| ≤ δ·log u` (eventual `|ε| ≤ δ`); hence
    `L(K·u)/L(K) ≤ (1+δ)·exp(δ·log u) = (1+δ)·u^δ`. -/
theorem IsSlowlyVarying.global_potter_upper
    {L : ℝ → ℝ} (hL : IsSlowlyVarying L)
    (hL_pos : ∀ᶠ s in atTop, 0 < L s) (hL_meas : Measurable L)
    {δ : ℝ} (hδ_pos : 0 < δ) :
    ∃ T₀ > 0, ∀ K, T₀ ≤ K → ∀ u, 1 ≤ u → L (K * u) / L K ≤ (1 + δ) * u ^ δ := by
  obtain ⟨T, hT_pos, c₀, c, ε, hRep⟩ :=
    hL.karamata_representation hL_pos hL_meas
  -- Pick η := δ/(2+δ) ∈ (0, 1); then (1+η)/(1-η) = 1+δ.
  set η_const : ℝ := δ / (2 + δ) with hη_def
  have h2δ_pos : (0 : ℝ) < 2 + δ := by linarith
  have hη_pos : 0 < η_const := by rw [hη_def]; positivity
  have hη_lt_one : η_const < 1 := by
    rw [hη_def, div_lt_one h2δ_pos]; linarith
  have h_one_minus_η_pos : 0 < 1 - η_const := by linarith
  have hη_ratio : (1 + η_const) / (1 - η_const) = 1 + δ := by
    rw [hη_def]
    have : (2 + δ : ℝ) ≠ 0 := h2δ_pos.ne'
    field_simp
    ring
  -- Eventually `|c(s) − c₀| ≤ η·c₀` and `|ε(s)| ≤ δ`.
  have hηc₀_pos : 0 < η_const * c₀ := mul_pos hη_pos hRep.hc₀_pos
  obtain ⟨T_c, hT_c⟩ : ∃ T_c, ∀ s, T_c ≤ s → |c s - c₀| ≤ η_const * c₀ := by
    have h_evt : ∀ᶠ s in atTop, dist (c s) c₀ < η_const * c₀ :=
      hRep.hc_lim.eventually (Metric.ball_mem_nhds c₀ hηc₀_pos)
    rcases Filter.eventually_atTop.mp h_evt with ⟨T_c, hT_c⟩
    refine ⟨T_c, fun s hs => ?_⟩
    have h := hT_c s hs
    rw [Real.dist_eq] at h
    exact h.le
  obtain ⟨T_ε, hT_ε⟩ : ∃ T_ε, ∀ s, T_ε ≤ s → |ε s| ≤ δ := by
    have h_evt : ∀ᶠ s in atTop, dist (ε s) 0 < δ :=
      hRep.hε_lim.eventually (Metric.ball_mem_nhds 0 hδ_pos)
    rcases Filter.eventually_atTop.mp h_evt with ⟨T_ε, hT_ε⟩
    refine ⟨T_ε, fun s hs => ?_⟩
    have h := hT_ε s hs
    rw [Real.dist_eq, sub_zero] at h
    exact h.le
  -- Anchor T₀ := max(T, T_c, T_ε, 1).
  set T₀ : ℝ := max (max T (max T_c T_ε)) 1 with hT₀_def
  have hT₀_ge_T : T ≤ T₀ := le_trans (le_max_left _ _) (le_max_left _ _)
  have hT₀_ge_Tc : T_c ≤ T₀ :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_left _ _)
  have hT₀_ge_Tε : T_ε ≤ T₀ :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_left _ _)
  have hT₀_ge_one : (1 : ℝ) ≤ T₀ := le_max_right _ _
  have hT₀_pos : (0 : ℝ) < T₀ := lt_of_lt_of_le zero_lt_one hT₀_ge_one
  refine ⟨T₀, hT₀_pos, fun K hK_ge u hu_ge_one => ?_⟩
  have hK_ge_T : T ≤ K := le_trans hT₀_ge_T hK_ge
  have hK_ge_Tc : T_c ≤ K := le_trans hT₀_ge_Tc hK_ge
  have hK_ge_Tε : T_ε ≤ K := le_trans hT₀_ge_Tε hK_ge
  have hK_pos : 0 < K := lt_of_lt_of_le hT₀_pos hK_ge
  have hu_pos : 0 < u := lt_of_lt_of_le zero_lt_one hu_ge_one
  have hKu : K ≤ K * u := by nlinarith [hu_ge_one, hK_pos]
  have hKu_pos : 0 < K * u := mul_pos hK_pos hu_pos
  have hKu_ge_T : T ≤ K * u := le_trans hK_ge_T hKu
  have hKu_ge_Tc : T_c ≤ K * u := le_trans hK_ge_Tc hKu
  have hKu_ge_Tε : T_ε ≤ K * u := le_trans hK_ge_Tε hKu
  -- c(K), c(K·u) ∈ [c₀(1−η), c₀(1+η)], hence positive.
  have h_c_bound_K : c₀ * (1 - η_const) ≤ c K ∧ c K ≤ c₀ * (1 + η_const) := by
    have h_abs := hT_c K hK_ge_Tc
    rw [abs_le] at h_abs
    refine ⟨?_, ?_⟩
    · nlinarith [hRep.hc₀_pos, h_abs.1]
    · nlinarith [hRep.hc₀_pos, h_abs.2]
  have h_c_bound_Ku : c₀ * (1 - η_const) ≤ c (K * u) ∧ c (K * u) ≤ c₀ * (1 + η_const) := by
    have h_abs := hT_c (K * u) hKu_ge_Tc
    rw [abs_le] at h_abs
    refine ⟨?_, ?_⟩
    · nlinarith [hRep.hc₀_pos, h_abs.1]
    · nlinarith [hRep.hc₀_pos, h_abs.2]
  have hc_K_pos : 0 < c K := by
    have : 0 < c₀ * (1 - η_const) := mul_pos hRep.hc₀_pos h_one_minus_η_pos
    linarith [h_c_bound_K.1]
  have hc_Ku_pos : 0 < c (K * u) := by
    have : 0 < c₀ * (1 - η_const) := mul_pos hRep.hc₀_pos h_one_minus_η_pos
    linarith [h_c_bound_Ku.1]
  -- Substitute the representation.
  have h_repr_K : L K = c K * Real.exp (∫ v in T..K, ε v / v) :=
    hRep.hL_repr K hK_ge_T
  have h_repr_Ku : L (K * u) =
      c (K * u) * Real.exp (∫ v in T..(K * u), ε v / v) :=
    hRep.hL_repr (K * u) hKu_ge_T
  -- Integrability and adjacent split: ∫_T^K + ∫_K^{Ku} = ∫_T^{Ku}.
  have h_int_TK := hRep.hε_div_int K hK_ge_T
  have h_int_TKu := hRep.hε_div_int (K * u) hKu_ge_T
  have h_int_KKu : IntervalIntegrable (fun v => ε v / v) volume K (K * u) := by
    refine h_int_TKu.mono_set ?_
    rw [Set.uIcc_of_le hKu, Set.uIcc_of_le hKu_ge_T]
    exact Set.Icc_subset_Icc hK_ge_T (le_refl _)
  have h_split : (∫ v in T..K, ε v / v) + (∫ v in K..(K * u), ε v / v) =
      ∫ v in T..(K * u), ε v / v :=
    intervalIntegral.integral_add_adjacent_intervals h_int_TK h_int_KKu
  -- Bound `|∫_K^{Ku} ε(v)/v dv| ≤ δ · log u`.
  have h_int_K_Ku_bound : |∫ v in K..(K * u), ε v / v| ≤ δ * Real.log u := by
    have h_div_int : IntervalIntegrable (fun v : ℝ => δ / v) volume K (K * u) := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [Set.uIcc_of_le hKu]
      intro v hv
      have hv_pos : 0 < v := lt_of_lt_of_le hK_pos hv.1
      refine ContinuousAt.continuousWithinAt ?_
      exact ContinuousAt.div continuousAt_const continuousAt_id hv_pos.ne'
    have h_norm_ae : ∀ᵐ v ∂volume, v ∈ Set.Ioc K (K * u) →
        ‖ε v / v‖ ≤ δ / v := by
      refine Filter.Eventually.of_forall (fun v hv => ?_)
      have hv_pos : 0 < v := lt_of_lt_of_le hK_pos hv.1.le
      have h_v_ge_Tε : T_ε ≤ v := le_trans hK_ge_Tε hv.1.le
      have h_ε_v : |ε v| ≤ δ := hT_ε v h_v_ge_Tε
      rw [Real.norm_eq_abs, abs_div, abs_of_pos hv_pos]
      exact div_le_div_of_nonneg_right h_ε_v hv_pos.le
    have h_norm_int : ‖∫ v in K..(K * u), ε v / v‖ ≤ ∫ v in K..(K * u), δ / v :=
      intervalIntegral.norm_integral_le_of_norm_le hKu h_norm_ae h_div_int
    have h_int_eq : ∫ v in K..(K * u), δ / v = δ * Real.log u := by
      have h_eq : (fun v : ℝ => δ / v) = fun v => δ * (1 / v) := by
        funext v; rw [mul_one_div]
      rw [h_eq, intervalIntegral.integral_const_mul,
          integral_one_div_of_pos hK_pos hKu_pos]
      congr 1
      rw [show K * u / K = u from by field_simp]
    rw [h_int_eq, Real.norm_eq_abs] at h_norm_int
    exact h_norm_int
  -- L(K·u)/L(K) = (c(K·u)/c(K)) · exp(∫_K^{Ku} ε/v).
  have h_ratio_eq : L (K * u) / L K =
      c (K * u) / c K * Real.exp (∫ v in K..(K * u), ε v / v) := by
    rw [h_repr_K, h_repr_Ku]
    rw [mul_div_mul_comm, ← Real.exp_sub]
    congr 1
    congr 1
    linarith [h_split]
  -- exp(∫) ≤ u^δ.
  have h_exp_le : Real.exp (∫ v in K..(K * u), ε v / v) ≤ u ^ δ := by
    have h_le : ∫ v in K..(K * u), ε v / v ≤ δ * Real.log u :=
      le_trans (le_abs_self _) h_int_K_Ku_bound
    calc Real.exp (∫ v in K..(K * u), ε v / v)
        ≤ Real.exp (δ * Real.log u) := Real.exp_le_exp.mpr h_le
      _ = u ^ δ := by rw [Real.rpow_def_of_pos hu_pos, mul_comm]
  -- c(K·u)/c(K) ≤ 1 + δ via (1+η)/(1-η) = 1+δ.
  have h_c_ratio_le : c (K * u) / c K ≤ 1 + δ := by
    rw [div_le_iff₀ hc_K_pos]
    calc c (K * u) ≤ c₀ * (1 + η_const) := h_c_bound_Ku.2
      _ = c₀ * ((1 + η_const) / (1 - η_const) * (1 - η_const)) := by
          rw [div_mul_cancel₀ _ h_one_minus_η_pos.ne']
      _ = c₀ * ((1 + δ) * (1 - η_const)) := by rw [hη_ratio]
      _ = (1 + δ) * (c₀ * (1 - η_const)) := by ring
      _ ≤ (1 + δ) * c K :=
          mul_le_mul_of_nonneg_left h_c_bound_K.1 (by linarith)
  -- Combine.
  rw [h_ratio_eq]
  have h_u_pow_pos : 0 < u ^ δ := Real.rpow_pos_of_pos hu_pos _
  have h_c_ratio_pos : 0 < c (K * u) / c K := div_pos hc_Ku_pos hc_K_pos
  calc c (K * u) / c K * Real.exp (∫ v in K..(K * u), ε v / v)
      ≤ c (K * u) / c K * u ^ δ :=
        mul_le_mul_of_nonneg_left h_exp_le h_c_ratio_pos.le
    _ ≤ (1 + δ) * u ^ δ :=
        mul_le_mul_of_nonneg_right h_c_ratio_le h_u_pow_pos.le


end TailOptionPricing
