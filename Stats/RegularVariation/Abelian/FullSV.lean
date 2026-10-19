module

/-
  Karamata's Abelian theorem.

  ## Stats.RegularVariation.Abelian.FullSV — full SV form.

  Karamata's Abelian theorem for general slowly-varying `L`,
  upgrading the bounded-L variant via the Potter bound.

  See `Stats/RegularVariation/Abelian.lean` for the umbrella.
-/
public import Stats.RegularVariation.Abelian.Potter

@[expose] public section

set_option maxHeartbeats 800000

open Real Set MeasureTheory Filter Topology

namespace TailOptionPricing

/-! ### Karamata's Abelian theorem, full SV form. -/

/-- **Karamata's Abelian theorem (full SV form).**  BGT 1.5.11 specialised
    to `s ↦ L(s) · s^(-α)`.  For `α > 1` and any measurable, slowly-varying,
    eventually-positive `L` (no boundedness required),
        `∫_K^∞ L(s) · s^(-α) ds  /  (L(K) · K^(1-α))  →  1 / (α - 1)`
    as `K → ∞`.

    Strict generalisation of `callPriceSV_asymptotic_of_bounded`: covers
    e.g. `L(s) = log s`, `(log s)^k`, etc., where `L` is unbounded.

    *Proof.*  Same DCT skeleton as the bounded case, with the dominator
    `(M/m) · u^(-α)` replaced by `(1+δ) · u^(δ-α)` derived from the
    *global* Potter bound; pick `δ < α-1` so the dominator is integrable
    on `(1, ∞)`. -/
theorem callPriceSV_asymptotic
    {L : ℝ → ℝ} {α : ℝ} (hα : 1 < α)
    (hL_meas : Measurable L)
    (hL : IsSlowlyVarying L)
    (hL_pos : ∀ᶠ s in atTop, 0 < L s) :
    Tendsto (fun K => callPriceSV L α K / (L K * K ^ (1 - α))) atTop
      (𝓝 (1 / (α - 1))) := by
  -- Pick δ ∈ (0, α-1) for global Potter and integrability.
  have hα1_pos : 0 < α - 1 := by linarith
  set δ := (α - 1) / 2 with hδ_def
  have hδ_pos : 0 < δ := by rw [hδ_def]; linarith
  have hδ_lt_α1 : δ < α - 1 := by rw [hδ_def]; linarith
  -- Global Potter upper bound.
  obtain ⟨T_pot, hT_pot_pos, hT_pot⟩ :=
    hL.global_potter_upper hL_pos hL_meas hδ_pos
  -- Eventual positivity threshold.
  obtain ⟨T_pos_th, hT_pos_at⟩ := Filter.eventually_atTop.mp hL_pos
  set T := max (max T_pot T_pos_th) 1 with hT_def
  have hT_ge_pot : T_pot ≤ T :=
    le_trans (le_max_left _ _) (le_max_left _ _)
  have hT_ge_pos : T_pos_th ≤ T :=
    le_trans (le_max_right _ _) (le_max_left _ _)
  have hT_ge_one : (1 : ℝ) ≤ T := le_max_right _ _
  have hT_pos : (0 : ℝ) < T := lt_of_lt_of_le zero_lt_one hT_ge_one
  have h_pos : ∀ s, T ≤ s → 0 < L s := fun s hs =>
    hT_pos_at s (le_trans hT_ge_pos hs)
  -- DCT setup.
  set f : ℝ → ℝ := fun u => u ^ (-α) with hf_def
  set F : ℝ → ℝ → ℝ := fun K u => (L (K * u) / L K) * u ^ (-α) with hF_def
  set bound : ℝ → ℝ := fun u => (1 + δ) * u ^ (δ - α) with hbound_def
  -- Bound integrable on Ioi 1: δ-α < -1.
  have h_bound_lt : δ - α < -1 := by linarith
  have h_rpow_int : IntegrableOn (fun u : ℝ => u ^ (δ - α)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt h_bound_lt zero_lt_one
  have h_bound_int : Integrable bound (volume.restrict (Ioi 1)) := by
    rw [hbound_def]
    exact h_rpow_int.const_mul (1 + δ)
  -- ∫_Ioi 1, f = 1/(α-1).
  have h_neg_α_lt : -α < -1 := by linarith
  have h_int_f : ∫ u in Ioi (1 : ℝ), u ^ (-α) = 1 / (α - 1) := by
    rw [integral_Ioi_rpow_of_lt h_neg_α_lt zero_lt_one, Real.one_rpow]
    have hα1_ne : (α - 1 : ℝ) ≠ 0 := ne_of_gt (by linarith)
    have h_one_α_ne : ((-α + 1) : ℝ) ≠ 0 := ne_of_lt (by linarith)
    field_simp
    ring
  -- Pointwise limit a.e.
  have h_lim : ∀ᵐ u ∂(volume.restrict (Ioi (1 : ℝ))),
      Tendsto (fun K => F K u) atTop (𝓝 (f u)) := by
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Filter.Eventually.of_forall (fun u hu => ?_)
    have hu_pos : 0 < u := lt_of_lt_of_le zero_lt_one (le_of_lt hu)
    have h_ratio : Tendsto (fun K : ℝ => L (K * u) / L K) atTop (𝓝 1) := hL u hu_pos
    have h_to : Tendsto (fun K : ℝ =>
        (L (K * u) / L K) * u ^ (-α)) atTop (𝓝 (1 * u ^ (-α))) :=
      h_ratio.mul tendsto_const_nhds
    simpa [hF_def, hf_def, one_mul] using h_to
  -- Eventually bounded via global Potter.
  have h_bound : ∀ᶠ K in atTop, ∀ᵐ u ∂(volume.restrict (Ioi (1 : ℝ))),
      ‖F K u‖ ≤ bound u := by
    filter_upwards [eventually_ge_atTop T] with K hK_ge_T
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Filter.Eventually.of_forall (fun u hu => ?_)
    have hu_ge_one : (1 : ℝ) ≤ u := le_of_lt hu
    have hu_pos : 0 < u := lt_of_lt_of_le zero_lt_one hu_ge_one
    have hK_ge_pot : T_pot ≤ K := le_trans hT_ge_pot hK_ge_T
    have hK_pos : 0 < K := lt_of_lt_of_le hT_pos hK_ge_T
    have hLK_pos : 0 < L K := h_pos K hK_ge_T
    have hKu_ge_K : K ≤ K * u := by nlinarith
    have hKu_ge_T : T ≤ K * u := le_trans hK_ge_T hKu_ge_K
    have hLKu_pos : 0 < L (K * u) := h_pos (K * u) hKu_ge_T
    have h_potter : L (K * u) / L K ≤ (1 + δ) * u ^ δ :=
      hT_pot K hK_ge_pot u hu_ge_one
    have h_ratio_nn : 0 ≤ L (K * u) / L K := div_nonneg hLKu_pos.le hLK_pos.le
    have hu_pow_neg_nn : 0 ≤ u ^ (-α) := Real.rpow_nonneg hu_pos.le _
    have h_pow : u ^ δ * u ^ (-α) = u ^ (δ - α) := by
      rw [← Real.rpow_add hu_pos]
      ring_nf
    show ‖(L (K * u) / L K) * u ^ (-α)‖ ≤ (1 + δ) * u ^ (δ - α)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h_ratio_nn hu_pow_neg_nn)]
    calc (L (K * u) / L K) * u ^ (-α)
        ≤ (1 + δ) * u ^ δ * u ^ (-α) :=
          mul_le_mul_of_nonneg_right h_potter hu_pow_neg_nn
      _ = (1 + δ) * (u ^ δ * u ^ (-α)) := by ring
      _ = (1 + δ) * u ^ (δ - α) := by rw [h_pow]
  -- Strong measurability (same as bounded case).
  have h_meas : ∀ᶠ K in atTop, AEStronglyMeasurable (F K)
      (volume.restrict (Ioi (1 : ℝ))) := by
    refine Filter.Eventually.of_forall (fun K => ?_)
    refine AEStronglyMeasurable.mul ?_ ?_
    · refine Measurable.aestronglyMeasurable ?_
      exact (hL_meas.comp (measurable_const_mul K)).div_const (L K)
    · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
      intro u hu
      refine ContinuousAt.continuousWithinAt ?_
      apply continuousAt_rpow_const
      left
      exact (lt_of_lt_of_le zero_lt_one (le_of_lt hu)).ne'
  -- DCT.
  have h_dct :
      Tendsto (fun K => ∫ u in Ioi (1 : ℝ), F K u) atTop
        (𝓝 (∫ u in Ioi (1 : ℝ), f u)) :=
    tendsto_integral_filter_of_dominated_convergence bound h_meas h_bound
      h_bound_int h_lim
  rw [show (∫ u in Ioi (1 : ℝ), f u) = 1 / (α - 1) from h_int_f] at h_dct
  -- Bridge.
  have h_bridge : ∀ᶠ K in atTop,
      callPriceSV L α K / (L K * K ^ (1 - α)) = ∫ u in Ioi (1 : ℝ), F K u := by
    filter_upwards [eventually_ge_atTop T] with K hK_ge_T
    have hK_pos : 0 < K := lt_of_lt_of_le hT_pos hK_ge_T
    have hLK_pos : 0 < L K := h_pos K hK_ge_T
    have hLK_ne : L K ≠ 0 := hLK_pos.ne'
    have hK_pow_pos : 0 < K ^ (1 - α) := Real.rpow_pos_of_pos hK_pos _
    have hK_pow_ne : K ^ (1 - α) ≠ 0 := hK_pow_pos.ne'
    rw [callPriceSV_substitution hK_pos]
    rw [show K ^ (1 - α) * (∫ x in Ioi (1 : ℝ), L (K * x) * x ^ (-α)) /
            (L K * K ^ (1 - α)) =
          (1 / L K) * ∫ x in Ioi (1 : ℝ), L (K * x) * x ^ (-α) from by
      field_simp]
    rw [show (1 : ℝ) / L K * ∫ x in Ioi (1 : ℝ), L (K * x) * x ^ (-α) =
          ∫ x in Ioi (1 : ℝ), (1 / L K) * (L (K * x) * x ^ (-α)) from by
      rw [integral_const_mul]]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x _
    show (1 / L K) * (L (K * x) * x ^ (-α)) = L (K * x) / L K * x ^ (-α)
    field_simp
  refine h_dct.congr' ?_
  filter_upwards [h_bridge] with K hK
  exact hK.symm

/-- **Slowly-varying Result 1 / Eq. (3) (asymptotic ratio, full SV form).**
    For `α > 1` and any measurable, slowly-varying, eventually-positive `L`
    (no boundedness required), the call-price ratio at strikes `c·K, K → ∞`
    satisfies `C(c · K) / C(K) → c^(1-α)`.

    Strict generalisation of `callPriceSV_ratio_asymptotic_of_bounded`. -/
theorem callPriceSV_ratio_asymptotic
    {L : ℝ → ℝ} {α c : ℝ} (hα : 1 < α) (hc : 0 < c)
    (hL_meas : Measurable L)
    (hL : IsSlowlyVarying L)
    (hL_pos : ∀ᶠ s in atTop, 0 < L s) :
    Tendsto (fun K => callPriceSV L α (c * K) / callPriceSV L α K) atTop
      (𝓝 (c ^ (1 - α))) := by
  have h_asy_K := callPriceSV_asymptotic hα hL_meas hL hL_pos
  have h_lift : Tendsto (fun K : ℝ => c * K) atTop atTop :=
    Tendsto.const_mul_atTop hc tendsto_id
  have h_asy_cK :
      Tendsto (fun K =>
        callPriceSV L α (c * K) / (L (c * K) * (c * K) ^ (1 - α))) atTop
      (𝓝 (1 / (α - 1))) := h_asy_K.comp h_lift
  have h_L_ratio : Tendsto (fun K : ℝ => L (c * K) / L K) atTop (𝓝 1) := by
    have h := hL c hc
    refine h.congr (fun K => ?_)
    rw [mul_comm]
  have hα1_pos : 0 < α - 1 := by linarith
  have hα1_ne : (α - 1 : ℝ) ≠ 0 := hα1_pos.ne'
  have h_lim_pos : (0 : ℝ) < 1 / (α - 1) := by positivity
  have h_lim_ne : (1 / (α - 1) : ℝ) ≠ 0 := h_lim_pos.ne'
  have h_BA : Tendsto (fun K : ℝ =>
      (callPriceSV L α (c * K) / (L (c * K) * (c * K) ^ (1 - α))) /
      (callPriceSV L α K / (L K * K ^ (1 - α)))) atTop (𝓝 1) := by
    have h := h_asy_cK.div h_asy_K h_lim_ne
    rwa [div_self h_lim_ne] at h
  have h_combined :
      Tendsto (fun K : ℝ =>
        (callPriceSV L α (c * K) / (L (c * K) * (c * K) ^ (1 - α))) /
        (callPriceSV L α K / (L K * K ^ (1 - α))) *
        (L (c * K) / L K) * c ^ (1 - α)) atTop
      (𝓝 (c ^ (1 - α))) := by
    have h1 := (h_BA.mul h_L_ratio).mul (tendsto_const_nhds (x := c ^ (1 - α)))
    rw [show (1 : ℝ) * 1 * c ^ (1 - α) = c ^ (1 - α) from by ring] at h1
    exact h1
  refine h_combined.congr' ?_
  obtain ⟨T_pos_th, hT_pos_at⟩ := Filter.eventually_atTop.mp hL_pos
  have hL_lift : Tendsto (fun K : ℝ => c * K) atTop atTop :=
    Tendsto.const_mul_atTop hc tendsto_id
  have h_C_pos_K : ∀ᶠ K in atTop,
      0 < callPriceSV L α K / (L K * K ^ (1 - α)) :=
    h_asy_K.eventually (eventually_gt_nhds h_lim_pos)
  have h_C_pos_cK : ∀ᶠ K in atTop,
      0 < callPriceSV L α (c * K) / (L (c * K) * (c * K) ^ (1 - α)) :=
    h_asy_cK.eventually (eventually_gt_nhds h_lim_pos)
  filter_upwards [eventually_gt_atTop (0 : ℝ),
                  eventually_ge_atTop T_pos_th,
                  hL_lift.eventually (eventually_ge_atTop T_pos_th),
                  h_C_pos_K, h_C_pos_cK]
    with K hK_pos hK_ge_th hcK_ge_th hC_K_ratio_pos hC_cK_ratio_pos
  have hcK_pos : 0 < c * K := mul_pos hc hK_pos
  have hLK_pos : 0 < L K := hT_pos_at K hK_ge_th
  have hLcK_pos : 0 < L (c * K) := hT_pos_at (c * K) hcK_ge_th
  have hLK_ne : L K ≠ 0 := hLK_pos.ne'
  have hLcK_ne : L (c * K) ≠ 0 := hLcK_pos.ne'
  have hK_pow_pos : 0 < K ^ (1 - α) := Real.rpow_pos_of_pos hK_pos _
  have hcK_pow_pos : 0 < (c * K) ^ (1 - α) := Real.rpow_pos_of_pos hcK_pos _
  have hK_pow_ne : K ^ (1 - α) ≠ 0 := hK_pow_pos.ne'
  have hcK_pow_ne : (c * K) ^ (1 - α) ≠ 0 := hcK_pow_pos.ne'
  have hC_K_ne : callPriceSV L α K ≠ 0 := by
    intro h_eq
    rw [h_eq, zero_div] at hC_K_ratio_pos
    exact lt_irrefl 0 hC_K_ratio_pos
  have hC_cK_ne : callPriceSV L α (c * K) ≠ 0 := by
    intro h_eq
    rw [h_eq, zero_div] at hC_cK_ratio_pos
    exact lt_irrefl 0 hC_cK_ratio_pos
  show (callPriceSV L α (c * K) / (L (c * K) * (c * K) ^ (1 - α))) /
       (callPriceSV L α K / (L K * K ^ (1 - α))) *
       (L (c * K) / L K) * c ^ (1 - α) =
       callPriceSV L α (c * K) / callPriceSV L α K
  rw [show ((c * K) ^ (1 - α) : ℝ) = c ^ (1 - α) * K ^ (1 - α) from
        Real.mul_rpow hc.le hK_pos.le]
  field_simp


end TailOptionPricing
