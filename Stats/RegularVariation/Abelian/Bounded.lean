module

/-
  Karamata's Abelian theorem.

  ## Stats.RegularVariation.Abelian.Bounded — bounded-L Abelian theorem.

  Proves the Abelian theorem under a bounded-L assumption
  (`m ≤ L ≤ M` eventually with `0 < m`), strictly stronger than
  the paper's strong-Pareto Result 1.

  See `Stats/RegularVariation/Abelian.lean` for the umbrella.
-/
public import Stats.RegularVariation.Abelian.Basic

@[expose] public section

set_option maxHeartbeats 800000

open Real Set MeasureTheory Filter Topology

namespace TailOptionPricing

/-! ### Karamata's Abelian theorem (bounded-`L` case). -/

/-- **Karamata's Abelian theorem (bounded-`L` case).**  Bounded-`L` form
    of BGT 1.5.11 specialised to `s ↦ L(s) · s^(-α)`.  For `α > 1` and any
    measurable, slowly-varying `L` that is eventually bounded between two
    positive constants `m ≤ M`,
        `∫_K^∞ L(s) · s^(-α) ds  /  (L(K) · K^(1-α))  →  1 / (α - 1)`
    as `K → ∞`.

    This is strictly stronger than the strong-Pareto Result 1 (Eq. 2):
    Eq. (2) is the special case `L = l^α` (constant), in which the
    asymptotic equivalence holds with strict equality.

    *Proof.*  After the substitution `s = K · u`, the LHS equals
        `∫_1^∞ (L(K·u) / L(K)) · u^(-α) du`.
    By the slowly-varying property, the integrand converges pointwise to
    `u^(-α)`.  The bounded-`L` hypothesis gives the dominating function
    `(M/m) · u^(-α)`, integrable on `(1, ∞)` since `α > 1`.  Dominated
    convergence then yields the limit `∫_1^∞ u^(-α) du = 1/(α-1)`. -/
theorem callPriceSV_asymptotic_of_bounded
    {L : ℝ → ℝ} {α m M : ℝ} (hα : 1 < α) (hm : 0 < m)
    (hL_meas : Measurable L)
    (hL : IsSlowlyVarying L)
    (hL_lb : ∀ᶠ s in atTop, m ≤ L s)
    (hL_ub : ∀ᶠ s in atTop, L s ≤ M) :
    Tendsto (fun K => callPriceSV L α K / (L K * K ^ (1 - α))) atTop
      (𝓝 (1 / (α - 1))) := by
  -- Set up parameters.
  have hmM : m ≤ M := by
    rcases (hL_lb.and hL_ub).exists with ⟨_, hl, hu⟩; linarith
  have hM_pos : 0 < M := lt_of_lt_of_le hm hmM
  have hMm_pos : 0 < M / m := div_pos hM_pos hm
  -- Anchor T : eventual lower/upper bounds, K ≥ 1.
  obtain ⟨T_lb, hT_lb_at⟩ := Filter.eventually_atTop.mp hL_lb
  obtain ⟨T_ub, hT_ub_at⟩ := Filter.eventually_atTop.mp hL_ub
  set T := max (max T_lb T_ub) 1 with hT_def
  have hT_ge_lb : T_lb ≤ T :=
    le_trans (le_max_left _ _) (le_max_left _ _)
  have hT_ge_ub : T_ub ≤ T :=
    le_trans (le_max_right _ _) (le_max_left _ _)
  have hT_ge_one : (1 : ℝ) ≤ T := le_max_right _ _
  have hT_pos : (0 : ℝ) < T := lt_of_lt_of_le zero_lt_one hT_ge_one
  have h_lb : ∀ s, T ≤ s → m ≤ L s := fun s hs =>
    hT_lb_at s (le_trans hT_ge_lb hs)
  have h_ub : ∀ s, T ≤ s → L s ≤ M := fun s hs =>
    hT_ub_at s (le_trans hT_ge_ub hs)
  have h_pos : ∀ s, T ≤ s → 0 < L s := fun s hs =>
    lt_of_lt_of_le hm (h_lb s hs)
  -- DCT setup: F K u := (L(K*u) / L(K)) * u^(-α) on Ioi 1.
  set f : ℝ → ℝ := fun u => u ^ (-α) with hf_def
  set F : ℝ → ℝ → ℝ := fun K u => (L (K * u) / L K) * u ^ (-α) with hF_def
  set bound : ℝ → ℝ := fun u => (M / m) * u ^ (-α) with hbound_def
  -- (a) Bound is integrable on Ioi 1 (since α > 1).
  have h_rpow_int : IntegrableOn (fun u : ℝ => u ^ (-α)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
  have h_bound_int : Integrable bound (volume.restrict (Ioi 1)) := by
    rw [hbound_def]
    exact h_rpow_int.const_mul (M / m)
  -- (b) ∫_Ioi 1, f = 1/(α-1).
  have h_neg_α_lt : -α < -1 := by linarith
  have h_int_f : ∫ u in Ioi (1 : ℝ), u ^ (-α) = 1 / (α - 1) := by
    rw [integral_Ioi_rpow_of_lt h_neg_α_lt zero_lt_one, Real.one_rpow]
    have hα1_ne : (α - 1 : ℝ) ≠ 0 := ne_of_gt (by linarith)
    have h_one_α_ne : ((-α + 1) : ℝ) ≠ 0 := ne_of_lt (by linarith)
    field_simp
    ring
  -- (c) Pointwise limit a.e. u in Ioi 1.
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
  -- (d) Eventually bounded.
  have h_bound : ∀ᶠ K in atTop, ∀ᵐ u ∂(volume.restrict (Ioi (1 : ℝ))),
      ‖F K u‖ ≤ bound u := by
    filter_upwards [eventually_ge_atTop T] with K hK_ge_T
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Filter.Eventually.of_forall (fun u hu => ?_)
    have hu_ge_one : (1 : ℝ) ≤ u := le_of_lt hu
    have hu_pos : 0 < u := lt_of_lt_of_le zero_lt_one hu_ge_one
    have hK_pos : 0 < K := lt_of_lt_of_le hT_pos hK_ge_T
    have hK_le : K ≤ K * u := by nlinarith [hu_ge_one, hK_pos]
    have hT_le_K : T ≤ K := hK_ge_T
    have hT_le_Ku : T ≤ K * u := le_trans hT_le_K hK_le
    have hLK_pos : 0 < L K := h_pos K hT_le_K
    have hLKu_pos : 0 < L (K * u) := h_pos (K * u) hT_le_Ku
    have hLKu_le : L (K * u) ≤ M := h_ub (K * u) hT_le_Ku
    have hm_le_LK : m ≤ L K := h_lb K hT_le_K
    have hu_pow_nn : 0 ≤ u ^ (-α) := Real.rpow_nonneg hu_pos.le _
    have h_ratio_nn : 0 ≤ L (K * u) / L K := div_nonneg hLKu_pos.le hLK_pos.le
    have h_ratio_le : L (K * u) / L K ≤ M / m := by
      rw [div_le_div_iff₀ hLK_pos hm]
      calc L (K * u) * m ≤ M * m :=
            mul_le_mul_of_nonneg_right hLKu_le hm.le
        _ ≤ M * L K := mul_le_mul_of_nonneg_left hm_le_LK hM_pos.le
    show ‖(L (K * u) / L K) * u ^ (-α)‖ ≤ (M / m) * u ^ (-α)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h_ratio_nn hu_pow_nn)]
    exact mul_le_mul_of_nonneg_right h_ratio_le hu_pow_nn
  -- (e) Strong measurability of F K (on Ioi 1, where u^(-α) is continuous).
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
  -- (f) DCT yields the integral limit.
  have h_dct :
      Tendsto (fun K => ∫ u in Ioi (1 : ℝ), F K u) atTop
        (𝓝 (∫ u in Ioi (1 : ℝ), f u)) :=
    tendsto_integral_filter_of_dominated_convergence bound h_meas h_bound
      h_bound_int h_lim
  rw [show (∫ u in Ioi (1 : ℝ), f u) = 1 / (α - 1) from h_int_f] at h_dct
  -- (g) Bridge the LHS expression with ∫ F K u.
  have h_bridge : ∀ᶠ K in atTop,
      callPriceSV L α K / (L K * K ^ (1 - α)) = ∫ u in Ioi (1 : ℝ), F K u := by
    filter_upwards [eventually_ge_atTop T] with K hK_ge_T
    have hK_pos : 0 < K := lt_of_lt_of_le hT_pos hK_ge_T
    have hT_le_K : T ≤ K := hK_ge_T
    have hLK_pos : 0 < L K := h_pos K hT_le_K
    have hLK_ne : L K ≠ 0 := hLK_pos.ne'
    have hK_pow_pos : 0 < K ^ (1 - α) := Real.rpow_pos_of_pos hK_pos _
    have hK_pow_ne : K ^ (1 - α) ≠ 0 := hK_pow_pos.ne'
    rw [callPriceSV_substitution hK_pos]
    -- K^(1-α) * I / (L K * K^(1-α)) = I / L K = ∫ (1/L K) (L(K·) · ·^(-α)).
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

/-- **Slowly-varying Result 1 / Eq. (3) (asymptotic ratio, bounded-`L`).**
    For `α > 1` and any slowly-varying, measurable, eventually-bounded `L`,
    the call-price ratio at strikes `c·K` and `K → ∞` satisfies
        `C(c · K) / C(K)  →  c^(1-α)`.
    The slowly-varying factor `L` cancels in the limit (since `L(c·K)/L(K) → 1`),
    so the ratio depends only on `α` and `c`.  Strong Pareto (constant `L`) is
    a special case in which this asymptotic equivalence holds with strict
    equality at every `K ≥ l/c` (Eq. 3).

    *Proof.*  Decompose the ratio as
        `C(c·K)/C(K) = [B(K)/A(K)] · [L(c·K)/L(K)] · c^(1-α)`,
    where `A(K) := C(K)/(L(K)·K^(1-α))` and `B(K) := C(c·K)/(L(c·K)·(c·K)^(1-α))`.
    The Abelian theorem gives `A(K), B(K) → 1/(α-1) ≠ 0`, so `B/A → 1`; the SV
    property gives `L(c·K)/L(K) → 1`; the constant factor `c^(1-α)` is
    untouched.  Product of the limits is `c^(1-α)`. -/
theorem callPriceSV_ratio_asymptotic_of_bounded
    {L : ℝ → ℝ} {α m M c : ℝ} (hα : 1 < α) (hm : 0 < m) (hc : 0 < c)
    (hL_meas : Measurable L)
    (hL : IsSlowlyVarying L)
    (hL_lb : ∀ᶠ s in atTop, m ≤ L s)
    (hL_ub : ∀ᶠ s in atTop, L s ≤ M) :
    Tendsto (fun K => callPriceSV L α (c * K) / callPriceSV L α K) atTop
      (𝓝 (c ^ (1 - α))) := by
  have h_asy_K := callPriceSV_asymptotic_of_bounded hα hm hL_meas hL hL_lb hL_ub
  -- Lift the asymptotic along K ↦ c·K.
  have h_lift : Tendsto (fun K : ℝ => c * K) atTop atTop :=
    Tendsto.const_mul_atTop hc tendsto_id
  have h_asy_cK :
      Tendsto (fun K =>
        callPriceSV L α (c * K) / (L (c * K) * (c * K) ^ (1 - α))) atTop
      (𝓝 (1 / (α - 1))) := h_asy_K.comp h_lift
  -- L(c·K)/L(K) → 1 (SV property).
  have h_L_ratio : Tendsto (fun K : ℝ => L (c * K) / L K) atTop (𝓝 1) := by
    have h := hL c hc
    refine h.congr (fun K => ?_)
    rw [mul_comm]
  -- α-1 ≠ 0; 1/(α-1) ≠ 0.
  have hα1_pos : 0 < α - 1 := by linarith
  have hα1_ne : (α - 1 : ℝ) ≠ 0 := hα1_pos.ne'
  have h_lim_pos : (0 : ℝ) < 1 / (α - 1) := by positivity
  have h_lim_ne : (1 / (α - 1) : ℝ) ≠ 0 := h_lim_pos.ne'
  -- B(K)/A(K) → (1/(α-1)) / (1/(α-1)) = 1.
  have h_BA : Tendsto (fun K : ℝ =>
      (callPriceSV L α (c * K) / (L (c * K) * (c * K) ^ (1 - α))) /
      (callPriceSV L α K / (L K * K ^ (1 - α)))) atTop (𝓝 1) := by
    have h := h_asy_cK.div h_asy_K h_lim_ne
    rwa [div_self h_lim_ne] at h
  -- Combined limit: 1 · 1 · c^(1-α) = c^(1-α).
  have h_combined :
      Tendsto (fun K : ℝ =>
        (callPriceSV L α (c * K) / (L (c * K) * (c * K) ^ (1 - α))) /
        (callPriceSV L α K / (L K * K ^ (1 - α))) *
        (L (c * K) / L K) * c ^ (1 - α)) atTop
      (𝓝 (c ^ (1 - α))) := by
    have h1 := (h_BA.mul h_L_ratio).mul (tendsto_const_nhds (x := c ^ (1 - α)))
    rw [show (1 : ℝ) * 1 * c ^ (1 - α) = c ^ (1 - α) from by ring] at h1
    exact h1
  -- Bridge: combined K = callPriceSV L α (c·K) / callPriceSV L α K eventually.
  refine h_combined.congr' ?_
  -- Set up the eventual hypotheses.
  obtain ⟨T_lb, hT_lb_at⟩ := Filter.eventually_atTop.mp hL_lb
  obtain ⟨T_ub, hT_ub_at⟩ := Filter.eventually_atTop.mp hL_ub
  set T := max (max T_lb T_ub) 1 with hT_def
  have hT_ge_lb : T_lb ≤ T :=
    le_trans (le_max_left _ _) (le_max_left _ _)
  have hT_ge_ub : T_ub ≤ T :=
    le_trans (le_max_right _ _) (le_max_left _ _)
  have hT_ge_one : (1 : ℝ) ≤ T := le_max_right _ _
  have hT_pos : (0 : ℝ) < T := lt_of_lt_of_le zero_lt_one hT_ge_one
  have h_pos_L : ∀ s, T ≤ s → 0 < L s := fun s hs => by
    have h1 : m ≤ L s := hT_lb_at s (le_trans hT_ge_lb hs); linarith
  have h_C_pos_K : ∀ᶠ K in atTop,
      0 < callPriceSV L α K / (L K * K ^ (1 - α)) :=
    h_asy_K.eventually (eventually_gt_nhds h_lim_pos)
  have h_C_pos_cK : ∀ᶠ K in atTop,
      0 < callPriceSV L α (c * K) / (L (c * K) * (c * K) ^ (1 - α)) :=
    h_asy_cK.eventually (eventually_gt_nhds h_lim_pos)
  filter_upwards [eventually_ge_atTop T,
                  h_lift.eventually (eventually_ge_atTop T),
                  h_C_pos_K, h_C_pos_cK]
    with K hK_ge_T hcK_ge_T hC_K_ratio_pos hC_cK_ratio_pos
  have hK_pos : 0 < K := lt_of_lt_of_le hT_pos hK_ge_T
  have hcK_pos : 0 < c * K := mul_pos hc hK_pos
  have hLK_pos : 0 < L K := h_pos_L K hK_ge_T
  have hLcK_pos : 0 < L (c * K) := h_pos_L (c * K) hcK_ge_T
  have hLK_ne : L K ≠ 0 := hLK_pos.ne'
  have hLcK_ne : L (c * K) ≠ 0 := hLcK_pos.ne'
  have hK_pow_pos : 0 < K ^ (1 - α) := Real.rpow_pos_of_pos hK_pos _
  have hcK_pow_pos : 0 < (c * K) ^ (1 - α) := Real.rpow_pos_of_pos hcK_pos _
  have hK_pow_ne : K ^ (1 - α) ≠ 0 := hK_pow_pos.ne'
  have hcK_pow_ne : (c * K) ^ (1 - α) ≠ 0 := hcK_pow_pos.ne'
  have hLK_pow_ne : L K * K ^ (1 - α) ≠ 0 := mul_ne_zero hLK_ne hK_pow_ne
  have hLcK_pow_ne : L (c * K) * (c * K) ^ (1 - α) ≠ 0 :=
    mul_ne_zero hLcK_ne hcK_pow_ne
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
