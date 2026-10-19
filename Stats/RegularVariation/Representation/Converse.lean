module

/-
  Karamata's representation theorem for slowly varying functions.

  ## Stats.RegularVariation.Representation.Converse — predicate and converse direction.

  Defines `IsKaramataRepresentation` and proves the easy direction:
  if `L` admits a Karamata representation, then `L` is slowly
  varying.

  See `Stats/RegularVariation/Representation.lean` for the umbrella.
-/
public import Stats.RegularVariation.UCT
public import Stats.RegularVariation.Karamata
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

@[expose] public section

set_option maxHeartbeats 800000

open Real Set Filter Topology Asymptotics MeasureTheory intervalIntegral

namespace TailOptionPricing

/-! ### The representation predicate. -/

/-- `L` admits a *Karamata representation* with anchor `T`, asymptotic
    constant `c₀`, slowly-varying part `c`, and decay `ε`.  The
    `hε_div_int` field ensures that `ε(u)/u` is integrable on every
    compact `[T, s]`, so that the integral in `hL_repr` is the genuine
    Lebesgue integral and additive identities like `∫_T^{t·x} = ∫_T^t +
    ∫_t^{t·x}` hold. -/
structure IsKaramataRepresentation
    (L : ℝ → ℝ) (T c₀ : ℝ) (c ε : ℝ → ℝ) : Prop where
  protected hT : 0 < T
  protected hε_div_int : ∀ s, T ≤ s →
    IntervalIntegrable (fun u => ε u / u) volume T s
  protected hc₀_pos : 0 < c₀
  protected hc_lim : Tendsto c atTop (𝓝 c₀)
  protected hε_lim : Tendsto ε atTop (𝓝 0)
  protected hL_repr : ∀ s, T ≤ s →
    L s = c s * Real.exp (∫ u in T..s, ε u / u)

/-! ### Converse direction: representation ⇒ slowly varying.

    Given the representation, factor `L(t·x)/L(t) = c(t·x)/c(t) · exp(R(t,x))`
    where `R(t, x) := ∫_t^{t·x} ε(u)/u du`.  The `c`-ratio converges to 1.
    For `R`, the substitution `u = t·v` shows `R(t, x) = ∫_1^x ε(t·v)/v dv`,
    which is bounded by `(sup_{v ∈ [1,x]} |ε(t·v)|)·log x → 0`. -/

/-- **The integral `∫_t^{t·x} ε(u)/u du` vanishes** as `t → ∞`, for any
    measurable `ε → 0` and `x > 0`. -/
private lemma karamata_inner_integral_tendsto_zero
    {ε : ℝ → ℝ}
    (hε_lim : Tendsto ε atTop (𝓝 0))
    {x : ℝ} (hx_pos : 0 < x) :
    Tendsto (fun t : ℝ => ∫ u in t..(t * x), ε u / u) atTop (𝓝 0) := by
  -- Constant Mx = |x − 1| / min(1, x).
  set Mx : ℝ := |x - 1| / min 1 x with hMx_def
  have hmin_pos : 0 < min 1 x := lt_min zero_lt_one hx_pos
  have hMx_nn : 0 ≤ Mx := by rw [hMx_def]; positivity
  rw [Metric.tendsto_atTop]
  intro η hη_pos
  set K : ℝ := Mx + 1 with hK_def
  have hK_pos : 0 < K := by rw [hK_def]; linarith
  set δ : ℝ := η / (2 * K) with hδ_def
  have hδ_pos : 0 < δ := by rw [hδ_def]; positivity
  -- ε → 0: eventually |ε u| ≤ δ.
  rw [Metric.tendsto_atTop] at hε_lim
  obtain ⟨S, hS⟩ := hε_lim δ hδ_pos
  have h_eps_le : ∀ u, S ≤ u → |ε u| ≤ δ := fun u hu => by
    have := hS u hu; rw [Real.dist_eq, sub_zero] at this; exact this.le
  set T₀ : ℝ := max (max S (S / x)) 1 with hT₀_def
  refine ⟨T₀, fun t ht => ?_⟩
  have ht_ge_S : S ≤ t :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) ht
  have ht_ge_Sx : S / x ≤ t :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) ht
  have ht_ge_one : (1 : ℝ) ≤ t := le_trans (le_max_right _ _) ht
  have ht_pos : 0 < t := lt_of_lt_of_le zero_lt_one ht_ge_one
  have htx_pos : 0 < t * x := mul_pos ht_pos hx_pos
  have htx_ge_S : S ≤ t * x := by
    rw [div_le_iff₀ hx_pos] at ht_ge_Sx; linarith
  have h_min_pos : 0 < min t (t * x) := lt_min ht_pos htx_pos
  have h_min_ge_S : S ≤ min t (t * x) := le_min ht_ge_S htx_ge_S
  -- Constant bound on |ε u / u| on uIoc t (t·x).
  have h_const_bound : ∀ u ∈ Set.Ioc (min t (t*x)) (max t (t*x)),
      ‖ε u / u‖ ≤ δ / min t (t*x) := by
    intro u hu
    obtain ⟨hu_lo, _⟩ := hu
    have h_u_pos : 0 < u := lt_trans h_min_pos hu_lo
    have h_u_ge_S : S ≤ u := le_trans h_min_ge_S hu_lo.le
    have h_eps_u : |ε u| ≤ δ := h_eps_le u h_u_ge_S
    have h_inv_le : (1 : ℝ) / u ≤ 1 / min t (t*x) :=
      one_div_le_one_div_of_le h_min_pos hu_lo.le
    rw [Real.norm_eq_abs, abs_div, abs_of_pos h_u_pos]
    calc |ε u| / u
        = |ε u| * (1 / u) := by ring
      _ ≤ δ * (1 / min t (t*x)) :=
          mul_le_mul h_eps_u h_inv_le (by positivity) hδ_pos.le
      _ = δ / min t (t * x) := by ring
  -- Apply the constant bound.
  have h_norm : ‖∫ u in t..(t * x), ε u / u‖ ≤
      (δ / min t (t * x)) * |t * x - t| :=
    intervalIntegral.norm_integral_le_of_norm_le_const h_const_bound
  rw [Real.norm_eq_abs] at h_norm
  -- |t·x − t| = t · |x − 1|.
  have h_abs_diff : |t * x - t| = t * |x - 1| := by
    rw [show t * x - t = t * (x - 1) from by ring,
        abs_mul, abs_of_pos ht_pos]
  -- min(t, t·x) = t · min(1, x).
  have h_min_eq : min t (t * x) = t * min 1 x := by
    rcases le_total 1 x with hx1 | hx1
    · have h_t_le_tx : t ≤ t * x := by nlinarith [ht_pos]
      rw [min_eq_left hx1, min_eq_left h_t_le_tx, mul_one]
    · have h_tx_le_t : t * x ≤ t := by nlinarith [ht_pos]
      rw [min_eq_right hx1, min_eq_right h_tx_le_t]
  rw [h_abs_diff, h_min_eq] at h_norm
  rw [Real.dist_eq, sub_zero]
  have h_t_ne : (t : ℝ) ≠ 0 := ht_pos.ne'
  have h_min1x_ne : min 1 x ≠ 0 := hmin_pos.ne'
  have hK_ne : K ≠ 0 := hK_pos.ne'
  have h_simp1 : δ / (t * min 1 x) * (t * |x - 1|) = δ * Mx := by
    rw [hMx_def]; field_simp
  have h_simp2 : δ * K = η / 2 := by
    rw [hδ_def]; field_simp
  calc |∫ u in t..(t * x), ε u / u|
      ≤ δ / (t * min 1 x) * (t * |x - 1|) := h_norm
    _ = δ * Mx := h_simp1
    _ ≤ δ * K := mul_le_mul_of_nonneg_left
        (by rw [hK_def]; linarith) hδ_pos.le
    _ = η / 2 := h_simp2
    _ < η := by linarith

/-- **Converse direction.**  A function admitting a Karamata representation
    is slowly varying. -/
theorem IsKaramataRepresentation.isSlowlyVarying
    {L : ℝ → ℝ} {T c₀ : ℝ} {c ε : ℝ → ℝ}
    (h : IsKaramataRepresentation L T c₀ c ε) :
    IsSlowlyVarying L := by
  intro x hx_pos
  -- Eventually `c t > c₀ / 2 > 0`.
  have hc₀_half : 0 < c₀ / 2 := by linarith [h.hc₀_pos]
  have h_c_pos : ∀ᶠ t in atTop, 0 < c t := by
    have := h.hc_lim.eventually (Metric.ball_mem_nhds c₀ hc₀_half)
    filter_upwards [this] with t ht
    rw [Real.dist_eq] at ht
    have h_lo := (abs_lt.mp ht).1
    linarith
  have h_lift_x : Tendsto (fun t : ℝ => t * x) atTop atTop :=
    Filter.tendsto_id.atTop_mul_const hx_pos
  have h_c_pos_x : ∀ᶠ t in atTop, 0 < c (t * x) := h_lift_x.eventually h_c_pos
  have h_T_le : ∀ᶠ t in atTop, T ≤ t := eventually_ge_atTop T
  have h_T_le_x : ∀ᶠ t in atTop, T ≤ t * x := h_lift_x.eventually h_T_le
  -- c-ratio → 1.
  have h_c_lim_x : Tendsto (fun t => c (t * x)) atTop (𝓝 c₀) :=
    h.hc_lim.comp h_lift_x
  have h_c_ratio : Tendsto (fun t => c (t * x) / c t) atTop (𝓝 1) := by
    have h_div : Tendsto (fun t => c (t * x) / c t) atTop (𝓝 (c₀ / c₀)) :=
      h_c_lim_x.div h.hc_lim h.hc₀_pos.ne'
    rwa [div_self h.hc₀_pos.ne'] at h_div
  -- Inner integral identity.
  have h_diff_eq : ∀ᶠ t in atTop,
      (∫ u in T..(t * x), ε u / u) - (∫ u in T..t, ε u / u) =
        ∫ u in t..(t * x), ε u / u := by
    filter_upwards [h_T_le, h_T_le_x] with t ht_T ht_Tx
    have h_int_T_t := h.hε_div_int t ht_T
    have h_int_T_tx := h.hε_div_int (t * x) ht_Tx
    have h_int_t_tx : IntervalIntegrable (fun u => ε u / u) volume t (t * x) := by
      rcases le_total t (t * x) with htx | htx
      · -- T ≤ t ≤ t·x. uIcc t (t·x) = [t, t·x] ⊆ [T, t·x].
        refine h_int_T_tx.mono_set ?_
        rw [Set.uIcc_of_le htx, Set.uIcc_of_le ht_Tx]
        exact Set.Icc_subset_Icc ht_T (le_refl _)
      · -- T ≤ t·x ≤ t. uIcc t (t·x) = [t·x, t] ⊆ [T, t].
        refine h_int_T_t.mono_set ?_
        rw [Set.uIcc_of_ge htx, Set.uIcc_of_le ht_T]
        exact Set.Icc_subset_Icc ht_Tx (le_refl _)
    -- ∫_T^t + ∫_t^{t·x} = ∫_T^{t·x}.
    have := intervalIntegral.integral_add_adjacent_intervals h_int_T_t h_int_t_tx
    linarith
  -- Integral diff → 0.
  have h_int_diff_zero : Tendsto
      (fun t => (∫ u in T..(t * x), ε u / u) - ∫ u in T..t, ε u / u)
      atTop (𝓝 0) := by
    apply Tendsto.congr' (h_diff_eq.mono fun t ht => ht.symm)
    exact karamata_inner_integral_tendsto_zero h.hε_lim hx_pos
  -- exp(∫ - ∫) → 1.
  have h_exp_diff : Tendsto
      (fun t => Real.exp ((∫ u in T..(t * x), ε u / u) - ∫ u in T..t, ε u / u))
      atTop (𝓝 1) := by
    rw [show (1 : ℝ) = Real.exp 0 from Real.exp_zero.symm]
    exact (Real.continuous_exp.tendsto _).comp h_int_diff_zero
  -- L-ratio = c-ratio · exp(diff) eventually.
  have h_factor : ∀ᶠ t in atTop,
      L (t * x) / L t =
        c (t * x) / c t *
          Real.exp ((∫ u in T..(t * x), ε u / u) - ∫ u in T..t, ε u / u) := by
    filter_upwards [h_T_le, h_T_le_x] with t hT_t hT_tx
    rw [h.hL_repr t hT_t, h.hL_repr (t * x) hT_tx]
    rw [mul_div_mul_comm, ← Real.exp_sub]
  -- Combine.
  have h_full : Tendsto
      (fun t => c (t * x) / c t *
          Real.exp ((∫ u in T..(t * x), ε u / u) - ∫ u in T..t, ε u / u))
      atTop (𝓝 (1 * 1)) :=
    Tendsto.mul h_c_ratio h_exp_diff
  rw [mul_one] at h_full
  exact h_full.congr' (h_factor.mono fun t ht => ht.symm)


end TailOptionPricing
