/-
  Karamata's representation theorem for slowly varying functions.

  ## Stats.RegularVariation.Representation.Forward — SV ⇒ representation.

  The hard direction.  Following the BGT recipe
  (Bingham–Goldie–Teugels, *Regular Variation*, Theorem 1.3.1):

  1. Pass to additive coordinates `η(t) := log L(eᵗ)`.  Pointwise
     SV becomes `η(t + u) − η(t) → 0` for each `u`; Korevaar's
     measurable UCT makes this *uniform* in `u ∈ [0, 1]`.
  2. Smooth via the moving average `ξ(t) := ∫_t^{t+1} η`.
     Translation invariance gives `ξ(t) − ξ(T) =
     ∫_T^t [η(s+1) − η(s)] ds`.
  3. The UCT bound gives `η(t) − ξ(t) → 0`.  Setting
     `ε̃(t) := η(t+1) − η(t)` yields
     `η(t) = (η − ξ)(t) + ξ(T) + ∫_T^t ε̃(s) ds`.
  4. Substitute `s = log v` to convert back to the multiplicative
     form.

  See `Stats/RegularVariation/Representation.lean` for the umbrella.
-/
import Stats.RegularVariation.Representation.Converse

set_option maxHeartbeats 800000

open Real Set Filter Topology Asymptotics MeasureTheory intervalIntegral

namespace TailOptionPricing

/-! ### Forward direction: SV ⇒ representation.

    We follow the BGT recipe.  Throughout, fix a measurable, eventually
    positive, slowly varying `L`.

    Let `η : ℝ → ℝ`, `η(t) := log L(eᵗ)`.  By Korevaar's measurable UCT,
    `η(t + u) − η(t) → 0` uniformly for `u ∈ [0, 1]`.  This gives:

    *  `η` is *eventually locally bounded*: for `T` large, `|η(t)| ≤
       |η(T)| + 1 + ⌈t − T⌉` for `t ≥ T` (the UCT bound on `[0, 1]`
       telescopes across integer-indexed intervals).
    *  Hence `η` is *eventually locally integrable*.

    The smoothed version `ξ(t) := ∫_t^{t+1} η` then satisfies:

    *  `η(t) − ξ(t) → 0` (uniform convergence on `[0, 1]` integrates).
    *  Translation invariance of the Lebesgue integral gives the
       *moving-average identity*  `ξ(b) − ξ(a) = ∫_a^b [η(s+1) − η(s)] ds`.

    Setting `ε̃(s) := η(s + 1) − η(s)`, this rewrites as
    `η(t) = (η − ξ)(t) + ξ(T) + ∫_T^t ε̃(s) ds`.

    Exponentiating and substituting `v = eˢ` (Jacobian `dv/v = ds`) yields
    `L(s) = c(s) · exp(∫_{eᵀ}^{s} ε(v)/v dv)` where:

    *  `ε(v) := ε̃(log v) = log L(v·e) − log L(v)` (defined for `v > 0`)
    *  `c(s) := exp((η − ξ)(log s) + ξ(T))`, which `→ exp(ξ(T)) > 0`. -/

/-- `η L t := log L(eᵗ)`, the additive form of `log L`. -/
private noncomputable def η (L : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.log (L (Real.exp t))

private lemma η_measurable {L : ℝ → ℝ} (hL_meas : Measurable L) :
    Measurable (η L) :=
  Real.measurable_log.comp (hL_meas.comp Real.measurable_exp)

private lemma η_eventually_pos {L : ℝ → ℝ} (hL_pos : ∀ᶠ s in atTop, 0 < L s) :
    ∀ᶠ t in atTop, 0 < L (Real.exp t) :=
  (Real.tendsto_exp_atTop).eventually hL_pos

/-- **UCT in additive form.**  For SV, eventually positive, measurable `L`,
    `η(t + u) − η(t) → 0` uniformly for `u ∈ Set.Icc 0 1`. -/
private lemma η_uct_uniform_on_unit
    {L : ℝ → ℝ} (hL : IsSlowlyVarying L)
    (hL_pos : ∀ᶠ s in atTop, 0 < L s) (hL_meas : Measurable L) :
    TendstoUniformlyOn (fun t u => η L (t + u) - η L t) (fun _ => 0)
      atTop (Set.Icc (0 : ℝ) 1) := by
  -- Apply uniform_convergence on x ∈ [1, e] to get ratio uniformly close to 1,
  -- then take logs.
  have h_e_pos : (0 : ℝ) < 1 := zero_lt_one
  have h_one_le_e : (1 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp 1; linarith
  have h_uct := hL.uniform_convergence hL_pos hL_meas h_e_pos h_one_le_e
  rw [Metric.tendstoUniformlyOn_iff] at h_uct
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε_pos
  -- Take ε small. We translate `|L(t·x)/L(t) − 1| < α` to
  -- `|log L(t·x) − log L(t)| ≤ ε` via the same `2α` chain.
  set α : ℝ := min (ε / 4) (1 / 2) with hα_def
  have hα_pos : 0 < α := lt_min (by linarith) (by norm_num)
  have hα_le_half : α ≤ 1 / 2 := min_le_right _ _
  have hα_le_eps_quarter : α ≤ ε / 4 := min_le_left _ _
  have h1mα_pos : 0 < 1 - α := by linarith
  -- UCT-derived eventual bound.
  have h_uct_event := h_uct α hα_pos
  rcases Filter.eventually_atTop.mp hL_pos with ⟨T_pos, h_pos_T⟩
  rcases Filter.eventually_atTop.mp h_uct_event with ⟨T_uct, h_uct_T⟩
  -- For `t ≥ max(T_uct, T_pos, 1)` (in additive form: `t = log r` for r large).
  have h_lift_log : Tendsto (Real.exp : ℝ → ℝ) atTop atTop :=
    Real.tendsto_exp_atTop
  filter_upwards [h_lift_log.eventually (eventually_ge_atTop T_uct),
                  h_lift_log.eventually (eventually_ge_atTop T_pos)] with t ht_uct ht_pos
  intro u hu
  have h_e_u_pos : 0 < Real.exp u := Real.exp_pos _
  have h_one_le_eu : 1 ≤ Real.exp u := by
    have := Real.add_one_le_exp u
    have h0 : 0 ≤ u := hu.1
    linarith
  have h_eu_le_e : Real.exp u ≤ Real.exp 1 := by
    have := Real.exp_le_exp.mpr hu.2; exact this
  have h_eu_in : Real.exp u ∈ Set.Icc (1 : ℝ) (Real.exp 1) := ⟨h_one_le_eu, h_eu_le_e⟩
  have h_exp_t_pos : 0 < Real.exp t := Real.exp_pos _
  have hL_et_pos : 0 < L (Real.exp t) := h_pos_T _ ht_pos
  have h_exp_tu_pos : 0 < Real.exp (t + u) := Real.exp_pos _
  have h_exp_t_eu_eq : Real.exp t * Real.exp u = Real.exp (t + u) := by
    rw [Real.exp_add]
  have h_exp_t_eu_ge_T_pos : T_pos ≤ Real.exp t * Real.exp u := by
    calc T_pos ≤ Real.exp t := ht_pos
      _ = Real.exp t * 1 := (mul_one _).symm
      _ ≤ Real.exp t * Real.exp u :=
          mul_le_mul_of_nonneg_left h_one_le_eu h_exp_t_pos.le
  have hL_etu_pos : 0 < L (Real.exp t * Real.exp u) :=
    h_pos_T _ h_exp_t_eu_ge_T_pos
  -- Apply UCT bound at t = exp t, x = exp u.
  have h_uct_at : dist 1 (L (Real.exp t * Real.exp u) / L (Real.exp t)) < α :=
    h_uct_T (Real.exp t) ht_uct (Real.exp u) h_eu_in
  rw [Real.dist_eq] at h_uct_at
  set y : ℝ := L (Real.exp t * Real.exp u) / L (Real.exp t) with hy_def
  have hy_pos : 0 < y := div_pos hL_etu_pos hL_et_pos
  have hy_low : 1 - α < y := by have := (abs_lt.mp h_uct_at).2; linarith
  have hy_up : y < 1 + α := by have := (abs_lt.mp h_uct_at).1; linarith
  have h_log_y_up : Real.log y ≤ y - 1 := Real.log_le_sub_one_of_pos hy_pos
  have h_log_y_lo : 1 - y⁻¹ ≤ Real.log y := Real.one_sub_inv_le_log_of_pos hy_pos
  have h_inv_y_le : y⁻¹ ≤ (1 - α)⁻¹ := by
    rw [inv_le_inv₀ hy_pos h1mα_pos]; linarith
  have h_eval : 1 - (1 - α)⁻¹ = -(α / (1 - α)) := by
    have h_ne : (1 - α : ℝ) ≠ 0 := h1mα_pos.ne'
    field_simp; ring
  have h_lo' : -(α / (1 - α)) ≤ Real.log y := by
    have : 1 - (1 - α)⁻¹ ≤ 1 - y⁻¹ := by linarith
    rw [h_eval] at this; linarith
  have h_div_le : α / (1 - α) ≤ 2 * α := by
    rw [div_le_iff₀ h1mα_pos]; nlinarith
  -- Convert log y to η difference.
  have h_log_eq : η L (t + u) - η L t = Real.log y := by
    show Real.log (L (Real.exp (t + u))) - Real.log (L (Real.exp t)) = _
    rw [hy_def, Real.log_div hL_etu_pos.ne' hL_et_pos.ne']
    congr 1; rw [h_exp_t_eu_eq]
  -- Distance bound.
  rw [Real.dist_eq, zero_sub, abs_neg, h_log_eq]
  by_cases h_log_nn : 0 ≤ Real.log y
  · rw [abs_of_nonneg h_log_nn]
    calc Real.log y ≤ y - 1 := h_log_y_up
      _ ≤ α := by linarith
      _ < ε := by linarith
  · have h_log_nn : Real.log y < 0 := not_le.mp h_log_nn
    rw [abs_of_neg h_log_nn]
    calc -Real.log y ≤ α / (1 - α) := by linarith
      _ ≤ 2 * α := h_div_le
      _ < ε := by linarith

/-- **Telescoping `η` bound from UCT.**  Given the UCT-derived inequality
    `|η(t + u) − η(t)| ≤ K` for `t ≥ T, u ∈ [0, 1]`, induction on integer
    offsets yields `|η(s) − η(T)| ≤ K · (s − T + 1)` for all `s ≥ T`. -/
private lemma η_telescope_bound {L : ℝ → ℝ} {T K : ℝ} (hK : 0 ≤ K)
    (h : ∀ t, T ≤ t → ∀ u ∈ Set.Icc (0 : ℝ) 1,
            |η L (t + u) - η L t| ≤ K) :
    ∀ s, T ≤ s → |η L s - η L T| ≤ K * (s - T + 1) := by
  -- Inductive bound: ∀ n : ℕ, ∀ s ∈ [T + n, T + n + 1],
  -- |η L s - η L T| ≤ K * (n + 1).
  have h_step : ∀ n : ℕ, ∀ s, T + (n : ℝ) ≤ s → s ≤ T + n + 1 →
      |η L s - η L T| ≤ K * ((n : ℝ) + 1) := by
    intro n
    induction n with
    | zero =>
      intro s hs1 hs2
      have hu1 : 0 ≤ s - T := by push_cast at hs1; linarith
      have hu2 : s - T ≤ 1 := by push_cast at hs2; linarith
      have h_app := h T le_rfl (s - T) ⟨hu1, hu2⟩
      have heq : T + (s - T) = s := by ring
      rw [heq] at h_app
      push_cast; linarith
    | succ k ih =>
      intro s hs1 hs2
      have hs1' : T + (k : ℝ) ≤ s - 1 := by push_cast at hs1; linarith
      have hs2' : s - 1 ≤ T + (k : ℝ) + 1 := by push_cast at hs2; linarith
      have h_ih := ih (s - 1) hs1' hs2'
      have hs'_ge_T : T ≤ s - 1 := by
        have h_T_nn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
        linarith
      have h_step_app := h (s - 1) hs'_ge_T 1 ⟨zero_le_one, le_refl _⟩
      have heq : (s - 1) + 1 = s := by ring
      rw [heq] at h_step_app
      have h_tri : |η L s - η L T|
          ≤ |η L s - η L (s - 1)| + |η L (s - 1) - η L T| := by
        have h_split : η L s - η L T =
            (η L s - η L (s - 1)) + (η L (s - 1) - η L T) := by ring
        rw [h_split]; exact abs_add_le _ _
      push_cast
      linarith [h_step_app, h_ih, h_tri]
  intro s hs
  set n : ℕ := ⌊s - T⌋₊ with hn_def
  have hsT_nn : 0 ≤ s - T := by linarith
  have hn_le : (n : ℝ) ≤ s - T := Nat.floor_le hsT_nn
  have hsT_lt : s - T < (n : ℝ) + 1 := Nat.lt_floor_add_one _
  have h1 : T + (n : ℝ) ≤ s := by linarith
  have h2 : s ≤ T + (n : ℝ) + 1 := by linarith
  have h_app := h_step n s h1 h2
  -- (n + 1) ≤ (s - T) + 1.
  have h_n_bound : ((n : ℝ) + 1) ≤ (s - T) + 1 := by
    have : (n : ℝ) ≤ s - T := hn_le
    linarith
  calc |η L s - η L T| ≤ K * ((n : ℝ) + 1) := h_app
    _ ≤ K * ((s - T) + 1) := mul_le_mul_of_nonneg_left h_n_bound hK

/-- **`η` is integrable on every compact `[T, b]` above the UCT threshold.** -/
private lemma η_integrableOn_Icc {L : ℝ → ℝ}
    (hL : IsSlowlyVarying L)
    (hL_pos : ∀ᶠ s in atTop, 0 < L s) (hL_meas : Measurable L) :
    ∃ T : ℝ, ∀ b, T ≤ b → IntegrableOn (η L) (Set.Icc T b) volume := by
  have h_uct := η_uct_uniform_on_unit hL hL_pos hL_meas
  rw [Metric.tendstoUniformlyOn_iff] at h_uct
  rcases Filter.eventually_atTop.mp (h_uct 1 zero_lt_one) with ⟨T, h_uct_T⟩
  refine ⟨T, fun b hb => ?_⟩
  -- Establish UCT bound at T.
  have h_uct_at : ∀ t, T ≤ t → ∀ u ∈ Set.Icc (0 : ℝ) 1,
      |η L (t + u) - η L t| ≤ 1 := by
    intro t ht u hu
    have h := h_uct_T t ht u hu
    rw [Real.dist_eq, zero_sub, abs_neg] at h
    exact h.le
  -- Telescope bound.
  have h_bound := η_telescope_bound (zero_le_one) h_uct_at
  -- |η L s| ≤ |η L T| + (b - T + 1) for s ∈ [T, b].
  set M : ℝ := |η L T| + (b - T + 1) with hM_def
  have hM_nn : 0 ≤ M := by
    rw [hM_def]; have := abs_nonneg (η L T); linarith
  -- Now apply IntegrableOn.of_bound.
  have h_vol_finite : volume (Set.Icc T b) < ⊤ := by
    rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top
  refine IntegrableOn.of_bound h_vol_finite ?_ M ?_
  · exact (η_measurable hL_meas).aestronglyMeasurable
  · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc ?_
    intro s hs
    obtain ⟨hsT, hsb⟩ := hs
    have h_diff_bound : |η L s - η L T| ≤ 1 * (s - T + 1) := h_bound s hsT
    rw [one_mul] at h_diff_bound
    have h_total : |η L s| ≤ |η L T| + (s - T + 1) := by
      calc |η L s| = |(η L s - η L T) + η L T| := by ring_nf
        _ ≤ |η L s - η L T| + |η L T| := abs_add_le _ _
        _ ≤ (s - T + 1) + |η L T| := by linarith
        _ = |η L T| + (s - T + 1) := by ring
    rw [Real.norm_eq_abs]
    calc |η L s| ≤ |η L T| + (s - T + 1) := h_total
      _ ≤ |η L T| + (b - T + 1) := by linarith
      _ = M := by rw [hM_def]

/-- **`η L` is interval-integrable above the UCT threshold.** -/
private lemma η_intervalIntegrable {L : ℝ → ℝ}
    (hL : IsSlowlyVarying L)
    (hL_pos : ∀ᶠ s in atTop, 0 < L s) (hL_meas : Measurable L) :
    ∃ T : ℝ, ∀ a b, T ≤ a → a ≤ b → IntervalIntegrable (η L) volume a b := by
  obtain ⟨T, hT⟩ := η_integrableOn_Icc hL hL_pos hL_meas
  refine ⟨T, fun a b hTa hab => ?_⟩
  have hTb : T ≤ b := le_trans hTa hab
  have h_int_T_b := hT b hTb
  have h_subset : Set.Icc a b ⊆ Set.Icc T b := Set.Icc_subset_Icc hTa le_rfl
  have h_int_a_b : IntegrableOn (η L) (Set.Icc a b) volume :=
    h_int_T_b.mono_set h_subset
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  exact h_int_a_b.mono_set Set.Ioc_subset_Icc_self

/-- The moving-average smoother `ξ(t) := ∫_t^{t+1} η(s) ds`. -/
private noncomputable def ξ (L : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ s in t..(t + 1), η L s

/-- **Translation/moving-average identity.**  For `η` interval-integrable on
    `[T, ∞)`, `ξ(b) − ξ(a) = ∫_a^b (η(s+1) − η(s)) ds` for `T ≤ a ≤ b`. -/
private lemma ξ_translation_identity {L : ℝ → ℝ} {T : ℝ}
    (h_int : ∀ a b, T ≤ a → a ≤ b → IntervalIntegrable (η L) volume a b)
    {a b : ℝ} (hTa : T ≤ a) (hab : a ≤ b) :
    ξ L b - ξ L a = ∫ s in a..b, (η L (s + 1) - η L s) := by
  -- Sub-integrabilities.
  have h_T_b : T ≤ b := le_trans hTa hab
  have h_T_b1 : T ≤ b + 1 := by linarith
  have h_T_a1 : T ≤ a + 1 := by linarith
  have h_a_a1 : a ≤ a + 1 := by linarith
  have h_b_b1 : b ≤ b + 1 := by linarith
  have h_a1_b1 : a + 1 ≤ b + 1 := by linarith
  have h_a_b1 : a ≤ b + 1 := by linarith
  have h_int_a_a1 : IntervalIntegrable (η L) volume a (a + 1) :=
    h_int a (a + 1) hTa h_a_a1
  have h_int_b_b1 : IntervalIntegrable (η L) volume b (b + 1) :=
    h_int b (b + 1) h_T_b h_b_b1
  have h_int_a_b : IntervalIntegrable (η L) volume a b := h_int a b hTa hab
  have h_int_a1_b1 : IntervalIntegrable (η L) volume (a + 1) (b + 1) :=
    h_int (a + 1) (b + 1) h_T_a1 h_a1_b1
  -- Translation: ∫_{a+1}^{b+1} η = ∫_a^b η(·+1).
  have h_trans : (∫ s in (a + 1)..(b + 1), η L s) =
                 ∫ s in a..b, η L (s + 1) := by
    have h := intervalIntegral.integral_comp_add_right (a := a) (b := b) (η L) 1
    exact h.symm
  -- Adjacent additivity:
  -- ∫_a^{a+1} + ∫_{a+1}^{b+1} = ∫_a^{b+1}
  -- ∫_a^b + ∫_b^{b+1} = ∫_a^{b+1}
  have h_add1 : (∫ s in a..(a + 1), η L s) + (∫ s in (a + 1)..(b + 1), η L s) =
                 ∫ s in a..(b + 1), η L s :=
    intervalIntegral.integral_add_adjacent_intervals h_int_a_a1 h_int_a1_b1
  have h_add2 : (∫ s in a..b, η L s) + (∫ s in b..(b + 1), η L s) =
                 ∫ s in a..(b + 1), η L s :=
    intervalIntegral.integral_add_adjacent_intervals h_int_a_b h_int_b_b1
  -- Combine.
  have h_eq_diff : (∫ s in (a + 1)..(b + 1), η L s) - (∫ s in a..b, η L s) =
                   (∫ s in b..(b + 1), η L s) - (∫ s in a..(a + 1), η L s) := by
    linarith
  -- η L (· + 1) is interval-integrable on [a, b].
  have h_int_shift : IntervalIntegrable (fun s => η L (s + 1)) volume a b := by
    have := h_int_a1_b1.comp_add_right 1
    have ha_eq : a + 1 - 1 = a := by ring
    have hb_eq : b + 1 - 1 = b := by ring
    rw [ha_eq, hb_eq] at this
    exact this
  -- Goal.
  show ξ L b - ξ L a = ∫ s in a..b, (η L (s + 1) - η L s)
  unfold ξ
  rw [intervalIntegral.integral_sub h_int_shift h_int_a_b, ← h_trans]
  linarith

/-- **`η − ξ → 0`.**  By UCT, `|η(t) − η(t + u)|` is uniformly small for
    `u ∈ [0, 1]` and `t` large; integrating in `u` gives the bound on
    `|η(t) − ξ(t)|`. -/
private lemma η_minus_ξ_tendsto_zero {L : ℝ → ℝ}
    (hL : IsSlowlyVarying L)
    (hL_pos : ∀ᶠ s in atTop, 0 < L s) (hL_meas : Measurable L)
    {T : ℝ}
    (h_int : ∀ a b, T ≤ a → a ≤ b → IntervalIntegrable (η L) volume a b) :
    Tendsto (fun t => η L t - ξ L t) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε_pos
  -- UCT.
  have h_uct := η_uct_uniform_on_unit hL hL_pos hL_meas
  rw [Metric.tendstoUniformlyOn_iff] at h_uct
  rcases Filter.eventually_atTop.mp (h_uct (ε / 2) (by linarith)) with ⟨T_uct, h_uct_T⟩
  set N : ℝ := max T T_uct with hN_def
  refine ⟨N, fun t ht => ?_⟩
  have ht_T : T ≤ t := le_trans (le_max_left _ _) ht
  have ht_uct : T_uct ≤ t := le_trans (le_max_right _ _) ht
  have h_t_le_t1 : t ≤ t + 1 := by linarith
  have h_int_t_t1 : IntervalIntegrable (η L) volume t (t + 1) :=
    h_int t (t + 1) ht_T h_t_le_t1
  -- η L t = ∫_t^{t+1} (η L t) ds (constant integral).
  have h_const : ∫ s in t..(t + 1), η L t = η L t := by
    rw [intervalIntegral.integral_const]; simp
  -- η L t - ξ L t = ∫_t^{t+1} (η L t - η L s) ds.
  have h_diff_eq : η L t - ξ L t =
      ∫ s in t..(t + 1), (η L t - η L s) := by
    unfold ξ
    rw [intervalIntegral.integral_sub
          intervalIntegrable_const h_int_t_t1, h_const]
  rw [Real.dist_eq, sub_zero, h_diff_eq]
  -- Translate to s = t + u.
  have h_translate : (∫ s in t..(t + 1), (η L t - η L s)) =
                     ∫ u in (0 : ℝ)..1, (η L t - η L (t + u)) := by
    have h := intervalIntegral.integral_comp_add_right (a := (0 : ℝ)) (b := 1)
      (fun s => η L t - η L s) t
    -- h : ∫ x in 0..1, (η L t - η L (x + t)) = ∫ x in 0+t..1+t, (η L t - η L x)
    have h_arg : (0 : ℝ) + t = t := by ring
    have h_arg2 : (1 : ℝ) + t = t + 1 := by ring
    rw [h_arg, h_arg2] at h
    have h_swap : (fun x => η L t - η L (x + t)) = (fun u => η L t - η L (t + u)) := by
      ext u; congr 2; ring
    rw [h_swap] at h
    exact h.symm
  rw [h_translate]
  -- Bound by `intervalIntegral.norm_integral_le_of_norm_le_const`.
  have h_const_bound : ∀ u ∈ Set.Ioc (min (0 : ℝ) 1) (max 0 1),
      ‖η L t - η L (t + u)‖ ≤ ε / 2 := by
    intro u hu
    have h_min : min (0 : ℝ) 1 = 0 := by norm_num
    have h_max : max (0 : ℝ) 1 = 1 := by norm_num
    rw [h_min, h_max] at hu
    obtain ⟨hu_lo, hu_hi⟩ := hu
    have hu_in : u ∈ Set.Icc (0 : ℝ) 1 := ⟨hu_lo.le, hu_hi⟩
    have h := h_uct_T t ht_uct u hu_in
    rw [Real.dist_eq, zero_sub, abs_neg] at h
    rw [Real.norm_eq_abs, show η L t - η L (t + u) = -(η L (t + u) - η L t) from by ring,
        abs_neg]
    exact h.le
  have h_norm := intervalIntegral.norm_integral_le_of_norm_le_const h_const_bound
  -- |1 - 0| = 1.
  have h_abs : |(1 : ℝ) - 0| = 1 := by norm_num
  rw [h_abs, mul_one] at h_norm
  rw [Real.norm_eq_abs] at h_norm
  linarith

/-- **Change of variable `u = eᵛ`.**  For measurable `f` and `T > 0`,
    `∫ y in T..eᵗ, f(y)/y dy = ∫ v in log T..t, f(eᵛ) dv`. -/
private lemma integral_div_eq_integral_comp_exp
    {f : ℝ → ℝ} {T t : ℝ} (hT : 0 < T) (hLogT_le_t : Real.log T ≤ t) :
    ∫ y in T..(Real.exp t), f y / y = ∫ v in (Real.log T)..t, f (Real.exp v) := by
  have hT_le_exp_t : T ≤ Real.exp t := by
    rw [show T = Real.exp (Real.log T) from (Real.exp_log hT).symm]
    exact Real.exp_le_exp.mpr hLogT_le_t
  -- Image of Icc under exp.
  have h_image : Real.exp '' Set.Icc (Real.log T) t = Set.Icc T (Real.exp t) := by
    ext y
    simp only [Set.mem_image, Set.mem_Icc]
    constructor
    · rintro ⟨v, ⟨hv_lo, hv_hi⟩, rfl⟩
      refine ⟨?_, Real.exp_le_exp.mpr hv_hi⟩
      rw [show T = Real.exp (Real.log T) from (Real.exp_log hT).symm]
      exact Real.exp_le_exp.mpr hv_lo
    · rintro ⟨hy_lo, hy_hi⟩
      have hy_pos : 0 < y := lt_of_lt_of_le hT hy_lo
      refine ⟨Real.log y, ⟨Real.log_le_log hT hy_lo, ?_⟩, Real.exp_log hy_pos⟩
      rw [show t = Real.log (Real.exp t) from (Real.log_exp t).symm]
      exact Real.log_le_log hy_pos hy_hi
  -- Injectivity & derivative.
  have h_inj : Set.InjOn Real.exp (Set.Icc (Real.log T) t) :=
    Real.exp_strictMono.injective.injOn
  have h_deriv : ∀ v ∈ Set.Icc (Real.log T) t,
      HasDerivWithinAt Real.exp (Real.exp v) (Set.Icc (Real.log T) t) v :=
    fun v _ => (Real.hasDerivAt_exp v).hasDerivWithinAt
  -- Apply Jacobian formula.
  have h_jac := MeasureTheory.integral_image_eq_integral_abs_deriv_smul
    measurableSet_Icc h_deriv h_inj (fun y => f y / y)
  rw [h_image] at h_jac
  -- Simplify: |exp v| = exp v, exp v • (f(exp v) / exp v) = f(exp v).
  have h_simp : Set.EqOn (fun v => |Real.exp v| • (f (Real.exp v) / Real.exp v))
      (fun v => f (Real.exp v)) (Set.Icc (Real.log T) t) := by
    intro v _
    show |Real.exp v| • (f (Real.exp v) / Real.exp v) = f (Real.exp v)
    have h_pos : 0 < Real.exp v := Real.exp_pos _
    rw [abs_of_pos h_pos, smul_eq_mul, mul_div_cancel₀ _ h_pos.ne']
  rw [setIntegral_congr_fun measurableSet_Icc h_simp] at h_jac
  -- Convert from set integrals over Icc to interval integrals.
  rw [intervalIntegral.integral_of_le hT_le_exp_t,
      intervalIntegral.integral_of_le hLogT_le_t]
  rw [← integral_Icc_eq_integral_Ioc, ← integral_Icc_eq_integral_Ioc]
  exact h_jac

/-! ### The main forward theorem.

    Given measurable, eventually positive, slowly varying `L`, we
    construct a Karamata representation `L(s) = c(s) · exp(∫_T^s ε/u du)`.

    *  `T := exp T_uct` for `T_uct` from the local-integrability lemma.
    *  `ε(s) := log L(s · e) − log L(s)` for `s` where `L` is positive
       (and `0` elsewhere): bounded measurable, `→ 0`.
    *  `c(s) := exp((η − ξ)(log s) + ξ T_uct)`: measurable, `→ exp ξ T_uct > 0`. -/

theorem IsSlowlyVarying.karamata_representation
    {L : ℝ → ℝ} (hL : IsSlowlyVarying L)
    (hL_pos : ∀ᶠ s in atTop, 0 < L s) (hL_meas : Measurable L) :
    ∃ T > 0, ∃ c₀, ∃ c ε : ℝ → ℝ, IsKaramataRepresentation L T c₀ c ε := by
  -- Anchor `T_uct` from local integrability.
  obtain ⟨T_uct, h_int⟩ := η_intervalIntegrable hL hL_pos hL_meas
  -- ε(s) := log L(s · e) - log L(s).
  set ε_fn : ℝ → ℝ := fun s => Real.log (L (s * Real.exp 1)) - Real.log (L s) with hε_def
  have hε_meas : Measurable ε_fn := by
    refine Measurable.sub ?_ ?_
    · exact Real.measurable_log.comp
        (hL_meas.comp (measurable_id.mul_const _))
    · exact Real.measurable_log.comp hL_meas
  -- ε → 0: pointwise SV at e gives L(s·e)/L(s) → 1, so log → 0.
  have h_e_pos : (0 : ℝ) < Real.exp 1 := Real.exp_pos _
  have h_ratio_to_one : Tendsto (fun s => L (s * Real.exp 1) / L s) atTop (𝓝 1) :=
    hL (Real.exp 1) h_e_pos
  have h_log_lim : Tendsto Real.log (𝓝 1) (𝓝 0) := by
    have := (Real.continuousAt_log one_ne_zero).tendsto
    rwa [Real.log_one] at this
  have hε_lim : Tendsto ε_fn atTop (𝓝 0) := by
    have h_log_ratio : Tendsto (fun s => Real.log (L (s * Real.exp 1) / L s))
        atTop (𝓝 0) := h_log_lim.comp h_ratio_to_one
    have h_lift : Tendsto (fun s : ℝ => s * Real.exp 1) atTop atTop :=
      Filter.tendsto_id.atTop_mul_const h_e_pos
    have h_eq : ∀ᶠ s in atTop,
        Real.log (L (s * Real.exp 1) / L s) = ε_fn s := by
      filter_upwards [hL_pos, h_lift.eventually hL_pos] with s h_pos h_pos_e
      rw [hε_def]
      exact Real.log_div h_pos_e.ne' h_pos.ne'
    exact h_log_ratio.congr' h_eq
  -- ε is bounded eventually (since ε → 0).  Get a hard bound on [T_anchor, ∞).
  obtain ⟨T_eps_anchor, hT_eps⟩ := (Metric.tendsto_atTop.mp hε_lim) 1 zero_lt_one
  have hT_eps' : ∀ s, T_eps_anchor ≤ s → |ε_fn s| ≤ 1 := fun s hs => by
    have := hT_eps s hs; rw [Real.dist_eq, sub_zero] at this; exact this.le
  -- Get S_pos so that L is positive on [S_pos, ∞).
  rcases Filter.eventually_atTop.mp hL_pos with ⟨S_pos, hS_pos⟩
  -- The anchor `T` (multiplicative) := exp(max(T_uct, T_eps_anchor, log S_pos) + 1).
  set T_anchor : ℝ :=
    max (max T_uct T_eps_anchor) (max (Real.log (max S_pos 1)) 0) + 1 with hT_anchor_def
  set T : ℝ := Real.exp T_anchor with hT_def
  have hT_pos : 0 < T := Real.exp_pos _
  have hT_anchor_ge_T_uct : T_uct ≤ T_anchor := by
    rw [hT_anchor_def]
    have h1 : T_uct ≤ max T_uct T_eps_anchor := le_max_left _ _
    have h2 : max T_uct T_eps_anchor ≤
      max (max T_uct T_eps_anchor) (max (Real.log (max S_pos 1)) 0) :=
        le_max_left _ _
    linarith
  have hT_anchor_ge_T_eps : T_eps_anchor ≤ T_anchor := by
    rw [hT_anchor_def]
    have h1 : T_eps_anchor ≤ max T_uct T_eps_anchor := le_max_right _ _
    have h2 : max T_uct T_eps_anchor ≤
      max (max T_uct T_eps_anchor) (max (Real.log (max S_pos 1)) 0) :=
        le_max_left _ _
    linarith
  have hT_anchor_ge_logSpos : Real.log (max S_pos 1) ≤ T_anchor := by
    rw [hT_anchor_def]
    have h1 : Real.log (max S_pos 1) ≤ max (Real.log (max S_pos 1)) 0 :=
      le_max_left _ _
    have h2 : max (Real.log (max S_pos 1)) 0 ≤
      max (max T_uct T_eps_anchor) (max (Real.log (max S_pos 1)) 0) :=
        le_max_right _ _
    linarith
  have h_logT : Real.log T = T_anchor := Real.log_exp T_anchor
  have hT_ge_Spos : S_pos ≤ T := by
    have h_max_ge : S_pos ≤ max S_pos 1 := le_max_left _ _
    have h_pos : 0 < max S_pos 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    have h_log_le : Real.log (max S_pos 1) ≤ T_anchor := hT_anchor_ge_logSpos
    have h_le : max S_pos 1 ≤ T := by
      rw [show max S_pos 1 = Real.exp (Real.log (max S_pos 1)) from
            (Real.exp_log h_pos).symm, hT_def]
      exact Real.exp_le_exp.mpr h_log_le
    linarith
  -- η - ξ → 0.
  have h_η_ξ_zero := η_minus_ξ_tendsto_zero hL hL_pos hL_meas h_int
  -- Constants.
  set c₀ : ℝ := Real.exp (ξ L T_anchor) with hc₀_def
  have hc₀_pos : 0 < c₀ := Real.exp_pos _
  -- Define c.
  set c_fn : ℝ → ℝ := fun s =>
    Real.exp ((η L (Real.log s) - ξ L (Real.log s)) + ξ L T_anchor) with hc_def
  -- (Measurability of c not needed; structure no longer requires it.)
  -- c → c₀ as s → ∞.
  have hc_lim : Tendsto c_fn atTop (𝓝 c₀) := by
    rw [hc₀_def]
    refine Real.continuous_exp.tendsto _ |>.comp ?_
    -- (η - ξ)(log s) + ξ T_anchor → 0 + ξ T_anchor = ξ T_anchor.
    have h_log_to_inf : Tendsto (Real.log : ℝ → ℝ) atTop atTop :=
      Real.tendsto_log_atTop
    have h_inner : Tendsto (fun s => η L (Real.log s) - ξ L (Real.log s)) atTop (𝓝 0) :=
      h_η_ξ_zero.comp h_log_to_inf
    have : Tendsto
        (fun s => (η L (Real.log s) - ξ L (Real.log s)) + ξ L T_anchor)
        atTop (𝓝 (0 + ξ L T_anchor)) := h_inner.add tendsto_const_nhds
    rwa [zero_add] at this
  -- ε/u is interval-integrable on [T, s] for s ≥ T.
  -- Since |ε(u)| ≤ 1 for u ≥ T_eps_anchor, and T_anchor ≥ T_eps_anchor,
  -- ε is bounded on [T_anchor, ∞).  Then ε(exp v) bounded on [T_anchor, ∞).
  -- The change of variable converts ∫_T^s ε(u)/u du = ∫_{T_anchor}^{log s} ε(exp v) dv.
  have hε_div_int : ∀ s, T ≤ s → IntervalIntegrable (fun u => ε_fn u / u) volume T s := by
    intro s hs
    -- Bounded |ε_fn u| ≤ 1 for u ≥ T_eps_anchor (and T ≥ T_eps_anchor since T = exp T_anchor ≥ T_anchor ≥ T_eps_anchor + 1).
    -- For u ≥ T > 0, |ε_fn u / u| ≤ 1 / T (since |u| ≥ T).
    -- Bounded measurable on [T, s] → integrable.
    have hT_ge_T_eps_anchor : T_eps_anchor ≤ T := by
      have h1 : T_eps_anchor ≤ T_anchor := hT_anchor_ge_T_eps
      have h2 : T_anchor ≤ T := by
        have h_self : T_anchor ≤ Real.exp T_anchor := by
          have := Real.add_one_le_exp T_anchor; linarith
        linarith
      linarith
    refine MeasureTheory.IntegrableOn.intervalIntegrable ?_
    -- Bounded by 1/T on Set.uIcc T s = Set.Icc T s (since T ≤ s).
    have h_uIcc_eq : Set.uIcc T s = Set.Icc T s := Set.uIcc_of_le hs
    have h_bound_on : ∀ u ∈ Set.Icc T s, ‖ε_fn u / u‖ ≤ 1 / T := by
      intro u hu
      obtain ⟨hu_lo, _⟩ := hu
      have hu_pos : 0 < u := lt_of_lt_of_le hT_pos hu_lo
      have hu_ge_T_eps : T_eps_anchor ≤ u := by
        have := hT_ge_T_eps_anchor
        linarith
      have h_eps : |ε_fn u| ≤ 1 := hT_eps' u hu_ge_T_eps
      have h_inv : (1 : ℝ) / u ≤ 1 / T :=
        one_div_le_one_div_of_le hT_pos hu_lo
      rw [Real.norm_eq_abs, abs_div, abs_of_pos hu_pos]
      calc |ε_fn u| / u
          = |ε_fn u| * (1 / u) := by ring
        _ ≤ 1 * (1 / T) :=
            mul_le_mul h_eps h_inv (by positivity) (by linarith)
        _ = 1 / T := by ring
    rw [h_uIcc_eq]
    refine IntegrableOn.of_bound ?_ ?_ (1 / T) ?_
    · rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top
    · refine Measurable.aestronglyMeasurable ?_
      exact hε_meas.div measurable_id
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc ?_
      exact h_bound_on
  -- The representation: L(s) = c(s) · exp(∫_T^s ε/u du) for s ≥ T.
  have hL_repr : ∀ s, T ≤ s →
      L s = c_fn s * Real.exp (∫ u in T..s, ε_fn u / u) := by
    intro s hs
    -- For s ≥ T, log s ≥ T_anchor.
    have hs_pos : 0 < s := lt_of_lt_of_le hT_pos hs
    have hLogs_ge : T_anchor ≤ Real.log s := by
      rw [show T_anchor = Real.log T from h_logT.symm]
      exact Real.log_le_log hT_pos hs
    -- ∫_T^s ε/u du = ∫_{T_anchor}^{log s} ε(exp v) dv.
    have h_cov := integral_div_eq_integral_comp_exp (f := ε_fn)
      (T := T) (t := Real.log s) hT_pos
      (by rw [h_logT]; exact hLogs_ge)
    have h_exp_log : Real.exp (Real.log s) = s := Real.exp_log hs_pos
    rw [h_logT] at h_cov
    rw [h_exp_log] at h_cov
    -- Now ∫_T^s ε/u du = ∫_{T_anchor}^{log s} ε(exp v) dv.
    -- And ε(exp v) = log L(exp v · e) - log L(exp v) = η(v + 1) - η(v).
    -- So ∫_{T_anchor}^{log s} ε(exp v) dv = ∫_{T_anchor}^{log s} (η(v+1) - η(v)) dv
    --                                    = ξ(log s) - ξ(T_anchor)  [translation identity]
    have h_ε_exp_eq : ∀ v, ε_fn (Real.exp v) = η L (v + 1) - η L v := by
      intro v
      simp only [hε_def]
      show Real.log (L (Real.exp v * Real.exp 1)) - Real.log (L (Real.exp v)) =
           Real.log (L (Real.exp (v + 1))) - Real.log (L (Real.exp v))
      congr 1
      congr 1
      rw [← Real.exp_add]
    have h_cov2 : (∫ v in T_anchor..Real.log s, ε_fn (Real.exp v))
                 = ∫ v in T_anchor..Real.log s, (η L (v + 1) - η L v) := by
      apply intervalIntegral.integral_congr (fun v _ => h_ε_exp_eq v)
    have h_ξ := ξ_translation_identity h_int hT_anchor_ge_T_uct hLogs_ge
    -- Combine.
    rw [h_cov, h_cov2, ← h_ξ]
    -- L s = c s · exp((ξ(log s) - ξ T_anchor))
    -- c s = exp((η - ξ)(log s) + ξ T_anchor)
    -- so c s · exp(ξ(log s) - ξ T_anchor) = exp(η(log s) - ξ(log s) + ξ T_anchor + ξ(log s) - ξ T_anchor)
    --                                    = exp(η(log s)) = L(exp(log s)) = L s.
    rw [hc_def]
    rw [← Real.exp_add]
    show L s = Real.exp ((η L (Real.log s) - ξ L (Real.log s)) + ξ L T_anchor +
                          (ξ L (Real.log s) - ξ L T_anchor))
    have h_simp : (η L (Real.log s) - ξ L (Real.log s)) + ξ L T_anchor +
                   (ξ L (Real.log s) - ξ L T_anchor) = η L (Real.log s) := by ring
    rw [h_simp]
    show L s = Real.exp (Real.log (L (Real.exp (Real.log s))))
    rw [h_exp_log]
    have hL_s_pos : 0 < L s := hS_pos s (le_trans hT_ge_Spos hs)
    rw [Real.exp_log hL_s_pos]
  -- Construct the IsKaramataRepresentation.
  refine ⟨T, hT_pos, c₀, c_fn, ε_fn, ?_⟩
  exact ⟨hT_pos, hε_div_int, hc₀_pos, hc_lim, hε_lim, hL_repr⟩


end TailOptionPricing
