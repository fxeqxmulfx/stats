/-
  Theorem 1 from Taleb et al., "Tail Option Pricing Under Power Laws":
  log returns of `S` are NOT in the regular variation class.

  Two versions:
    • strong-Pareto specialisation (`survivalLogReturn_not_regularlyVarying`),
    • Karamata-constant version (`...regularlyVarying_general`):
      `bF = L · s^(−α)` with `L → L_∞ ∈ (0, ∞)` at infinity.

  Defines the regular variation class `IsRegularlyVarying`.
-/
import Stats.Pareto

open Real Set MeasureTheory Filter Topology

namespace TailOptionPricing

/-- A function `f : ℝ → ℝ` is *regularly varying at infinity with index `ρ`*
    iff for every `x > 0`, `f(t·x)/f(t) → x^ρ` as `t → ∞`. (Paper Eq. (1).) -/
def IsRegularlyVarying (f : ℝ → ℝ) (ρ : ℝ) : Prop :=
  ∀ x : ℝ, 0 < x → Tendsto (fun t => f (t * x) / f t) atTop (𝓝 (x ^ ρ))

/-- **Eq. (1) applied to our `survival`.**  The strong-Pareto survival function
    `s ↦ (l/s)^α` itself lies in `RV_{−α}` — the ratio is in fact *constant*
    in `t`, equal to `x^(−α)`, so trivially convergent. -/
theorem survival_isRegularlyVarying {l α : ℝ} (hl : 0 < l) :
    IsRegularlyVarying (survival l α) (-α) := by
  intro x hx_pos
  refine Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
  unfold survival
  have hlt : 0 < l / t := div_pos hl ht
  have hltα : 0 < (l / t) ^ α := Real.rpow_pos_of_pos hlt _
  have hxα : 0 < x ^ α := Real.rpow_pos_of_pos hx_pos _
  rw [show l / (t * x) = (l / t) / x from by field_simp,
      Real.div_rpow hlt.le hx_pos.le,
      Real.rpow_neg hx_pos.le]
  field_simp

/-- Survival function of the log return `r_l = log(S/s₀)` under the strong
    Pareto law of `S`: `ℙ(r_l > x) = (l/s₀)^α · exp(-α·x)`. -/
noncomputable def survivalLogReturn (l α s₀ x : ℝ) : ℝ :=
  survival l α (s₀ * Real.exp x)

/-- Closed form for `survivalLogReturn`: the log-return survival is exponential. -/
private lemma survivalLogReturn_eq {l α s₀ x : ℝ} (hl : 0 < l) (hs₀ : 0 < s₀) :
    survivalLogReturn l α s₀ x = (l / s₀) ^ α * Real.exp (-α * x) := by
  unfold survivalLogReturn survival
  have hl_div_s₀_pos : 0 < l / s₀ := div_pos hl hs₀
  have h_simp : l / (s₀ * Real.exp x) = (l / s₀) * Real.exp (-x) := by
    rw [Real.exp_neg]; field_simp
  rw [h_simp, Real.mul_rpow hl_div_s₀_pos.le (Real.exp_pos _).le]
  congr 1
  rw [show (Real.exp (-x)) ^ α = Real.exp ((-x) * α) from (Real.exp_mul (-x) α).symm]
  congr 1; ring

/-- **Theorem 1, strong-Pareto specialisation.**  Under `ℙ(S > s) = (l/s)^α`
    with `α > 0`, the survival of `r_l = log(S/s₀)` is *not* regularly varying
    with any real index. -/
theorem survivalLogReturn_not_regularlyVarying {l α s₀ : ℝ}
    (hl : 0 < l) (hs₀ : 0 < s₀) (hα : 0 < α) (ρ : ℝ) :
    ¬ IsRegularlyVarying (survivalLogReturn l α s₀) ρ := by
  intro h
  have h2 : Tendsto (fun t => survivalLogReturn l α s₀ (t * 2) /
      survivalLogReturn l α s₀ t) atTop (𝓝 ((2 : ℝ) ^ ρ)) := h 2 (by norm_num)
  have hC_pos : 0 < (l / s₀) ^ α := Real.rpow_pos_of_pos (div_pos hl hs₀) _
  have hC_ne : ((l / s₀) ^ α) ≠ 0 := hC_pos.ne'
  have h_ratio : ∀ t : ℝ, survivalLogReturn l α s₀ (t * 2) /
        survivalLogReturn l α s₀ t = Real.exp (-α * t) := by
    intro t
    rw [survivalLogReturn_eq hl hs₀, survivalLogReturn_eq hl hs₀]
    rw [mul_div_mul_left _ _ hC_ne]
    rw [← Real.exp_sub]
    congr 1; ring
  rw [show (fun t => survivalLogReturn l α s₀ (t * 2) /
        survivalLogReturn l α s₀ t) = (fun t => Real.exp (-α * t)) from
      funext h_ratio] at h2
  have h_neg : (-α : ℝ) < 0 := by linarith
  have h_atBot : Tendsto (fun t : ℝ => -α * t) atTop atBot :=
    Tendsto.const_mul_atTop_of_neg h_neg tendsto_id
  have h_to_zero : Tendsto (fun t : ℝ => Real.exp (-α * t)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp h_atBot
  have h2_pow : ((2 : ℝ) ^ ρ) = 0 := tendsto_nhds_unique h2 h_to_zero
  have h2_pos : (0 : ℝ) < (2 : ℝ) ^ ρ := Real.rpow_pos_of_pos (by norm_num) ρ
  linarith

/-- **Theorem 1, Karamata-constant version.**  If the survival function admits
    a representation `s ↦ L(s) · s^(−α)` with `L → L_∞ ∈ (0,∞)` at infinity and
    `α > 0`, then the survival of `r_l = log(S/s₀)` is *not* regularly varying. -/
theorem survivalLogReturn_not_regularlyVarying_general
    {L : ℝ → ℝ} {α s₀ Linf : ℝ}
    (hα : 0 < α) (hs₀ : 0 < s₀) (hLinf : 0 < Linf)
    (h_lim : Tendsto L atTop (𝓝 Linf)) (ρ : ℝ) :
    ¬ IsRegularlyVarying
      (fun x => L (s₀ * Real.exp x) * (s₀ * Real.exp x) ^ (-α)) ρ := by
  intro h_RV
  have h2 := h_RV 2 (by norm_num : (0:ℝ) < 2)
  have h_form : ∀ t : ℝ,
      (L (s₀ * Real.exp (t * 2)) * (s₀ * Real.exp (t * 2)) ^ (-α)) /
      (L (s₀ * Real.exp t) * (s₀ * Real.exp t) ^ (-α)) =
      L (s₀ * Real.exp (t * 2)) / L (s₀ * Real.exp t) * Real.exp (-α * t) := by
    intro t
    have h_t_pos : 0 < s₀ * Real.exp t := mul_pos hs₀ (Real.exp_pos _)
    have h_2t_pos : 0 < s₀ * Real.exp (t * 2) := mul_pos hs₀ (Real.exp_pos _)
    have h_pow_ratio : (s₀ * Real.exp (t * 2)) ^ (-α) /
          (s₀ * Real.exp t) ^ (-α) = Real.exp (-α * t) := by
      rw [← Real.div_rpow h_2t_pos.le h_t_pos.le]
      rw [show s₀ * Real.exp (t * 2) / (s₀ * Real.exp t) = Real.exp t from by
        rw [show t * 2 = t + t from by ring, Real.exp_add]; field_simp]
      rw [show (Real.exp t) ^ (-α) = Real.exp ((-α) * t) from by
        rw [show (-α) * t = t * (-α) from by ring, ← Real.exp_mul]]
    rw [mul_div_mul_comm, h_pow_ratio]
  rw [show (fun t =>
      (L (s₀ * Real.exp (t * 2)) * (s₀ * Real.exp (t * 2)) ^ (-α)) /
      (L (s₀ * Real.exp t) * (s₀ * Real.exp t) ^ (-α))) =
      (fun t => L (s₀ * Real.exp (t * 2)) / L (s₀ * Real.exp t) *
                Real.exp (-α * t)) from funext h_form] at h2
  have h_st : Tendsto (fun t : ℝ => s₀ * Real.exp t) atTop atTop :=
    Tendsto.const_mul_atTop hs₀ Real.tendsto_exp_atTop
  have h_s2t : Tendsto (fun t : ℝ => s₀ * Real.exp (t * 2)) atTop atTop := by
    apply Tendsto.const_mul_atTop hs₀
    apply Real.tendsto_exp_atTop.comp
    exact Tendsto.atTop_mul_const (by norm_num : (0:ℝ) < 2) tendsto_id
  have h_Lt : Tendsto (fun t : ℝ => L (s₀ * Real.exp t)) atTop (𝓝 Linf) :=
    h_lim.comp h_st
  have h_L2t : Tendsto (fun t : ℝ => L (s₀ * Real.exp (t * 2))) atTop (𝓝 Linf) :=
    h_lim.comp h_s2t
  have h_Lratio : Tendsto
      (fun t => L (s₀ * Real.exp (t * 2)) / L (s₀ * Real.exp t)) atTop (𝓝 1) := by
    convert h_L2t.div h_Lt hLinf.ne' using 1 <;> simp [div_self hLinf.ne']
  have h_exp_decay : Tendsto (fun t : ℝ => Real.exp (-α * t)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp
      (Tendsto.const_mul_atTop_of_neg (by linarith : (-α : ℝ) < 0) tendsto_id)
  have h_to_zero : Tendsto
      (fun t => L (s₀ * Real.exp (t * 2)) / L (s₀ * Real.exp t) *
                Real.exp (-α * t)) atTop (𝓝 0) := by
    simpa using h_Lratio.mul h_exp_decay
  have h_pow_zero : (2 : ℝ) ^ ρ = 0 := tendsto_nhds_unique h2 h_to_zero
  have h_pow_pos : (0 : ℝ) < (2 : ℝ) ^ ρ := Real.rpow_pos_of_pos (by norm_num) ρ
  linarith

/-- **Theorem 1, bounded-`L` version.**  Strict generalisation of
    `survivalLogReturn_not_regularlyVarying_general`: instead of requiring
    `L → L_∞ ∈ (0, ∞)`, only require `L` to be eventually bounded
    between two positive constants `m` and `M`.  Covers e.g. oscillating
    factors like `L(s) = 2 + sin s` that have no limit but are bounded.

    The proof squeezes the slowly-varying ratio `L(s₀·e^{2t})/L(s₀·e^t)`
    into `[m/M, M/m]` and combines with `e^{-αt} → 0`. -/
theorem survivalLogReturn_not_regularlyVarying_bdd
    {L : ℝ → ℝ} {α s₀ m M : ℝ}
    (hα : 0 < α) (hs₀ : 0 < s₀) (hm : 0 < m)
    (hLb : ∀ᶠ s in atTop, m ≤ L s)
    (hLub : ∀ᶠ s in atTop, L s ≤ M)
    (ρ : ℝ) :
    ¬ IsRegularlyVarying
      (fun x => L (s₀ * Real.exp x) * (s₀ * Real.exp x) ^ (-α)) ρ := by
  intro h_RV
  have h2 := h_RV 2 (by norm_num : (0:ℝ) < 2)
  -- Reduce the ratio to `(L_2t / L_t) · e^{-αt}`.
  have h_form : ∀ t : ℝ,
      (L (s₀ * Real.exp (t * 2)) * (s₀ * Real.exp (t * 2)) ^ (-α)) /
      (L (s₀ * Real.exp t) * (s₀ * Real.exp t) ^ (-α)) =
      L (s₀ * Real.exp (t * 2)) / L (s₀ * Real.exp t) * Real.exp (-α * t) := by
    intro t
    have h_t_pos : 0 < s₀ * Real.exp t := mul_pos hs₀ (Real.exp_pos _)
    have h_2t_pos : 0 < s₀ * Real.exp (t * 2) := mul_pos hs₀ (Real.exp_pos _)
    have h_pow_ratio : (s₀ * Real.exp (t * 2)) ^ (-α) /
          (s₀ * Real.exp t) ^ (-α) = Real.exp (-α * t) := by
      rw [← Real.div_rpow h_2t_pos.le h_t_pos.le]
      rw [show s₀ * Real.exp (t * 2) / (s₀ * Real.exp t) = Real.exp t from by
        rw [show t * 2 = t + t from by ring, Real.exp_add]; field_simp]
      rw [show (Real.exp t) ^ (-α) = Real.exp ((-α) * t) from by
        rw [show (-α) * t = t * (-α) from by ring, ← Real.exp_mul]]
    rw [mul_div_mul_comm, h_pow_ratio]
  rw [show (fun t =>
      (L (s₀ * Real.exp (t * 2)) * (s₀ * Real.exp (t * 2)) ^ (-α)) /
      (L (s₀ * Real.exp t) * (s₀ * Real.exp t) ^ (-α))) =
      (fun t => L (s₀ * Real.exp (t * 2)) / L (s₀ * Real.exp t) *
                Real.exp (-α * t)) from funext h_form] at h2
  -- Lift the bounds along `t ↦ s₀·e^t` and `t ↦ s₀·e^{2t}`.
  have h_st : Tendsto (fun t : ℝ => s₀ * Real.exp t) atTop atTop :=
    Tendsto.const_mul_atTop hs₀ Real.tendsto_exp_atTop
  have h_s2t : Tendsto (fun t : ℝ => s₀ * Real.exp (t * 2)) atTop atTop := by
    apply Tendsto.const_mul_atTop hs₀
    apply Real.tendsto_exp_atTop.comp
    exact Tendsto.atTop_mul_const (by norm_num : (0:ℝ) < 2) tendsto_id
  have hLb_t : ∀ᶠ t in atTop, m ≤ L (s₀ * Real.exp t) := h_st.eventually hLb
  have hLub_t : ∀ᶠ t in atTop, L (s₀ * Real.exp t) ≤ M := h_st.eventually hLub
  have hLb_2t : ∀ᶠ t in atTop, m ≤ L (s₀ * Real.exp (t * 2)) :=
    h_s2t.eventually hLb
  have hLub_2t : ∀ᶠ t in atTop, L (s₀ * Real.exp (t * 2)) ≤ M :=
    h_s2t.eventually hLub
  -- The bounds force `m ≤ M`, hence `M > 0`.
  have hM_pos : 0 < M := by
    rcases (hLb.and hLub).exists with ⟨_, hL_lb, hL_ub⟩; linarith
  -- Squeeze: `0 ≤ ratio · e^{-αt} ≤ (M/m) · e^{-αt} → 0`.
  have h_exp_decay : Tendsto (fun t : ℝ => Real.exp (-α * t)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp
      (Tendsto.const_mul_atTop_of_neg (by linarith : (-α : ℝ) < 0) tendsto_id)
  have h_const_decay :
      Tendsto (fun t : ℝ => (M / m) * Real.exp (-α * t)) atTop (𝓝 0) := by
    have := tendsto_const_nhds (x := M / m) (f := atTop).mul h_exp_decay
    simpa using this
  have h_lb : ∀ᶠ t in atTop,
      0 ≤ L (s₀ * Real.exp (t * 2)) / L (s₀ * Real.exp t) *
          Real.exp (-α * t) := by
    filter_upwards [hLb_t, hLb_2t] with t hL_t hL_2t
    have h_pos_t : 0 < L (s₀ * Real.exp t) := lt_of_lt_of_le hm hL_t
    have h_pos_2t : 0 ≤ L (s₀ * Real.exp (t * 2)) := le_trans hm.le hL_2t
    exact mul_nonneg
      (div_nonneg h_pos_2t h_pos_t.le)
      (Real.exp_nonneg _)
  have h_ub : ∀ᶠ t in atTop,
      L (s₀ * Real.exp (t * 2)) / L (s₀ * Real.exp t) *
          Real.exp (-α * t) ≤ (M / m) * Real.exp (-α * t) := by
    filter_upwards [hLb_t, hLub_2t] with t hL_t hL_2t
    have h_pos_t : 0 < L (s₀ * Real.exp t) := lt_of_lt_of_le hm hL_t
    have h_ratio_le : L (s₀ * Real.exp (t * 2)) / L (s₀ * Real.exp t) ≤
        M / m := by
      rw [div_le_div_iff₀ h_pos_t hm]
      calc L (s₀ * Real.exp (t * 2)) * m
          ≤ M * m := mul_le_mul_of_nonneg_right hL_2t hm.le
        _ ≤ M * L (s₀ * Real.exp t) := mul_le_mul_of_nonneg_left hL_t hM_pos.le
    exact mul_le_mul_of_nonneg_right h_ratio_le (Real.exp_nonneg _)
  have h_to_zero : Tendsto
      (fun t => L (s₀ * Real.exp (t * 2)) / L (s₀ * Real.exp t) *
                Real.exp (-α * t)) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      h_const_decay h_lb h_ub
  -- Final contradiction: `2^ρ` is positive but must equal `0`.
  have h_pow_zero : (2 : ℝ) ^ ρ = 0 := tendsto_nhds_unique h2 h_to_zero
  have h_pow_pos : (0 : ℝ) < (2 : ℝ) ^ ρ := Real.rpow_pos_of_pos (by norm_num) ρ
  linarith

/-- **Theorem 1, full slowly-varying version (parameterised on Karamata bound).**
    Assume `bF(s) = L(s) · s^(−α)` for `s` large with `α > 0` and `L > 0`.  If
    `L` satisfies the *Karamata bound* `log L(s · e^t) − log L(s) = o(t)` along
    `s = s₀·e^t → ∞` (which any slowly varying function satisfies, by Karamata's
    representation theorem), then the survival of `r_l = log(S/s₀)` is *not*
    regularly varying.

    The Karamata-bound hypothesis is the non-Mathlib ingredient — it is a
    consequence of Mathlib's missing Karamata representation theorem.  Stating
    it as a hypothesis lets us close Theorem 1 in full generality without
    formalising Karamata. -/
theorem survivalLogReturn_not_regularlyVarying_slow
    {L : ℝ → ℝ} {α s₀ : ℝ}
    (hα : 0 < α) (hs₀ : 0 < s₀)
    (hL_pos : ∀ᶠ s in atTop, 0 < L s)
    (h_subexp :
      Tendsto (fun t : ℝ =>
        Real.log (L (s₀ * Real.exp (t * 2)) / L (s₀ * Real.exp t)) / t)
        atTop (𝓝 0))
    (ρ : ℝ) :
    ¬ IsRegularlyVarying
      (fun x => L (s₀ * Real.exp x) * (s₀ * Real.exp x) ^ (-α)) ρ := by
  intro h_RV
  have h2 := h_RV 2 (by norm_num : (0:ℝ) < 2)
  -- Re-write the ratio.
  have h_form : ∀ t : ℝ,
      (L (s₀ * Real.exp (t * 2)) * (s₀ * Real.exp (t * 2)) ^ (-α)) /
      (L (s₀ * Real.exp t) * (s₀ * Real.exp t) ^ (-α)) =
      L (s₀ * Real.exp (t * 2)) / L (s₀ * Real.exp t) * Real.exp (-α * t) := by
    intro t
    have h_t_pos : 0 < s₀ * Real.exp t := mul_pos hs₀ (Real.exp_pos _)
    have h_2t_pos : 0 < s₀ * Real.exp (t * 2) := mul_pos hs₀ (Real.exp_pos _)
    have h_pow_ratio : (s₀ * Real.exp (t * 2)) ^ (-α) /
          (s₀ * Real.exp t) ^ (-α) = Real.exp (-α * t) := by
      rw [← Real.div_rpow h_2t_pos.le h_t_pos.le]
      rw [show s₀ * Real.exp (t * 2) / (s₀ * Real.exp t) = Real.exp t from by
        rw [show t * 2 = t + t from by ring, Real.exp_add]; field_simp]
      rw [show (Real.exp t) ^ (-α) = Real.exp ((-α) * t) from by
        rw [show (-α) * t = t * (-α) from by ring, ← Real.exp_mul]]
    rw [mul_div_mul_comm, h_pow_ratio]
  rw [show (fun t =>
      (L (s₀ * Real.exp (t * 2)) * (s₀ * Real.exp (t * 2)) ^ (-α)) /
      (L (s₀ * Real.exp t) * (s₀ * Real.exp t) ^ (-α))) =
      (fun t => L (s₀ * Real.exp (t * 2)) / L (s₀ * Real.exp t) *
                Real.exp (-α * t)) from funext h_form] at h2
  -- L > 0 along the lifted variable.
  have h_st : Tendsto (fun t : ℝ => s₀ * Real.exp t) atTop atTop :=
    Tendsto.const_mul_atTop hs₀ Real.tendsto_exp_atTop
  have h_s2t : Tendsto (fun t : ℝ => s₀ * Real.exp (t * 2)) atTop atTop := by
    apply Tendsto.const_mul_atTop hs₀
    apply Real.tendsto_exp_atTop.comp
    exact Tendsto.atTop_mul_const (by norm_num : (0:ℝ) < 2) tendsto_id
  have hLp_t : ∀ᶠ t in atTop, 0 < L (s₀ * Real.exp t) :=
    h_st.eventually hL_pos
  have hLp_2t : ∀ᶠ t in atTop, 0 < L (s₀ * Real.exp (t * 2)) :=
    h_s2t.eventually hL_pos
  -- Goal: show the rewritten ratio tends to 0.  Take logs:
  -- log[ratio · e^(-αt)] = log[L_2/L] + (-αt)
  --                     = t · (log[L_2/L]/t - α)  → -∞ (since log/t → 0, α > 0)
  -- Hence ratio · e^(-αt) → 0.
  have h_log_ratio :
      Tendsto (fun t : ℝ =>
          Real.log (L (s₀ * Real.exp (t * 2)) / L (s₀ * Real.exp t)) +
          (-α * t))
        atTop atBot := by
    have h_α_half_pos : (0 : ℝ) < α / 2 := by linarith
    have h_subexp_lt : ∀ᶠ t in atTop,
        Real.log (L (s₀ * Real.exp (t * 2)) / L (s₀ * Real.exp t)) / t <
        α / 2 := h_subexp.eventually (eventually_lt_nhds h_α_half_pos)
    have h_eventually_le : ∀ᶠ t in atTop,
        Real.log (L (s₀ * Real.exp (t * 2)) / L (s₀ * Real.exp t)) +
        (-α * t) ≤ -α / 2 * t := by
      filter_upwards [h_subexp_lt, eventually_gt_atTop (0:ℝ)]
        with t hsubexp ht_pos
      have h_log_eq : Real.log
          (L (s₀ * Real.exp (t * 2)) / L (s₀ * Real.exp t)) =
          t * (Real.log
            (L (s₀ * Real.exp (t * 2)) / L (s₀ * Real.exp t)) / t) := by
        field_simp
      have h_mul : t *
          (Real.log (L (s₀ * Real.exp (t * 2)) / L (s₀ * Real.exp t)) / t) <
          t * (α / 2) := mul_lt_mul_of_pos_left hsubexp ht_pos
      rw [h_log_eq]
      linarith
    have h_g_atBot : Tendsto (fun t : ℝ => -α / 2 * t) atTop atBot :=
      Tendsto.const_mul_atTop_of_neg
        (by linarith : (-α / 2 : ℝ) < 0) tendsto_id
    exact tendsto_atBot_mono' atTop h_eventually_le h_g_atBot
  have h_to_zero :
      Tendsto (fun t : ℝ =>
        L (s₀ * Real.exp (t * 2)) / L (s₀ * Real.exp t) * Real.exp (-α * t))
        atTop (𝓝 0) := by
    have h_eventually_pos : ∀ᶠ t in atTop,
        0 < L (s₀ * Real.exp (t * 2)) / L (s₀ * Real.exp t) *
            Real.exp (-α * t) := by
      filter_upwards [hLp_t, hLp_2t] with t hL_t hL_2t
      exact mul_pos (div_pos hL_2t hL_t) (Real.exp_pos _)
    have h_log_form :
        (fun t : ℝ => Real.log (
          L (s₀ * Real.exp (t * 2)) / L (s₀ * Real.exp t) *
          Real.exp (-α * t))) =ᶠ[atTop]
        (fun t : ℝ =>
          Real.log (L (s₀ * Real.exp (t * 2)) / L (s₀ * Real.exp t)) +
          (-α * t)) := by
      filter_upwards [hLp_t, hLp_2t] with t hL_t hL_2t
      rw [Real.log_mul (div_pos hL_2t hL_t).ne' (Real.exp_pos _).ne',
          Real.log_exp]
    have h_log_to_atBot :
        Tendsto (fun t : ℝ => Real.log (
          L (s₀ * Real.exp (t * 2)) / L (s₀ * Real.exp t) *
          Real.exp (-α * t))) atTop atBot :=
      h_log_ratio.congr' h_log_form.symm
    have h_exp_log : Tendsto (fun t : ℝ => Real.exp (Real.log (
          L (s₀ * Real.exp (t * 2)) / L (s₀ * Real.exp t) *
          Real.exp (-α * t)))) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp h_log_to_atBot
    refine h_exp_log.congr' ?_
    filter_upwards [h_eventually_pos] with t ht
    exact Real.exp_log ht
  have h_pow_zero : (2 : ℝ) ^ ρ = 0 := tendsto_nhds_unique h2 h_to_zero
  have h_pow_pos : (0 : ℝ) < (2 : ℝ) ^ ρ := Real.rpow_pos_of_pos (by norm_num) ρ
  linarith

end TailOptionPricing
