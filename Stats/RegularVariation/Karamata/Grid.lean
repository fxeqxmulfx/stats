module

/-
  Karamata's theory of regular variation.

  ## Stats.RegularVariation.Karamata.Grid — multiplicative-grid form.

  Bridges `log L = o(log s)` to the multiplicative-grid form
  `subexp_along_exp_grid{,_of_monotone}` used by downstream
  consumers.

  See `Stats/RegularVariation/Karamata.lean` for the umbrella.
-/
public import Stats.RegularVariation.Karamata.Monotone
public import Stats.RegularVariation.Karamata.Measurable

@[expose] public section

set_option maxHeartbeats 800000

open Real Set Filter Topology Asymptotics

namespace TailOptionPricing

/-! ### Multiplicative-grid form

    Both the measurable variant `subexp_along_exp_grid` and the monotone
    variant `subexp_along_exp_grid_of_monotone` reduce to a common helper
    that takes `log L = o(log s)` as input. -/

/-- **Helper: multiplicative-grid form from `log L = o(log s)`.**
    Given the Karamata `o`-bound `h_o`, derive
    `log(L(s₀·e^{2t}) / L(s₀·e^t)) / t → 0`.

    Proof: `|log L(s)| ≤ δ · log s` eventually, so for `s_t := s₀·e^t`,
    `|log L(s_{2t}) − log L(s_t)| ≤ δ · (log s₀ + 2t) + δ · (log s₀ + t)
    ≤ 5δ · t` for `t ≥ |log s₀| + 1`, hence `/t ≤ 5δ < ε`. -/
private lemma subexp_along_exp_grid_of_log_o_log
    {L : ℝ → ℝ} (hL_pos : ∀ᶠ s in atTop, 0 < L s)
    (h_o : (fun s => Real.log (L s)) =o[atTop] (fun s => Real.log s))
    {s₀ : ℝ} (hs₀ : 0 < s₀) :
    Tendsto (fun t : ℝ =>
        Real.log (L (s₀ * Real.exp (t * 2)) / L (s₀ * Real.exp t)) / t)
      atTop (𝓝 0) := by
  rw [Asymptotics.isLittleO_iff] at h_o
  have h_lift_t : Tendsto (fun t : ℝ => s₀ * Real.exp t) atTop atTop :=
    Tendsto.const_mul_atTop hs₀ Real.tendsto_exp_atTop
  have h_lift_2t : Tendsto (fun t : ℝ => s₀ * Real.exp (t * 2)) atTop atTop := by
    apply Tendsto.const_mul_atTop hs₀
    apply Real.tendsto_exp_atTop.comp
    exact Tendsto.atTop_mul_const (by norm_num : (0:ℝ) < 2) tendsto_id
  refine Metric.tendsto_atTop.mpr (fun ε hε => ?_)
  set δ := ε / 10 with hδ_def
  have hδ_pos : 0 < δ := by positivity
  have h_5δ_lt : 5 * δ < ε := by rw [hδ_def]; linarith
  -- Eventual bounds for log L at s₀·e^t and s₀·e^{2t}, plus positivity.
  have h_event_t := h_lift_t.eventually (h_o hδ_pos)
  have h_event_2t := h_lift_2t.eventually (h_o hδ_pos)
  have h_pos_t := h_lift_t.eventually hL_pos
  have h_pos_2t := h_lift_2t.eventually hL_pos
  have h_t_large : ∀ᶠ t in atTop, |Real.log s₀| + 1 ≤ t :=
    eventually_ge_atTop _
  have h_all := h_event_t.and (h_event_2t.and (h_pos_t.and (h_pos_2t.and h_t_large)))
  rcases Filter.eventually_atTop.mp h_all with ⟨N, hN⟩
  refine ⟨N, fun t ht => ?_⟩
  obtain ⟨h_bnd_t, h_bnd_2t, h_pos_t_t, h_pos_2t_t, h_t_log⟩ := hN t ht
  -- Pin down t > 0
  have h_logs₀_nn : 0 ≤ |Real.log s₀| := abs_nonneg _
  have ht_pos : 0 < t := by linarith
  have h_t_abs : |t| = t := abs_of_pos ht_pos
  -- Express the goal with log L difference
  rw [Real.dist_eq, sub_zero, abs_div, h_t_abs,
      Real.log_div h_pos_2t_t.ne' h_pos_t_t.ne', div_lt_iff₀ ht_pos]
  -- Compute log s₀·exp t = log s₀ + t etc.
  have h_log_st : Real.log (s₀ * Real.exp t) = Real.log s₀ + t := by
    rw [Real.log_mul hs₀.ne' (Real.exp_pos _).ne', Real.log_exp]
  have h_log_s2t : Real.log (s₀ * Real.exp (t * 2)) = Real.log s₀ + 2 * t := by
    rw [Real.log_mul hs₀.ne' (Real.exp_pos _).ne', Real.log_exp]; ring
  -- Translate the SV bounds with these.
  simp only [Real.norm_eq_abs] at h_bnd_t h_bnd_2t
  rw [h_log_st] at h_bnd_t
  rw [h_log_s2t] at h_bnd_2t
  -- Triangle bound on |log s₀ + t| and |log s₀ + 2t|
  have h_abs_t : |Real.log s₀ + t| ≤ |Real.log s₀| + t := by
    calc |Real.log s₀ + t| ≤ |Real.log s₀| + |t| := abs_add_le _ _
      _ = |Real.log s₀| + t := by rw [h_t_abs]
  have h_abs_2t : |Real.log s₀ + 2 * t| ≤ |Real.log s₀| + 2 * t := by
    have h_2t_pos : (0 : ℝ) < 2 * t := by linarith
    calc |Real.log s₀ + 2 * t| ≤ |Real.log s₀| + |2 * t| := abs_add_le _ _
      _ = |Real.log s₀| + 2 * t := by rw [abs_of_pos h_2t_pos]
  -- Bound the difference of two logs via the triangle.
  have h_diff_bound :
      |Real.log (L (s₀ * Real.exp (t * 2))) - Real.log (L (s₀ * Real.exp t))|
        ≤ δ * (2 * |Real.log s₀| + 3 * t) := by
    have h_tri :
        |Real.log (L (s₀ * Real.exp (t * 2))) - Real.log (L (s₀ * Real.exp t))| ≤
        |Real.log (L (s₀ * Real.exp (t * 2)))| + |Real.log (L (s₀ * Real.exp t))| := by
      rw [sub_eq_add_neg]
      calc |Real.log (L (s₀ * Real.exp (t * 2))) +
              -Real.log (L (s₀ * Real.exp t))|
          ≤ |Real.log (L (s₀ * Real.exp (t * 2)))| +
              |-Real.log (L (s₀ * Real.exp t))| := abs_add_le _ _
        _ = |Real.log (L (s₀ * Real.exp (t * 2)))| +
              |Real.log (L (s₀ * Real.exp t))| := by rw [abs_neg]
    calc |Real.log (L (s₀ * Real.exp (t * 2))) - Real.log (L (s₀ * Real.exp t))|
        ≤ |Real.log (L (s₀ * Real.exp (t * 2)))| +
            |Real.log (L (s₀ * Real.exp t))| := h_tri
      _ ≤ δ * |Real.log s₀ + 2 * t| + δ * |Real.log s₀ + t| := by linarith
      _ ≤ δ * (|Real.log s₀| + 2 * t) + δ * (|Real.log s₀| + t) := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_left h_abs_2t hδ_pos.le
          · exact mul_le_mul_of_nonneg_left h_abs_t hδ_pos.le
      _ = δ * (2 * |Real.log s₀| + 3 * t) := by ring
  -- Crucial: 2|log s₀| + 3t ≤ 5t - 2 (using |log s₀| ≤ t - 1).
  have h_5t : 2 * |Real.log s₀| + 3 * t ≤ 5 * t - 2 := by linarith
  calc |Real.log (L (s₀ * Real.exp (t * 2))) - Real.log (L (s₀ * Real.exp t))|
      ≤ δ * (2 * |Real.log s₀| + 3 * t) := h_diff_bound
    _ ≤ δ * (5 * t - 2) := mul_le_mul_of_nonneg_left h_5t hδ_pos.le
    _ < 5 * δ * t := by nlinarith [hδ_pos, ht_pos]
    _ ≤ ε * t := by nlinarith [ht_pos, h_5δ_lt]

/-- **Monotone variant of `subexp_along_exp_grid`.**  Direct corollary of
    `log_isLittleO_log_of_monotone` plus the helper. -/
theorem IsSlowlyVarying.subexp_along_exp_grid_of_monotone
    {L : ℝ → ℝ} (hL : IsSlowlyVarying L)
    (hL_pos : ∀ᶠ s in atTop, 0 < L s)
    (hL_mono : ∃ T₀ > 0, MonotoneOn L (Set.Ici T₀))
    {s₀ : ℝ} (hs₀ : 0 < s₀) :
    Tendsto (fun t : ℝ =>
        Real.log (L (s₀ * Real.exp (t * 2)) / L (s₀ * Real.exp t)) / t)
      atTop (𝓝 0) :=
  subexp_along_exp_grid_of_log_o_log hL_pos
    (hL.log_isLittleO_log_of_monotone hL_pos hL_mono) hs₀

/-- **Measurable variant of `subexp_along_exp_grid`.**  Direct corollary of
    `log_isLittleO_log` plus the helper. -/
theorem IsSlowlyVarying.subexp_along_exp_grid
    {L : ℝ → ℝ} (hL : IsSlowlyVarying L)
    (hL_pos : ∀ᶠ s in atTop, 0 < L s)
    (hL_meas : Measurable L)
    {s₀ : ℝ} (hs₀ : 0 < s₀) :
    Tendsto (fun t : ℝ =>
        Real.log (L (s₀ * Real.exp (t * 2)) / L (s₀ * Real.exp t)) / t)
      atTop (𝓝 0) :=
  subexp_along_exp_grid_of_log_o_log hL_pos
    (hL.log_isLittleO_log hL_pos hL_meas) hs₀


end TailOptionPricing
