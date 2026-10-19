module

/-
  Karamata's theory of regular variation.

  ## Stats.RegularVariation.Karamata.Measurable — `log L = o(log s)` for measurable SV.

  Proves `IsSlowlyVarying.log_isLittleO_log` as a direct corollary
  of the measurable Korevaar UCT.  The "sandwich" step
  `|log L(s) − log L(T·rⁿ)| ≤ δ²` is discharged by uniform
  convergence on `[1, r]`; the telescoping argument at the
  geometric grid is unchanged.

  See `Stats/RegularVariation/Karamata.lean` for the umbrella.
-/
public import Stats.RegularVariation.Karamata.Helpers

@[expose] public section

set_option maxHeartbeats 800000

open Real Set Filter Topology Asymptotics

namespace TailOptionPricing

/-- **Karamata's `o`-bound, measurable variant.**  For slowly varying `L`
    that is measurable and eventually positive, `log L(s) = o(log s)` as
    `s → ∞`.

    *Proof outline.*  Same skeleton as the monotone variant, with the
    monotonicity sandwich replaced by the measurable UCT
    (`IsSlowlyVarying.uniform_convergence`).  Given `ε > 0`, set
    `δ := min(ε/4, 1/2)`, `r := 1+δ`, `α := δ²/2`.

    1. **UCT on `[1, r]` at precision `α`.**  Eventually for `t ≥ T_uct`
       and uniformly in `x ∈ [1, r]`, `|L(t·x)/L(t) − 1| < α`, hence by
       `log y ≤ y − 1` and `1 − 1/y ≤ log y`, `|log L(t·x) − log L(t)| ≤ δ²`.
    2. **Step bound** (specialise UCT to `x = r`).
    3. **Telescoping** (`log_L_telescope`).
    4. **Sandwich via UCT** (specialise to `x = s/(T·rⁿ) ∈ [1, r]`):
       `|log L(s) − log L(T·rⁿ)| ≤ δ²`.
    5. **Combine + finalise** identically to the monotone proof. -/
theorem IsSlowlyVarying.log_isLittleO_log
    {L : ℝ → ℝ} (hL : IsSlowlyVarying L)
    (hL_pos : ∀ᶠ s in atTop, 0 < L s)
    (hL_meas : Measurable L) :
    (fun s => Real.log (L s)) =o[atTop] (fun s => Real.log s) := by
  rw [Asymptotics.isLittleO_iff]
  intro ε hε_pos
  -- 1. Pick δ small.
  set δ := min (ε / 4) (1 / 2) with hδ_def
  have hδ_pos : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδ_le_quarter : δ ≤ ε / 4 := min_le_left _ _
  have hδ_le_half : δ ≤ 1 / 2 := min_le_right _ _
  have hδ_le_one : δ ≤ 1 := by linarith
  have h_2δ_le : 2 * δ ≤ ε / 2 := by linarith
  have hδ_sq_le_one : δ ^ 2 ≤ 1 := by nlinarith
  have hδ_sq_pos : 0 < δ ^ 2 := by positivity
  set r := 1 + δ with hr_def
  have hr_pos : (0 : ℝ) < r := by rw [hr_def]; linarith
  have hr_ge_one : (1 : ℝ) ≤ r := by rw [hr_def]; linarith
  have hr_gt_one : (1 : ℝ) < r := by rw [hr_def]; linarith
  have h_log_r_ge : δ / 2 ≤ Real.log r := log_one_add_ge_half hδ_pos hδ_le_one
  have h_log_r_pos : 0 < Real.log r := lt_of_lt_of_le (by linarith) h_log_r_ge
  -- 2. UCT on [1, r] with precision α = δ²/2.
  set α := δ ^ 2 / 2 with hα_def
  have hα_pos : 0 < α := by positivity
  have hα_le_half : α ≤ 1 / 2 := by rw [hα_def]; linarith
  have h1mα_pos : 0 < 1 - α := by linarith
  have h_uct := hL.uniform_convergence hL_pos hL_meas
                  (by norm_num : (0:ℝ) < 1) hr_ge_one
  rw [Metric.tendstoUniformlyOn_iff] at h_uct
  rcases Filter.eventually_atTop.mp (h_uct α hα_pos) with ⟨T_uct, h_uct_T⟩
  rcases Filter.eventually_atTop.mp hL_pos with ⟨T_pos, h_pos_T⟩
  -- 3. Anchor T = max(T_uct, T_pos, 1).
  set T := max (max T_uct T_pos) 1 with hT_def
  have hT_ge_uct : T_uct ≤ T :=
    le_trans (le_max_left _ _) (le_max_left _ _)
  have hT_ge_pos : T_pos ≤ T :=
    le_trans (le_max_right _ _) (le_max_left _ _)
  have hT_ge_one : (1 : ℝ) ≤ T := le_max_right _ _
  have hT_pos : 0 < T := lt_of_lt_of_le zero_lt_one hT_ge_one
  have h_pos_T' : ∀ t, T ≤ t → 0 < L t :=
    fun t ht => h_pos_T t (le_trans hT_ge_pos ht)
  -- 4. UCT-based log bound on [1, r], for all t ≥ T:
  --    |log L(t·x) − log L(t)| ≤ δ².
  have h_uct_log : ∀ t, T ≤ t → ∀ x ∈ Set.Icc (1 : ℝ) r,
      |Real.log (L (t * x)) - Real.log (L t)| ≤ δ ^ 2 := by
    intro t ht x hx
    have ht_uct : T_uct ≤ t := le_trans hT_ge_uct ht
    have ht_pos' : 0 < t := lt_of_lt_of_le hT_pos ht
    have hL_t_pos : 0 < L t := h_pos_T' t ht
    have hx_one_le : (1 : ℝ) ≤ x := hx.1
    have h_t_le_tx : t ≤ t * x := by nlinarith
    have hL_tx_pos : 0 < L (t * x) :=
      h_pos_T' (t * x) (le_trans ht h_t_le_tx)
    have h_uct_at : dist 1 (L (t * x) / L t) < α := h_uct_T t ht_uct x hx
    rw [Real.dist_eq] at h_uct_at
    set y := L (t * x) / L t with hy_def
    have hy_pos : 0 < y := div_pos hL_tx_pos hL_t_pos
    have hy_low : 1 - α < y := by
      have := (abs_lt.mp h_uct_at).2; linarith
    have hy_up : y < 1 + α := by
      have := (abs_lt.mp h_uct_at).1; linarith
    have h_log_eq : Real.log (L (t * x)) - Real.log (L t) = Real.log y := by
      rw [hy_def, Real.log_div hL_tx_pos.ne' hL_t_pos.ne']
    rw [h_log_eq]
    -- |log y| ≤ 2α = δ².
    have h_log_y_up : Real.log y ≤ y - 1 := Real.log_le_sub_one_of_pos hy_pos
    have h_log_y_lo : 1 - y⁻¹ ≤ Real.log y := Real.one_sub_inv_le_log_of_pos hy_pos
    have h_inv_y_le : y⁻¹ ≤ (1 - α)⁻¹ := by
      rw [inv_le_inv₀ hy_pos h1mα_pos]
      linarith
    have h_eval : 1 - (1 - α)⁻¹ = -(α / (1 - α)) := by
      have h_ne : (1 - α : ℝ) ≠ 0 := h1mα_pos.ne'
      field_simp
      ring
    have h_lo' : -(α / (1 - α)) ≤ Real.log y := by
      have : 1 - (1 - α)⁻¹ ≤ 1 - y⁻¹ := by linarith
      rw [h_eval] at this; linarith
    have h_div_le : α / (1 - α) ≤ 2 * α := by
      rw [div_le_iff₀ h1mα_pos]; nlinarith
    have h_2α_eq : 2 * α = δ ^ 2 := by rw [hα_def]; ring
    rw [abs_le]
    refine ⟨?_, ?_⟩
    · linarith
    · have h_α_le_sq : α ≤ δ ^ 2 := by rw [hα_def]; linarith
      linarith
  -- 5. Step bound for telescope: x = r ∈ [1, r].
  have h_step_T : ∀ t, T ≤ t →
      |Real.log (L (t * r)) - Real.log (L t)| ≤ δ ^ 2 :=
    fun t ht => h_uct_log t ht r ⟨hr_ge_one, le_refl r⟩
  -- 6. Telescope.
  have h_telescope : ∀ n : ℕ, ∀ t, T ≤ t →
      |Real.log (L (t * r ^ n)) - Real.log (L t)| ≤ (n : ℝ) * δ ^ 2 :=
    log_L_telescope hr_ge_one hT_pos h_step_T
  -- 7. Anchor offset M.
  have h_L_T_pos : 0 < L T := h_pos_T' T le_rfl
  set M := |Real.log (L T)| with hM_def
  have hM_nonneg : 0 ≤ M := abs_nonneg _
  -- 8. S₀ = max(T·r, exp(2(M+1)/ε)).
  set S₀ := max (T * r) (Real.exp (2 * (M + 1) / ε)) with hS₀_def
  have hS₀_ge_Tr : T * r ≤ S₀ := le_max_left _ _
  have h_log_S₀_ge : 2 * (M + 1) / ε ≤ Real.log S₀ := by
    have h_pos₁ : 0 < Real.exp (2 * (M + 1) / ε) := Real.exp_pos _
    rw [show (2 * (M + 1) / ε : ℝ) = Real.log (Real.exp (2 * (M + 1) / ε)) from
          (Real.log_exp _).symm]
    exact Real.log_le_log h_pos₁ (le_max_right _ _)
  -- 9. For s ≥ S₀, derive bound.
  filter_upwards [eventually_ge_atTop S₀] with s hs_ge_S₀
  have hs_ge_Tr : T * r ≤ s := le_trans hS₀_ge_Tr hs_ge_S₀
  have hs_pos : 0 < s := lt_of_lt_of_le (by positivity) hs_ge_Tr
  have hT_le_s : T ≤ s := by
    calc T ≤ T * r := by nlinarith [hT_pos, hr_ge_one]
      _ ≤ s := hs_ge_Tr
  have h_L_s_pos : 0 < L s := h_pos_T' s hT_le_s
  -- 10. Index n = ⌊log(s/T)/log r⌋.
  have hsT_ge_r : r ≤ s / T := by
    rw [le_div_iff₀ hT_pos]; linarith [hs_ge_Tr]
  have hsT_pos : 0 < s / T := div_pos hs_pos hT_pos
  have hsT_gt_one : 1 < s / T := lt_of_lt_of_le hr_gt_one hsT_ge_r
  have h_log_sT_pos : 0 < Real.log (s / T) := Real.log_pos hsT_gt_one
  have h_log_sT_ge_logr : Real.log r ≤ Real.log (s / T) :=
    Real.log_le_log hr_pos hsT_ge_r
  have h_log_T_nonneg : 0 ≤ Real.log T := Real.log_nonneg hT_ge_one
  have h_log_sT_le_log_s : Real.log (s / T) ≤ Real.log s := by
    rw [Real.log_div hs_pos.ne' hT_pos.ne']; linarith
  set N : ℝ := Real.log (s / T) / Real.log r with hN_def
  have hN_pos : 0 < N := div_pos h_log_sT_pos h_log_r_pos
  have hN_ge_one : 1 ≤ N := by
    rw [hN_def, le_div_iff₀ h_log_r_pos]; linarith
  set n : ℕ := ⌊N⌋₊ with hn_def
  have hn_floor_le : (n : ℝ) ≤ N := Nat.floor_le hN_pos.le
  have hN_lt_succ : N < (n : ℝ) + 1 := Nat.lt_floor_add_one N
  -- 11. T·rⁿ ≤ s ≤ T·rⁿ⁺¹.
  have h_rpow_eq : r ^ (Real.log (s / T) / Real.log r) = s / T := by
    have h_arg : Real.log r * (Real.log (s / T) / Real.log r) = Real.log (s / T) := by
      field_simp
    rw [Real.rpow_def_of_pos hr_pos, h_arg, Real.exp_log hsT_pos]
  have h_rpow_n_le_sT : (r : ℝ) ^ n ≤ s / T := by
    have h_le : r ^ (n : ℝ) ≤ r ^ N :=
      Real.rpow_le_rpow_of_exponent_le hr_ge_one hn_floor_le
    rw [hN_def, h_rpow_eq] at h_le
    rw [show (r : ℝ) ^ n = r ^ (n : ℝ) from (Real.rpow_natCast r n).symm]
    exact h_le
  have h_sT_lt_rpow_succ : s / T < (r : ℝ) ^ (n + 1) := by
    have h_lt : r ^ N < r ^ ((n + 1 : ℕ) : ℝ) := by
      apply Real.rpow_lt_rpow_of_exponent_lt hr_gt_one
      rw [Nat.cast_add, Nat.cast_one]; exact hN_lt_succ
    rw [hN_def, h_rpow_eq] at h_lt
    rwa [show (r : ℝ) ^ (n + 1) = r ^ ((n + 1 : ℕ) : ℝ) from
          (Real.rpow_natCast r (n + 1)).symm]
  have h_T_rpow_n_le_s : T * r ^ n ≤ s := by
    rw [le_div_iff₀ hT_pos] at h_rpow_n_le_sT; linarith
  have h_s_le_T_rpow_succ : s ≤ T * r ^ (n + 1) := by
    rw [div_lt_iff₀ hT_pos] at h_sT_lt_rpow_succ; linarith
  have h_one_le_rn : (1 : ℝ) ≤ r ^ n := one_le_pow₀ hr_ge_one
  have h_T_rn_ge_T : T ≤ T * r ^ n := by
    calc T = T * 1 := (mul_one T).symm
      _ ≤ T * r ^ n := mul_le_mul_of_nonneg_left h_one_le_rn hT_pos.le
  have h_T_rn_pos : 0 < T * r ^ n := lt_of_lt_of_le hT_pos h_T_rn_ge_T
  -- 12. Sandwich via UCT: x = s/(T·rⁿ) ∈ [1, r].
  set xs : ℝ := s / (T * r ^ n) with hxs_def
  have hxs_ge_one : 1 ≤ xs := by
    rw [hxs_def, le_div_iff₀ h_T_rn_pos]; linarith
  have hxs_le_r : xs ≤ r := by
    rw [hxs_def, div_le_iff₀ h_T_rn_pos]
    have h_eq : r * (T * r ^ n) = T * r ^ (n + 1) := by rw [pow_succ]; ring
    rw [h_eq]; exact h_s_le_T_rpow_succ
  have hxs_in : xs ∈ Set.Icc (1 : ℝ) r := ⟨hxs_ge_one, hxs_le_r⟩
  have h_T_rn_x_eq : T * r ^ n * xs = s := by
    rw [hxs_def]; field_simp
  have h_uct_at_n :
      |Real.log (L (T * r ^ n * xs)) - Real.log (L (T * r ^ n))| ≤ δ ^ 2 :=
    h_uct_log (T * r ^ n) h_T_rn_ge_T xs hxs_in
  rw [h_T_rn_x_eq] at h_uct_at_n
  -- 13. Telescope at T.
  have h_telescope_n : |Real.log (L (T * r ^ n)) - Real.log (L T)| ≤
      (n : ℝ) * δ ^ 2 := h_telescope n T le_rfl
  -- 14. Combine: |log L s − log L T| ≤ (n+1)·δ².
  have h_diff_bound : |Real.log (L s) - Real.log (L T)| ≤
      ((n + 1 : ℕ) : ℝ) * δ ^ 2 := by
    have h_split : Real.log (L s) - Real.log (L T) =
        (Real.log (L s) - Real.log (L (T * r ^ n))) +
        (Real.log (L (T * r ^ n)) - Real.log (L T)) := by ring
    calc |Real.log (L s) - Real.log (L T)|
        = |(Real.log (L s) - Real.log (L (T * r ^ n))) +
            (Real.log (L (T * r ^ n)) - Real.log (L T))| := by rw [h_split]
      _ ≤ |Real.log (L s) - Real.log (L (T * r ^ n))| +
          |Real.log (L (T * r ^ n)) - Real.log (L T)| := abs_add_le _ _
      _ ≤ δ ^ 2 + (n : ℝ) * δ ^ 2 := add_le_add h_uct_at_n h_telescope_n
      _ = ((n + 1 : ℕ) : ℝ) * δ ^ 2 := by push_cast; ring
  -- 15. Bound n+1 ≤ 2 log s / δ + 1.
  have h_n_succ_le : ((n + 1 : ℕ) : ℝ) ≤ 2 * Real.log s / δ + 1 := by
    push_cast
    have h_n_le_N : (n : ℝ) ≤ N := hn_floor_le
    have hN_le : N ≤ 2 * Real.log s / δ := by
      rw [hN_def]
      have h_log_r_inv : 1 / Real.log r ≤ 2 / δ := by
        rw [div_le_div_iff₀ h_log_r_pos hδ_pos]; linarith
      have h_log_s_nn : 0 ≤ Real.log s := by
        apply Real.log_nonneg
        have h_one_le_Tr : (1 : ℝ) ≤ T * r := by
          calc (1 : ℝ) = 1 * 1 := by norm_num
            _ ≤ T * r := mul_le_mul hT_ge_one hr_ge_one zero_le_one
                (le_trans zero_le_one hT_ge_one)
        linarith [hs_ge_Tr]
      calc Real.log (s / T) / Real.log r
          = Real.log (s / T) * (1 / Real.log r) := by ring
        _ ≤ Real.log s * (2 / δ) :=
            mul_le_mul h_log_sT_le_log_s h_log_r_inv (by positivity) h_log_s_nn
        _ = 2 * Real.log s / δ := by ring
    linarith
  have h_log_s_pos : 0 < Real.log s := by
    apply Real.log_pos
    have h_one_lt_Tr : (1 : ℝ) < T * r := by
      calc (1 : ℝ) < r := hr_gt_one
        _ = 1 * r := (one_mul r).symm
        _ ≤ T * r := mul_le_mul_of_nonneg_right hT_ge_one hr_pos.le
    linarith [hs_ge_Tr]
  have h_succ_δ_sq_bound : ((n + 1 : ℕ) : ℝ) * δ ^ 2 ≤
      2 * δ * Real.log s + 1 := by
    have h1 : ((n + 1 : ℕ) : ℝ) * δ ^ 2 ≤
        (2 * Real.log s / δ + 1) * δ ^ 2 :=
      mul_le_mul_of_nonneg_right h_n_succ_le (by positivity)
    have h2 : (2 * Real.log s / δ + 1) * δ ^ 2 =
        2 * δ * Real.log s + δ ^ 2 := by
      have : δ ≠ 0 := hδ_pos.ne'; field_simp
    linarith
  have h_final_bound : |Real.log (L s)| ≤ M + 2 * δ * Real.log s + 1 := by
    calc |Real.log (L s)|
        = |(Real.log (L s) - Real.log (L T)) + Real.log (L T)| := by ring_nf
      _ ≤ |Real.log (L s) - Real.log (L T)| + |Real.log (L T)| := abs_add_le _ _
      _ ≤ ((n + 1 : ℕ) : ℝ) * δ ^ 2 + M := by linarith
      _ ≤ (2 * δ * Real.log s + 1) + M := by linarith
      _ = M + 2 * δ * Real.log s + 1 := by ring
  have h_log_s_ge : 2 * (M + 1) / ε ≤ Real.log s := by
    calc 2 * (M + 1) / ε ≤ Real.log S₀ := h_log_S₀_ge
      _ ≤ Real.log s := Real.log_le_log
          (lt_of_lt_of_le (by positivity) hS₀_ge_Tr) hs_ge_S₀
  have h_M_plus_one_bound : M + 1 ≤ ε / 2 * Real.log s := by
    have hε_inv_pos : 0 < ε / 2 := by linarith
    have := mul_le_mul_of_nonneg_left h_log_s_ge hε_inv_pos.le
    have h_simp : ε / 2 * (2 * (M + 1) / ε) = M + 1 := by field_simp
    rw [h_simp] at this; exact this
  have h_norm_log_s : ‖Real.log s‖ = Real.log s := by
    rw [Real.norm_eq_abs, abs_of_pos h_log_s_pos]
  have h_norm_log_L_s : ‖Real.log (L s)‖ = |Real.log (L s)| := Real.norm_eq_abs _
  rw [h_norm_log_s, h_norm_log_L_s]
  calc |Real.log (L s)|
      ≤ M + 2 * δ * Real.log s + 1 := h_final_bound
    _ = (M + 1) + 2 * δ * Real.log s := by ring
    _ ≤ ε / 2 * Real.log s + 2 * δ * Real.log s := by linarith
    _ ≤ ε / 2 * Real.log s + ε / 2 * Real.log s := by
        have h_2δ_le_eps_half : 2 * δ ≤ ε / 2 := by linarith
        nlinarith
    _ = ε * Real.log s := by ring


end TailOptionPricing
