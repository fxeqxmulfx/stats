/-
  Karamata's theory of regular variation.

  ## Stats.RegularVariation.Karamata.Monotone — `log L = o(log s)` for monotone SV.

  Proves `IsSlowlyVarying.log_isLittleO_log_of_monotone` directly,
  via a step bound from pointwise SV, telescoping, and a sandwich
  argument using monotonicity at the grid points `T·rⁿ`.

  See `Stats/RegularVariation/Karamata.lean` for the umbrella.
-/
import Stats.RegularVariation.Karamata.Helpers

set_option maxHeartbeats 800000

open Real Set Filter Topology Asymptotics

namespace TailOptionPricing

/-- **Karamata's `o`-bound, monotone variant.**  For slowly varying `L` that
    is eventually monotone (non-decreasing on `[T₀, ∞)` for some `T₀ > 0`)
    and eventually positive, `log L(s) = o(log s)` as `s → ∞`.

    *Proof outline.*  Given `ε > 0`, set `δ := min(ε/4, 1/2)`, `r := 1+δ`.

    1. **Step bound** (from pointwise SV at `r`).  Eventually
       `|log L(t·r) − log L(t)| ≤ δ²`.
    2. **Telescoping** (`log_L_telescope`).
       `|log L(t·rⁿ) − log L(t)| ≤ n·δ²` for `t ≥ T`, all `n : ℕ`.
    3. **Anchor.**  Take `T := max(T₀, T_step, T_pos, 1) ≥ 1`.
    4. **Indexing.**  For `s ≥ T·r`, set `n := ⌊log(s/T)/log r⌋`.
       Then `T·rⁿ ≤ s ≤ T·rⁿ⁺¹`.
    5. **Sandwich via monotonicity.**
       `log L(T·rⁿ) ≤ log L(s) ≤ log L(T·rⁿ⁺¹)`, both within `(n+1)·δ²` of
       `log L T`.  Conclude `|log L s − log L T| ≤ (n+1)·δ²`.
    6. **Bound `n+1 ≤ 2 log s/δ + 1`**, so `(n+1)·δ² ≤ 2δ·log s + δ²`.
    7. **Finalise.**  `|log L s| ≤ |log L T| + 2δ·log s + δ² ≤ ε·log s` for
       `s ≥ exp(2(M+1)/ε)`. -/
theorem IsSlowlyVarying.log_isLittleO_log_of_monotone
    {L : ℝ → ℝ} (hL : IsSlowlyVarying L)
    (hL_pos : ∀ᶠ s in atTop, 0 < L s)
    (hL_mono : ∃ T₀ > 0, MonotoneOn L (Set.Ici T₀)) :
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
  set r := 1 + δ with hr_def
  have hr_pos : (0 : ℝ) < r := by rw [hr_def]; linarith
  have hr_ge_one : (1 : ℝ) ≤ r := by rw [hr_def]; linarith
  have hr_gt_one : (1 : ℝ) < r := by rw [hr_def]; linarith
  have h_log_r_ge : δ / 2 ≤ Real.log r := log_one_add_ge_half hδ_pos hδ_le_one
  have h_log_r_pos : 0 < Real.log r := lt_of_lt_of_le (by linarith) h_log_r_ge
  -- 2. Step bound from pointwise SV at r.
  have hδ_sq_pos : 0 < δ ^ 2 := by positivity
  have h_step := hL.log_step_bound_eventually hL_pos hr_pos hδ_sq_pos
  -- 3. Anchor T: combine all eventual conditions.
  obtain ⟨T₀, hT₀_pos, hL_mono⟩ := hL_mono
  rcases Filter.eventually_atTop.mp h_step with ⟨T_step, h_step_T⟩
  rcases Filter.eventually_atTop.mp hL_pos with ⟨T_pos, h_pos_T⟩
  set T := max (max T₀ (max T_step T_pos)) 1 with hT_def
  have hT_ge_T₀ : T₀ ≤ T := le_trans (le_max_left _ _) (le_max_left _ _)
  have hT_ge_step : T_step ≤ T :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_left _ _)
  have hT_ge_pos : T_pos ≤ T :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_left _ _)
  have hT_ge_one : (1 : ℝ) ≤ T := le_max_right _ _
  have hT_pos : 0 < T := lt_of_lt_of_le zero_lt_one hT_ge_one
  have h_log_T_nonneg : 0 ≤ Real.log T := Real.log_nonneg hT_ge_one
  have h_step_T' : ∀ t, T ≤ t →
      |Real.log (L (t * r)) - Real.log (L t)| ≤ δ ^ 2 :=
    fun t ht => h_step_T t (le_trans hT_ge_step ht)
  have h_pos_T' : ∀ t, T ≤ t → 0 < L t :=
    fun t ht => h_pos_T t (le_trans hT_ge_pos ht)
  -- 4. Telescope at anchor T:
  --    ∀ n, |log L(T·rⁿ) - log L T| ≤ n·δ².
  have h_telescope : ∀ n : ℕ, ∀ t, T ≤ t →
      |Real.log (L (t * r ^ n)) - Real.log (L t)| ≤ (n : ℝ) * δ ^ 2 :=
    log_L_telescope hr_ge_one hT_pos h_step_T'
  -- 5. Anchor offset: M := |log L T|.
  have h_L_T_pos : 0 < L T := h_pos_T' T le_rfl
  set M := |Real.log (L T)| with hM_def
  have hM_nonneg : 0 ≤ M := abs_nonneg _
  -- 6. Pick S₀ ≥ T·r so that log s ≥ 2(M+1)/ε.
  set S₀ := max (T * r) (Real.exp (2 * (M + 1) / ε)) with hS₀_def
  have hS₀_ge_Tr : T * r ≤ S₀ := le_max_left _ _
  have h_log_S₀_ge : 2 * (M + 1) / ε ≤ Real.log S₀ := by
    have h_pos₁ : 0 < Real.exp (2 * (M + 1) / ε) := Real.exp_pos _
    have h_pos₂ : 0 < S₀ := by
      apply lt_of_lt_of_le h_pos₁ (le_max_right _ _)
    rw [show (2 * (M + 1) / ε : ℝ) = Real.log (Real.exp (2 * (M + 1) / ε)) from
          (Real.log_exp _).symm]
    exact Real.log_le_log h_pos₁ (le_max_right _ _)
  -- For s ≥ S₀, derive the bound.
  filter_upwards [eventually_ge_atTop S₀] with s hs_ge_S₀
  have hs_ge_Tr : T * r ≤ s := le_trans hS₀_ge_Tr hs_ge_S₀
  have hs_pos : 0 < s := lt_of_lt_of_le (by positivity) hs_ge_Tr
  have hT_le_s : T ≤ s := by
    calc T ≤ T * r := by nlinarith [hT_pos, hr_ge_one]
      _ ≤ s := hs_ge_Tr
  have h_L_s_pos : 0 < L s := h_pos_T' s hT_le_s
  -- 7. Indexing: n := ⌊log(s/T) / log r⌋
  have hsT_ge_r : r ≤ s / T := by
    rw [le_div_iff₀ hT_pos]; linarith [hs_ge_Tr]
  have hsT_pos : 0 < s / T := div_pos hs_pos hT_pos
  have hsT_gt_one : 1 < s / T := lt_of_lt_of_le hr_gt_one hsT_ge_r
  have h_log_sT_pos : 0 < Real.log (s / T) := Real.log_pos hsT_gt_one
  have h_log_sT_ge_logr : Real.log r ≤ Real.log (s / T) :=
    Real.log_le_log hr_pos hsT_ge_r
  -- log(s/T) ≤ log s since T ≥ 1.
  have h_log_sT_le_log_s : Real.log (s / T) ≤ Real.log s := by
    rw [Real.log_div hs_pos.ne' hT_pos.ne']
    linarith
  set N : ℝ := Real.log (s / T) / Real.log r with hN_def
  have hN_pos : 0 < N := div_pos h_log_sT_pos h_log_r_pos
  have hN_ge_one : 1 ≤ N := by
    rw [hN_def, le_div_iff₀ h_log_r_pos]; linarith
  set n : ℕ := ⌊N⌋₊ with hn_def
  have hn_floor_le : (n : ℝ) ≤ N := Nat.floor_le hN_pos.le
  have hN_lt_succ : N < (n : ℝ) + 1 := Nat.lt_floor_add_one N
  -- 8. Sandwich via monotonicity:
  --    T·rⁿ ≤ s ≤ T·rⁿ⁺¹  (using N ∈ [n, n+1) and rⁿ = exp(n·log r) etc.)
  have h_rpow_n_pos : 0 < (r : ℝ) ^ n := pow_pos hr_pos n
  have h_rpow_succ_pos : 0 < (r : ℝ) ^ (n + 1) := pow_pos hr_pos (n + 1)
  -- Use Real.rpow_natCast bridge.
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
    rw [le_div_iff₀ hT_pos] at h_rpow_n_le_sT
    linarith
  have h_s_le_T_rpow_succ : s ≤ T * r ^ (n + 1) := by
    rw [div_lt_iff₀ hT_pos] at h_sT_lt_rpow_succ
    linarith
  -- 9. Apply telescoping at T:
  have h_telescope_n : |Real.log (L (T * r ^ n)) - Real.log (L T)| ≤
      (n : ℝ) * δ ^ 2 := h_telescope n T le_rfl
  have h_telescope_succ : |Real.log (L (T * r ^ (n + 1))) - Real.log (L T)| ≤
      ((n + 1 : ℕ) : ℝ) * δ ^ 2 := h_telescope (n + 1) T le_rfl
  -- 10. Sandwich log L(s):
  --     log L(T·rⁿ) ≤ log L(s) ≤ log L(T·rⁿ⁺¹)  by monotonicity.
  have h_one_le_rn : (1 : ℝ) ≤ r ^ n := one_le_pow₀ hr_ge_one
  have h_one_le_rn_succ : (1 : ℝ) ≤ r ^ (n + 1) := one_le_pow₀ hr_ge_one
  have h_T_rpow_n_in_Ici : T * r ^ n ∈ Set.Ici T₀ := by
    show T₀ ≤ T * r ^ n
    calc T₀ ≤ T := hT_ge_T₀
      _ = T * 1 := (mul_one T).symm
      _ ≤ T * r ^ n := mul_le_mul_of_nonneg_left h_one_le_rn hT_pos.le
  have h_T_rpow_succ_in_Ici : T * r ^ (n + 1) ∈ Set.Ici T₀ := by
    show T₀ ≤ T * r ^ (n + 1)
    calc T₀ ≤ T := hT_ge_T₀
      _ = T * 1 := (mul_one T).symm
      _ ≤ T * r ^ (n + 1) := mul_le_mul_of_nonneg_left h_one_le_rn_succ hT_pos.le
  have h_s_in_Ici : s ∈ Set.Ici T₀ := le_trans hT_ge_T₀ hT_le_s
  -- Apply monotonicity:
  have h_L_lower : L (T * r ^ n) ≤ L s :=
    hL_mono h_T_rpow_n_in_Ici h_s_in_Ici h_T_rpow_n_le_s
  have h_L_upper : L s ≤ L (T * r ^ (n + 1)) :=
    hL_mono h_s_in_Ici h_T_rpow_succ_in_Ici h_s_le_T_rpow_succ
  have h_L_T_rpow_n_pos : 0 < L (T * r ^ n) := by
    apply h_pos_T'
    calc T = T * 1 := (mul_one T).symm
      _ ≤ T * r ^ n := mul_le_mul_of_nonneg_left h_one_le_rn hT_pos.le
  have h_L_T_rpow_succ_pos : 0 < L (T * r ^ (n + 1)) := by
    apply h_pos_T'
    show T ≤ T * r ^ (n + 1)
    calc T = T * 1 := (mul_one T).symm
      _ ≤ T * r ^ (n + 1) := mul_le_mul_of_nonneg_left h_one_le_rn_succ hT_pos.le
  have h_log_lower : Real.log (L (T * r ^ n)) ≤ Real.log (L s) :=
    Real.log_le_log h_L_T_rpow_n_pos h_L_lower
  have h_log_upper : Real.log (L s) ≤ Real.log (L (T * r ^ (n + 1))) :=
    Real.log_le_log h_L_s_pos h_L_upper
  -- 11. Combine: |log L s − log L T| ≤ (n+1) · δ²
  have h_diff_bound : |Real.log (L s) - Real.log (L T)| ≤
      ((n + 1 : ℕ) : ℝ) * δ ^ 2 := by
    -- log L T - n·δ² ≤ log L(T·rⁿ) ≤ log L s ≤ log L(T·rⁿ⁺¹) ≤ log L T + (n+1)·δ²
    rw [abs_le]
    have h_n_le : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by push_cast; linarith
    refine ⟨?_, ?_⟩
    · have := h_telescope_n
      rw [abs_le] at this
      calc -(((n + 1 : ℕ) : ℝ) * δ ^ 2)
          ≤ -((n : ℝ) * δ ^ 2) := by
              have hδ2 : 0 ≤ δ ^ 2 := by positivity
              nlinarith
        _ ≤ Real.log (L (T * r ^ n)) - Real.log (L T) := this.1
        _ ≤ Real.log (L s) - Real.log (L T) := by linarith
    · calc Real.log (L s) - Real.log (L T)
          ≤ Real.log (L (T * r ^ (n + 1))) - Real.log (L T) := by linarith
        _ ≤ |Real.log (L (T * r ^ (n + 1))) - Real.log (L T)| := le_abs_self _
        _ ≤ ((n + 1 : ℕ) : ℝ) * δ ^ 2 := h_telescope_succ
  -- 12. Bound n+1 ≤ 2 log s / δ + 1 and finalise.
  have h_n_succ_le : ((n + 1 : ℕ) : ℝ) ≤ 2 * Real.log s / δ + 1 := by
    push_cast
    have h_n_le_N : (n : ℝ) ≤ N := hn_floor_le
    have hN_le : N ≤ 2 * Real.log s / δ := by
      rw [hN_def]
      have h_log_r_inv : 1 / Real.log r ≤ 2 / δ := by
        rw [div_le_div_iff₀ h_log_r_pos hδ_pos]
        linarith
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
  -- (n+1) · δ² ≤ (2 log s / δ + 1) · δ² = 2δ · log s + δ²
  -- ≤ 2δ · log s + 1   [δ² ≤ 1]
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
      have : δ ≠ 0 := hδ_pos.ne'
      field_simp
    linarith
  -- |log L s| ≤ M + (n+1) · δ² ≤ M + 2δ · log s + 1
  have h_final_bound : |Real.log (L s)| ≤ M + 2 * δ * Real.log s + 1 := by
    calc |Real.log (L s)|
        = |(Real.log (L s) - Real.log (L T)) + Real.log (L T)| := by ring_nf
      _ ≤ |Real.log (L s) - Real.log (L T)| + |Real.log (L T)| := abs_add_le _ _
      _ ≤ ((n + 1 : ℕ) : ℝ) * δ ^ 2 + M := by linarith
      _ ≤ (2 * δ * Real.log s + 1) + M := by linarith
      _ = M + 2 * δ * Real.log s + 1 := by ring
  -- Finally: ‖log L s‖ ≤ ε * ‖log s‖
  -- For s ≥ S₀ ≥ exp(2(M+1)/ε), log s ≥ 2(M+1)/ε, so M+1 ≤ ε/2 · log s.
  have h_log_s_ge : 2 * (M + 1) / ε ≤ Real.log s := by
    calc 2 * (M + 1) / ε ≤ Real.log S₀ := h_log_S₀_ge
      _ ≤ Real.log s := Real.log_le_log
          (lt_of_lt_of_le (by positivity) hS₀_ge_Tr) hs_ge_S₀
  have h_M_plus_one_bound : M + 1 ≤ ε / 2 * Real.log s := by
    have hε_inv_pos : 0 < ε / 2 := by linarith
    have := mul_le_mul_of_nonneg_left h_log_s_ge hε_inv_pos.le
    have h_simp : ε / 2 * (2 * (M + 1) / ε) = M + 1 := by field_simp
    rw [h_simp] at this
    exact this
  -- ‖log L s‖ = |log L s|, ‖log s‖ = log s (since log s > 0)
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
