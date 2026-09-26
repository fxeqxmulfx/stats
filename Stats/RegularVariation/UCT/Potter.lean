/-
  Karamata's theory of regular variation — Potter bounds.

  ## Stats.RegularVariation.UCT.Potter — Potter bounds.

  Quantitative consequence of UCT in each variant (monotone and
  measurable): `L(t)/L(s) ≤ C · (t/s)^δ` for any `δ > 0`.

  See `Stats/RegularVariation/UCT.lean` for the umbrella.
-/
import Stats.RegularVariation.UCT.Measurable

set_option maxHeartbeats 800000

open Real Set Filter Topology Asymptotics MeasureTheory

namespace TailOptionPricing

/-- **Potter's bounds, measurable variant.**  Direct corollary of
    `IsSlowlyVarying.uniform_convergence`. -/
theorem IsSlowlyVarying.potter_bounds
    {L : ℝ → ℝ} (hL : IsSlowlyVarying L)
    (hL_pos : ∀ᶠ s in atTop, 0 < L s)
    (hL_meas : Measurable L)
    {a b δ : ℝ} (ha : 0 < a) (hab : a ≤ b) (hδ : 0 < δ) (hδ_lt : δ < 1) :
    ∀ᶠ t in atTop, ∀ x ∈ Set.Icc a b,
      (1 - δ) * min 1 (x ^ δ) ≤ L (t * x) / L t ∧
      L (t * x) / L t ≤ (1 + δ) * max 1 (x ^ δ) := by
  have h_uct := hL.uniform_convergence hL_pos hL_meas ha hab
  rw [Metric.tendstoUniformlyOn_iff] at h_uct
  filter_upwards [h_uct δ hδ] with t ht_close x hx_in
  have h := ht_close x hx_in
  rw [Real.dist_eq, abs_lt] at h
  obtain ⟨h_lo, h_hi⟩ := h
  refine ⟨?_, ?_⟩
  · have h_min_le_1 : min (1 : ℝ) (x ^ δ) ≤ 1 := min_le_left _ _
    have h_1_minus_pos : 0 ≤ 1 - δ := by linarith
    calc (1 - δ) * min 1 (x ^ δ)
        ≤ (1 - δ) * 1 := mul_le_mul_of_nonneg_left h_min_le_1 h_1_minus_pos
      _ = 1 - δ := mul_one _
      _ ≤ L (t * x) / L t := by linarith
  · have h_1_le_max : (1 : ℝ) ≤ max 1 (x ^ δ) := le_max_left _ _
    have h_1_plus_pos : 0 ≤ 1 + δ := by linarith
    calc L (t * x) / L t
        ≤ 1 + δ := by linarith
      _ = (1 + δ) * 1 := (mul_one _).symm
      _ ≤ (1 + δ) * max 1 (x ^ δ) :=
          mul_le_mul_of_nonneg_left h_1_le_max h_1_plus_pos

/-- **Potter's bounds, monotone variant.**  Direct corollary of
    `uniform_convergence_of_monotone`. -/
theorem IsSlowlyVarying.potter_bounds_of_monotone
    {L : ℝ → ℝ} (hL : IsSlowlyVarying L)
    (hL_pos : ∀ᶠ s in atTop, 0 < L s)
    (hL_mono : MonotoneOn L (Set.Ioi 0) ∨ AntitoneOn L (Set.Ioi 0))
    {a b δ : ℝ} (ha : 0 < a) (hab : a ≤ b) (hδ : 0 < δ) (hδ_lt : δ < 1) :
    ∀ᶠ t in atTop, ∀ x ∈ Set.Icc a b,
      (1 - δ) * min 1 (x ^ δ) ≤ L (t * x) / L t ∧
      L (t * x) / L t ≤ (1 + δ) * max 1 (x ^ δ) := by
  have h_uct := hL.uniform_convergence_of_monotone hL_pos hL_mono ha hab
  rw [Metric.tendstoUniformlyOn_iff] at h_uct
  filter_upwards [h_uct δ hδ] with t ht_close x hx_in
  have h := ht_close x hx_in
  rw [Real.dist_eq, abs_lt] at h
  obtain ⟨h_lo, h_hi⟩ := h
  refine ⟨?_, ?_⟩
  · have h_min_le_1 : min (1 : ℝ) (x ^ δ) ≤ 1 := min_le_left _ _
    have h_1_minus_pos : 0 ≤ 1 - δ := by linarith
    calc (1 - δ) * min 1 (x ^ δ)
        ≤ (1 - δ) * 1 := mul_le_mul_of_nonneg_left h_min_le_1 h_1_minus_pos
      _ = 1 - δ := mul_one _
      _ ≤ L (t * x) / L t := by linarith
  · have h_1_le_max : (1 : ℝ) ≤ max 1 (x ^ δ) := le_max_left _ _
    have h_1_plus_pos : 0 ≤ 1 + δ := by linarith
    calc L (t * x) / L t
        ≤ 1 + δ := by linarith
      _ = (1 + δ) * 1 := (mul_one _).symm
      _ ≤ (1 + δ) * max 1 (x ^ δ) :=
          mul_le_mul_of_nonneg_left h_1_le_max h_1_plus_pos


end TailOptionPricing
