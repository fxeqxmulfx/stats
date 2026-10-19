module

/-
  Risk measures & portfolio theory under Pareto.

  ## Stats.RiskMeasures.CVaR — `paretoCVaR` properties (Item 1).

  Monotonicity in `p` and `l`, scaling `paretoCVaR(c·l) = c·paretoCVaR(l)`,
  and the standard inequality `paretoCVaR ≥ paretoVaR`.

  See `Stats/RiskMeasures.lean` for the umbrella module.
-/
public import Stats.Pareto

@[expose] public section

open Real Set MeasureTheory Filter Topology intervalIntegral

namespace TailOptionPricing

/-! ## Item 1 — CVaR risk-measure properties.

    Monotonicity in the confidence level `p` and in the scale `l`,
    positive homogeneity in `l`, and the standard
    `paretoCVaR ≥ paretoVaR` inequality (Expected Shortfall ≥
    Value-at-Risk). -/

/-- **`paretoVaR` is monotone in `p`.**  Higher confidence → larger
    quantile threshold.  Follows from monotonicity of `(1−p)^(−1/α)`. -/
theorem paretoVaR_mono_p {l α p q : ℝ}
    (hα_pos : 0 < α) (hl : 0 ≤ l) (_hp : 0 ≤ p) (hq_lt : q < 1)
    (hpq : p ≤ q) :
    paretoVaR l α p ≤ paretoVaR l α q := by
  have h1mq_pos : 0 < 1 - q := by linarith
  have h1mp_pos : 0 < 1 - p := by linarith
  have h1mq_le_1mp : 1 - q ≤ 1 - p := by linarith
  have hinv_α_pos : 0 < 1 / α := by positivity
  have hpow_pos_q : 0 < (1 - q) ^ (1 / α) := Real.rpow_pos_of_pos h1mq_pos _
  have hpow_pos_p : 0 < (1 - p) ^ (1 / α) := Real.rpow_pos_of_pos h1mp_pos _
  have hpow_mono : (1 - q) ^ (1 / α) ≤ (1 - p) ^ (1 / α) :=
    Real.rpow_le_rpow h1mq_pos.le h1mq_le_1mp hinv_α_pos.le
  have hinv_mono : ((1 - p) ^ (1 / α))⁻¹ ≤ ((1 - q) ^ (1 / α))⁻¹ :=
    inv_anti₀ hpow_pos_q hpow_mono
  unfold paretoVaR
  rw [Real.rpow_neg h1mp_pos.le, Real.rpow_neg h1mq_pos.le]
  exact mul_le_mul_of_nonneg_left hinv_mono hl

/-- **`paretoVaR` is monotone in `l`.**  Larger scale → larger VaR
    at every confidence level. -/
theorem paretoVaR_mono_l {l₁ l₂ α p : ℝ}
    (_hα_pos : 0 < α) (hp_lt : p < 1) (hl : l₁ ≤ l₂) :
    paretoVaR l₁ α p ≤ paretoVaR l₂ α p := by
  have h1mp_pos : 0 < 1 - p := by linarith
  have hpow_pos : 0 < (1 - p) ^ (-(1 / α)) := Real.rpow_pos_of_pos h1mp_pos _
  unfold paretoVaR
  exact mul_le_mul_of_nonneg_right hl hpow_pos.le

/-- **`paretoVaR` is positively homogeneous in `l`:**
    `paretoVaR(c·l, α, p) = c · paretoVaR(l, α, p)`. -/
theorem paretoVaR_scale (c l α p : ℝ) :
    paretoVaR (c * l) α p = c * paretoVaR l α p := by
  unfold paretoVaR; ring

/-- **`paretoCVaR` is monotone in `p`.**  Direct from `paretoCVaR =
    α/(α−1) · paretoVaR` and monotonicity of `paretoVaR` in `p`. -/
theorem paretoCVaR_mono_p {l α p q : ℝ}
    (hα : 1 < α) (hl : 0 ≤ l) (hp : 0 ≤ p) (hq_lt : q < 1) (hpq : p ≤ q) :
    paretoCVaR l α p ≤ paretoCVaR l α q := by
  have hα_pos : 0 < α := by linarith
  have hfac_pos : 0 < α / (α - 1) := by
    apply div_pos hα_pos; linarith
  unfold paretoCVaR
  exact mul_le_mul_of_nonneg_left
    (paretoVaR_mono_p hα_pos hl hp hq_lt hpq) hfac_pos.le

/-- **`paretoCVaR` is monotone in `l`.**  Larger scale → larger CVaR. -/
theorem paretoCVaR_mono_l {l₁ l₂ α p : ℝ}
    (hα : 1 < α) (hp_lt : p < 1) (hl : l₁ ≤ l₂) :
    paretoCVaR l₁ α p ≤ paretoCVaR l₂ α p := by
  have hα_pos : 0 < α := by linarith
  have hfac_pos : 0 < α / (α - 1) := by
    apply div_pos hα_pos; linarith
  unfold paretoCVaR
  exact mul_le_mul_of_nonneg_left
    (paretoVaR_mono_l hα_pos hp_lt hl) hfac_pos.le

/-- **`paretoCVaR` is positively homogeneous in `l`:**
    `paretoCVaR(c·l, α, p) = c · paretoCVaR(l, α, p)`. -/
theorem paretoCVaR_scale (c l α p : ℝ) :
    paretoCVaR (c * l) α p = c * paretoCVaR l α p := by
  unfold paretoCVaR
  rw [paretoVaR_scale]; ring

/-- **`paretoCVaR ≥ paretoVaR`** (standard Expected Shortfall ≥
    Value-at-Risk).  Equivalent to `α/(α−1) ≥ 1` for `α > 1`. -/
theorem paretoCVaR_ge_paretoVaR {l α p : ℝ}
    (hα : 1 < α) (hl : 0 ≤ l) (hp : 0 ≤ p) (hp_lt : p < 1) :
    paretoVaR l α p ≤ paretoCVaR l α p := by
  have hα_pos : 0 < α := by linarith
  have hα1_pos : 0 < α - 1 := by linarith
  have h_VaR_nn : 0 ≤ paretoVaR l α p :=
    hl.trans (paretoVaR_ge_l (show (0:ℝ) < α from hα_pos) hl hp hp_lt)
  have h_fac_ge_one : 1 ≤ α / (α - 1) := by
    rw [le_div_iff₀ hα1_pos]; linarith
  unfold paretoCVaR
  calc paretoVaR l α p = 1 * paretoVaR l α p := (one_mul _).symm
    _ ≤ α / (α - 1) * paretoVaR l α p :=
        mul_le_mul_of_nonneg_right h_fac_ge_one h_VaR_nn


end TailOptionPricing
