module

/-
  Analytic ingredients for arXiv:2004.05894v1, Eq. 2 and Remark 1.
  Actual sample-law identifications are provided by the sibling modules.
-/
public import Stats.RiskMeasures.Drawdown
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

@[expose] public section

open Real Set Filter Topology MeasureTheory Finset

namespace TailOptionPricing

/-! ## Sample survival ratio (paper Remark 1).

    For `X_i` iid strong Pareto on `[l, ∞)` with index `α > 0`, the
    sample maximum `K_n := max X_i` has the *exact* survival
        ℙ(K_n > k) = 1 − paretoSampleMaxCDF n l α k
                   = 1 − (1 − (l/k)^α)^n      for k ≥ l.

    The corresponding candidate survival-ratio CDF is
        ℙ(Y ≤ y) = 1 − (1 − y)^n,
    the Beta(1, n) formula on `[0, 1]` for `n > 0`. The source's
    Remark 1 uses the Fréchet approximation `n*exp(-n*y)` and `1/n`.
    Here the polynomial formulas, derivative and mean integral
    `1/(n+1)` are proved. The sibling Maximum, SurvivalMass and Mean
    modules identify the actual iid maximum, actual hidden-mass CDF
    and expected hidden mass; see REVIEW.md, HM-04–HM-11. -/

/-- Candidate CDF polynomial from paper Remark 1's finite-sample
    correction: `1 - (1-y)^n`. It is used as a Beta(1,n) CDF only
    for `n > 0` on `[0,1]`; it is not a supported CDF on all reals. -/
noncomputable def paretoSampleSurvivalRatioCDF (n : ℕ) (y : ℝ) : ℝ :=
  1 - (1 - y) ^ n

/-- Candidate PDF polynomial: `n*(1-y)^(n-1)`. An actual density
    uses support `[0,1]` and positive sample size. -/
noncomputable def paretoSampleSurvivalRatioPDF (n : ℕ) (y : ℝ) : ℝ :=
  (n : ℝ) * (1 - y) ^ (n - 1)

/-- **CDF–maximum-CDF bridge.**  For `y ∈ (0, 1]`, the sample-survival-ratio
    CDF is related to the sample-maximum CDF via the substitution
    `k = l · y^(−1/α)`:
        `paretoSampleSurvivalRatioCDF n y
            = 1 − paretoSampleMaxCDF n l α (l · y^(−1/α))`.
    This is a function substitution; its probability interpretation
    requires the actual iid maximum law and continuity assumptions. -/
theorem paretoSampleSurvivalRatioCDF_eq_one_sub_maxCDF
    {l α y : ℝ} {n : ℕ}
    (hl : 0 < l) (hα_pos : 0 < α) (hy_pos : 0 < y) :
    paretoSampleSurvivalRatioCDF n y
      = 1 - paretoSampleMaxCDF n l α (l * y ^ (-(1 : ℝ) / α)) := by
  unfold paretoSampleSurvivalRatioCDF paretoSampleMaxCDF
  have hα_ne : α ≠ 0 := hα_pos.ne'
  have hy_pow_pos : 0 < y ^ (-(1:ℝ) / α) := Real.rpow_pos_of_pos hy_pos _
  have h_prod_pos : 0 < l * y ^ (-(1 : ℝ) / α) := mul_pos hl hy_pow_pos
  have h_prod_ne : l * y ^ (-(1 : ℝ) / α) ≠ 0 := h_prod_pos.ne'
  -- (l / (l · y^(-1/α)))^α = y.
  have h_ratio : (l / (l * y ^ (-(1 : ℝ) / α))) ^ α = y := by
    rw [show l / (l * y ^ (-(1 : ℝ) / α)) = (y ^ (-(1 : ℝ) / α))⁻¹ from by
          field_simp]
    rw [show ((y ^ (-(1 : ℝ) / α))⁻¹ : ℝ) = y ^ (-(-(1:ℝ)/α)) from by
          rw [← Real.rpow_neg hy_pos.le]]
    rw [show (-(-(1:ℝ)/α)) = (1/α) from by ring]
    rw [← Real.rpow_mul hy_pos.le]
    rw [show ((1/α) * α : ℝ) = 1 from by field_simp]
    exact Real.rpow_one y
  rw [h_ratio]

/-- **PDF identity** (`d/dy[1 - (1 - y)^n] = n · (1 - y)^(n-1)`).
    Standard derivative of the polynomial CDF; valid for any `y ∈ ℝ`. -/
theorem paretoSampleSurvivalRatioPDF_eq_deriv (n : ℕ) (y : ℝ) :
    HasDerivAt (paretoSampleSurvivalRatioCDF n)
      (paretoSampleSurvivalRatioPDF n y) y := by
  unfold paretoSampleSurvivalRatioCDF paretoSampleSurvivalRatioPDF
  -- d/dy[1 - (1 - y)^n] = -d/dy[(1 - y)^n] = -n · (1 - y)^(n-1) · (-1) = n · (1 - y)^(n-1).
  have h_base : HasDerivAt (fun y : ℝ => 1 - y) (-1) y := by
    simpa using (hasDerivAt_id y).const_sub (1 : ℝ)
  have h_pow : HasDerivAt (fun y : ℝ => (1 - y) ^ n)
      ((n : ℝ) * (1 - y) ^ (n - 1) * (-1)) y :=
    h_base.pow n
  have h := (h_pow.const_sub 1)
  convert h using 1
  ring

/-! ### Exact mean of the sample survival ratio. -/

/-- **Candidate PDF mean integral** for paper Remark 1's finite-sample
    correction. Computed as
        `∫_0^1 y · n · (1 − y)^(n−1) dy = 1 / (n+1)`
    via FTC with antiderivative
        `F(y) = − y · (1 − y)^n − (1 − y)^(n+1) / (n+1)`.

    Identifying this integral with the mean of an actual transformed
    sample maximum still needs the probability-law bridge. The integral
    value is `1/(n+1)`, whereas the Fréchet approximation uses `1/n`. -/
theorem paretoSampleSurvivalRatio_mean (n : ℕ) (hn : 1 ≤ n) :
    ∫ y in (0:ℝ)..1, y * paretoSampleSurvivalRatioPDF n y
      = 1 / ((n : ℝ) + 1) := by
  unfold paretoSampleSurvivalRatioPDF
  -- Antiderivative: F(y) = -y · (1 - y)^n - (1 - y)^(n+1) / (n+1).
  have hn_pos : 0 < n := hn
  have hn1_pos : (0 : ℝ) < (n : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n; linarith
  have hn1_ne : (n : ℝ) + 1 ≠ 0 := hn1_pos.ne'
  -- y · n · (1-y)^(n-1) = n · y · (1-y)^(n-1).
  have h_eq_integrand : ∀ y : ℝ,
      y * (↑n * (1 - y) ^ (n - 1))
        = ↑n * ((1 - y) ^ (n - 1) - (1 - y) ^ n) := by
    intro y
    have h_pow_split : (1 - y) ^ n = (1 - y) * (1 - y) ^ (n - 1) := by
      conv_lhs => rw [show n = (n - 1) + 1 from by omega]
      rw [pow_add, pow_one]
      ring
    rw [h_pow_split]
    ring
  rw [intervalIntegral.integral_congr (g := fun y =>
      ↑n * ((1 - y) ^ (n - 1) - (1 - y) ^ n)) ?_]
  swap
  · intros y _; exact h_eq_integrand y
  -- = n · (∫(1-y)^(n-1) - ∫(1-y)^n)
  rw [intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_sub]
  · -- ∫_0^1 (1-y)^(n-1) dy = 1/n via substitution u = 1-y.
    have h_int1 : (∫ y in (0:ℝ)..1, (1 - y) ^ (n - 1)) = 1 / (n : ℝ) := by
      have hn_real_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
      have hn_real_ne : (n : ℝ) ≠ 0 := hn_real_pos.ne'
      -- Antiderivative of (1 - y)^(n-1) is -(1 - y)^n / n.
      have h_anti : ∀ y : ℝ, HasDerivAt (fun y : ℝ => -(1 - y) ^ n / (n : ℝ))
          ((1 - y) ^ (n - 1)) y := by
        intro y
        have h_base : HasDerivAt (fun y : ℝ => 1 - y) (-1) y := by
          simpa using (hasDerivAt_id y).const_sub (1 : ℝ)
        have h_pow : HasDerivAt (fun y : ℝ => (1 - y) ^ n)
            ((n : ℝ) * (1 - y) ^ (n - 1) * (-1)) y := h_base.pow n
        have := (h_pow.neg).div_const (n : ℝ)
        convert this using 1
        field_simp
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
            (fun y _ => h_anti y)
            (Continuous.intervalIntegrable (by continuity) _ _)]
      have hn_zero : (0 : ℝ) ^ n = 0 := zero_pow hn_pos.ne'
      rw [show (1 - 1 : ℝ) = 0 from by ring, show (1 - 0 : ℝ) = 1 from by ring,
          hn_zero, one_pow]
      ring
    have h_int2 : (∫ y in (0:ℝ)..1, (1 - y) ^ n) = 1 / ((n : ℝ) + 1) := by
      have h_anti : ∀ y : ℝ, HasDerivAt
          (fun y : ℝ => -(1 - y) ^ (n + 1) / ((n : ℝ) + 1))
          ((1 - y) ^ n) y := by
        intro y
        have h_base : HasDerivAt (fun y : ℝ => 1 - y) (-1) y := by
          simpa using (hasDerivAt_id y).const_sub (1 : ℝ)
        have h_pow : HasDerivAt (fun y : ℝ => (1 - y) ^ (n + 1))
            (((n : ℝ) + 1) * (1 - y) ^ n * (-1)) y := by
          have h := h_base.pow (n + 1)
          convert h using 1
          push_cast; ring
        have := (h_pow.neg).div_const ((n : ℝ) + 1)
        convert this using 1
        field_simp
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
            (fun y _ => h_anti y)
            (Continuous.intervalIntegrable (by continuity) _ _)]
      have hn1_zero : (0 : ℝ) ^ (n + 1) = 0 := zero_pow (by omega)
      rw [show (1 - 1 : ℝ) = 0 from by ring, show (1 - 0 : ℝ) = 1 from by ring,
          hn1_zero, one_pow]
      ring
    rw [h_int1, h_int2]
    -- n · (1/n - 1/(n+1)) = 1 - n/(n+1) = 1/(n+1).
    have hn_real_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
    have hn_real_ne : (n : ℝ) ≠ 0 := hn_real_pos.ne'
    field_simp
    ring
  · exact Continuous.intervalIntegrable (by continuity) _ _
  · exact Continuous.intervalIntegrable (by continuity) _ _

/-- Reciprocal-formula gap: `1/n - 1/(n+1) = 1/(n*(n+1))`.
    This exact scalar identity compares the candidate finite-sample
    mean with the source's Fréchet mean expression. No random-variable
    expectation or asymptotic filter occurs in this theorem. -/
theorem paretoSampleSurvivalRatio_mean_asymptotic_gap (n : ℕ) (hn : 1 ≤ n) :
    (1 / (n : ℝ)) - 1 / ((n : ℝ) + 1) = 1 / ((n : ℝ) * ((n : ℝ) + 1)) := by
  have hn_pos : 0 < n := hn
  have hn_real_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
  have hn_real_ne : (n : ℝ) ≠ 0 := hn_real_pos.ne'
  have hn1_pos : (0 : ℝ) < (n : ℝ) + 1 := by linarith
  have hn1_ne : (n : ℝ) + 1 ≠ 0 := hn1_pos.ne'
  field_simp
  ring

end TailOptionPricing
