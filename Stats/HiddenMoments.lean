/-
  What You See and What You Don't See: The Hidden Moments of a
  Probability Distribution.  Taleb, arXiv:2004.05894v1 (Apr 2020).

  Formalized analytic ingredients:
    1. **Eq. (2):** Pareto p-th tail moment
          ∫_K^∞ x^p · α·L^α·x^{−α−1} dx = α·L^α·K^{p−α} / (α − p),
       generalising `paretoTailExpectation_eq` (p = 1) and recovering
       the survival function (p = 0).
    2. Candidate Beta(1, n) CDF `1 − (1 − y)^n`, its polynomial
       derivative and its algebraic substitution into the candidate
       maximum-CDF expression.
    3. The integral of y against this candidate PDF on `[0, 1]` is
       `1/(n+1)`, with an exact comparison to `1/n`.

  The actual iid sample, maximum law and survival-ratio pushforward
  are not constructed here. Consequently the function identities do
  not yet constitute an exact Beta-law theorem for `(L/K_n)^α`.
  See REVIEW.md, HM-01–HM-20.

  Out of scope:
    * Eq. (1) hidden-moment density (Fréchet form requires change of
      variable on Fréchet density).
    * Eq. (4) Gaussian hidden mass (requires erfc integration).
    * General-`p` hidden moment mean `L^p·n^{p/α−1}·Γ(1−p/α)`
      (Fréchet asymptotic) — requires Γ-function manipulation.
-/
import Stats.Pareto
import Stats.RiskMeasures

open Real Set Filter Topology MeasureTheory Finset

namespace TailOptionPricing

/-! ## Pareto p-th tail moment (paper Eq. 2). -/

/-- **Pareto `p`-th tail moment** above threshold `K`:
        `μ_{K, p}(K) := ∫_K^∞ x^p · paretoDensity(l, α, x) dx`. -/
noncomputable def paretoTailMoment (l α p K : ℝ) : ℝ :=
  ∫ s in Ioi K, s ^ p * paretoDensity l α s

/-- **Closed form (paper Eq. 2):**  For `α > p`, `l > 0`, `l ≤ K`,
        μ_{K, p}(K) = α · l^α · K^{p − α} / (α − p).
    Generalises `paretoTailExpectation_eq` (p = 1) and recovers the
    survival function (p = 0). -/
theorem paretoTailMoment_eq {l α p K : ℝ}
    (_hα : 0 < α) (hl : 0 < l) (hp : p < α) (hK : l ≤ K) :
    paretoTailMoment l α p K = α * l ^ α * K ^ (p - α) / (α - p) := by
  have hK_pos : 0 < K := hl.trans_le hK
  have hαp_pos : 0 < α - p := by linarith
  have hαp_ne : (α - p : ℝ) ≠ 0 := hαp_pos.ne'
  have h_neg : p - α - 1 < -1 := by linarith
  -- Reduce the integrand to a constant times an `rpow`.
  have h_pt : ∀ s ∈ Ioi K,
      s ^ p * paretoDensity l α s = (α * l ^ α) * s ^ (p - α - 1) := by
    intros s hs
    have hs_pos : 0 < s := hK_pos.trans hs
    unfold paretoDensity
    have hs_α1_pos : 0 < s ^ (α + 1) := Real.rpow_pos_of_pos hs_pos _
    have hs_α1_ne : s ^ (α + 1) ≠ 0 := hs_α1_pos.ne'
    have h_split : s ^ p / s ^ (α + 1) = s ^ (p - (α + 1)) := by
      rw [← Real.rpow_sub hs_pos]
    rw [show s ^ p * (α * l ^ α / s ^ (α + 1))
          = (α * l ^ α) * (s ^ p / s ^ (α + 1)) from by ring]
    rw [h_split, show (p - (α + 1) : ℝ) = p - α - 1 from by ring]
  unfold paretoTailMoment
  rw [setIntegral_congr_fun measurableSet_Ioi h_pt,
      MeasureTheory.integral_const_mul,
      integral_Ioi_rpow_of_lt h_neg hK_pos]
  -- ∫_K^∞ s^(p - α - 1) ds = -K^(p-α)/(p-α) = K^(p-α)/(α-p).
  rw [show (p - α - 1 + 1 : ℝ) = p - α from by ring]
  rw [show (p - α : ℝ) = -(α - p) from by ring, neg_div_neg_eq]
  ring

/-- **At p = 0**, the tail moment equals the survival function:
        μ_{K, 0}(K) = (l/K)^α = survival(l, α, K). -/
theorem paretoTailMoment_at_zero {l α K : ℝ}
    (hα : 0 < α) (hl : 0 < l) (hK : l ≤ K) :
    paretoTailMoment l α 0 K = survival l α K := by
  have hα_ne : α ≠ 0 := hα.ne'
  have hK_pos : 0 < K := hl.trans_le hK
  rw [paretoTailMoment_eq hα hl (by linarith : (0:ℝ) < α) hK]
  unfold survival
  rw [show (0 - α : ℝ) = -α from by ring,
      show (α - 0 : ℝ) = α from by ring,
      Real.div_rpow hl.le hK_pos.le, Real.rpow_neg hK_pos.le]
  have hK_α_pos : 0 < K ^ α := Real.rpow_pos_of_pos hK_pos _
  have hK_α_ne : K ^ α ≠ 0 := hK_α_pos.ne'
  field_simp

/-- **At p = 1**, the tail moment equals `paretoTailExpectation`. -/
theorem paretoTailMoment_at_one {l α K : ℝ}
    (hα : 1 < α) (hl : 0 < l) (hK : l ≤ K) :
    paretoTailMoment l α 1 K = paretoTailExpectation l α K := by
  rw [paretoTailMoment_eq (by linarith : (0:ℝ) < α) hl hα hK,
      paretoTailExpectation_eq hα hl hK]

/-! ## Sample survival ratio (paper Remark 1).

    For `X_i` iid strong Pareto on `[l, ∞)` with index `α > 0`, the
    sample maximum `K_n := max X_i` has the *exact* survival
        ℙ(K_n > k) = 1 − paretoSampleMaxCDF n l α k
                   = 1 − (1 − (l/k)^α)^n      for k ≥ l.

    The *sample survival ratio* `Y := (l/K_n)^α` thus has CDF
        ℙ(Y ≤ y) = 1 − (1 − y)^n,
    i.e., `Y ∼ Beta(1, n)` on `[0, 1]` (not exponential).  The paper's
    Remark 1 — "exponential pdf `g_{n,0}(z) = n·e^{−nz}`" — is the
    *Fréchet asymptotic*, where `(1−y)^n ≈ e^{−ny}` for small `y`;
    the **exact** distribution is Beta(1, n), with exact mean
    `1/(n+1)` rather than the paper's `1/n`. -/

/-- **CDF of the sample survival ratio `(L/K_n)^α`** (paper Remark 1,
    exact form): `1 − (1 − y)^n` on `[0, 1]`. -/
noncomputable def paretoSampleSurvivalRatioCDF (n : ℕ) (y : ℝ) : ℝ :=
  1 - (1 - y) ^ n

/-- **PDF of the sample survival ratio**: `n · (1 − y)^(n − 1)`. -/
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

/-- **Exact mean of `(L/K_n)^α = 1 / (n + 1)`** (paper Remark 1,
    exact form).  Computed as
        `∫_0^1 y · n · (1 − y)^(n−1) dy = 1 / (n+1)`
    via FTC with antiderivative
        `F(y) = − y · (1 − y)^n − (1 − y)^(n+1) / (n+1)`.

    The paper's claim "1/n" is the Fréchet asymptotic
    `(1−y)^n ≈ e^{−ny}`; the *exact* value is `1/(n+1)`. -/
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

/-- **Fréchet asymptotic ≈ exact mean.**  As `n → ∞`, the exact mean
    `1/(n+1)` and the Fréchet asymptotic `1/n` agree to leading order:
        `1/n − 1/(n+1) = 1/(n(n+1))` is `O(1/n²)`.
    Quantifies the gap between the paper's stated 1/n and the exact
    1/(n+1). -/
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
