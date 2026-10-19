module

/-
  Error function `Real.erf` and complementary error function `erfc`, and
  their connections to `stdNormalCdf`.  Used to state the paper's Eq. (10)
  lower bound `α ≥ log((1/2)·erfc(...))` in the same notation as the paper,
  and the Section IV-D switching-mean κ₁ closed form (Eq. 18) consumed by
  `Stats.Kappa.GaussianSwitchingMean`.

  Both `Real.erf` and `erfc` are defined here through `stdNormalCdf`.
  Their standard integral forms are proved below by the actual Gaussian
  CDF derivative and the fundamental theorem of calculus:
      `erf(x)  = (2/√π) ∫_0^x exp(−t²) dt`,
      `erfc(x) = 1 − (2/√π) ∫_0^x exp(−t²) dt`.
  The latter is the definition used in arXiv:1912.00277v2, Section III.
-/
public import Stats.BlackScholes.CallPrice

@[expose] public section

open Set MeasureTheory Filter Topology
open scoped NNReal

namespace Real

/-- **Error function** (functional definition).  `Real.erf x` is the
    standardised central probability of a `𝒩(0, 1)` variable:
        `Real.erf x = 2 · Φ(x · √2) − 1`,
    matching the standard integral form
        `erf(x) = (2/√π) ∫_0^x exp(−t²) dt`
    via the change of variables `t = u/√2`. The integral form is proved
    by `TailOptionPricing.erf_eq_integral`. -/
noncomputable def erf (x : ℝ) : ℝ :=
  2 * TailOptionPricing.stdNormalCdf (x * Real.sqrt 2) - 1

end Real

namespace TailOptionPricing

/-- **Complementary error function** (functional definition).  `erfc(x)` is
    the standard normal tail rescaled and translated:
        `erfc(x) = 2 · (1 − Φ(x · √2))`.
    The integral form `erfc(x) = 1 − (2/√π) ∫_0^x exp(−t²) dt` is proved
    by `erfc_eq_one_sub_integral`. -/
noncomputable def erfc (x : ℝ) : ℝ := 2 * (1 - stdNormalCdf (x * Real.sqrt 2))

/-- **Complementarity identity**: `Real.erf x + erfc x = 1`. -/
theorem erf_add_erfc (x : ℝ) : Real.erf x + erfc x = 1 := by
  unfold Real.erf erfc
  ring

/-- **Standard normal tail in `erfc` form.**  `1 − Φ(c) = (1/2) · erfc(c/√2)`. -/
theorem one_sub_stdNormalCdf_eq_half_erfc (c : ℝ) :
    1 - stdNormalCdf c = (1/2) * erfc (c / Real.sqrt 2) := by
  unfold erfc
  have h_sqrt_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have h_sqrt_ne : Real.sqrt 2 ≠ 0 := h_sqrt_pos.ne'
  rw [div_mul_cancel₀ c h_sqrt_ne]
  ring

/-- The actual standard Gaussian assigns probability one-half below
zero, by its proved reflection symmetry. -/
theorem stdNormalCdf_zero : stdNormalCdf 0 = 1 / 2 := by
  have h := stdNormalCdf_neg 0
  simp only [neg_zero] at h
  linarith

private theorem gaussianPDFReal_rescale_sqrt_two (x : ℝ) :
    ProbabilityTheory.gaussianPDFReal 0 1 (x * Real.sqrt 2) * Real.sqrt 2 =
      (Real.sqrt Real.pi)⁻¹ * Real.exp (-(x ^ 2)) := by
  have h₂ : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hπ : Real.sqrt Real.pi ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos)
  unfold ProbabilityTheory.gaussianPDFReal
  simp only [NNReal.coe_one, mul_one, sub_zero, mul_pow,
    Real.sq_sqrt (by norm_num : 0 ≤ (2 : ℝ))]
  rw [Real.sqrt_mul (by norm_num : 0 ≤ (2 : ℝ)),
    show -(x ^ 2 * 2) / 2 = -(x ^ 2) by ring]
  field_simp

/-- The actual Gaussian-tail definition of erfc equals the integral
definition in arXiv:1912.00277v2, Section III, below the exceedance formula.
The identity holds for every real endpoint, with an oriented interval. -/
theorem erfc_eq_one_sub_integral (x : ℝ) :
    erfc x = 1 - (2 / Real.sqrt Real.pi) *
      ∫ t in (0 : ℝ)..x, Real.exp (-(t ^ 2)) := by
  have hd (y : ℝ) : HasDerivAt (fun t : ℝ => stdNormalCdf (t * Real.sqrt 2))
      ((Real.sqrt Real.pi)⁻¹ * Real.exp (-(y ^ 2))) y := by
    have h := (stdNormalCdf_hasDerivAt (y * Real.sqrt 2)).comp y
      (hasDerivAt_mul_const (Real.sqrt 2))
    simpa only [Function.comp_def, gaussianPDFReal_rescale_sqrt_two] using h
  have hc : Continuous (fun t : ℝ => (Real.sqrt Real.pi)⁻¹ * Real.exp (-(t ^ 2))) := by
    fun_prop
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y _ => hd y) (hc.intervalIntegrable 0 x)
  rw [intervalIntegral.integral_const_mul, zero_mul, stdNormalCdf_zero] at hi
  unfold erfc
  rw [div_eq_mul_inv]
  linarith

/-- The actual CDF definition of erf has its usual integral form,
the complement of Section III's erfc integral definition. -/
theorem erf_eq_integral (x : ℝ) :
    Real.erf x = (2 / Real.sqrt Real.pi) *
      ∫ t in (0 : ℝ)..x, Real.exp (-(t ^ 2)) := by
  have h := erf_add_erfc x
  rw [erfc_eq_one_sub_integral] at h
  linarith

example : erfc 0 = 1 := by simp [erfc_eq_one_sub_integral]

#print axioms erfc_eq_one_sub_integral
#print axioms erf_eq_integral

open ProbabilityTheory MeasureTheory in
/-- **Risk-neutral lognormal survival in `erfc` form.**  Specialising
    `survivalLN_eq_one_sub_stdNormalCdf` and rewriting via `erfc`:
        `survivalLN S₀ μ v K = (1/2) · erfc((log(K/S₀) − μ)/(√v · √2))`.
    Direct restatement of the paper's `(1/2) erfc(d₂*/√2)` notation. -/
theorem survivalLN_eq_half_erfc {S₀ μ s : ℝ} {v : ℝ≥0}
    (hS₀ : 0 < S₀) (hv : v ≠ 0) (hs : 0 < s) :
    survivalLN S₀ μ v s =
    (1/2) * erfc ((Real.log (s / S₀) - μ) / (Real.sqrt (v : ℝ) * Real.sqrt 2)) := by
  rw [survivalLN_eq_one_sub_stdNormalCdf hS₀ hv hs,
      one_sub_stdNormalCdf_eq_half_erfc]
  congr 2
  rw [div_div]

open ProbabilityTheory MeasureTheory in
/-- **Eq. (10), paper-style `erfc` form.**  Combining the lognormal BS-tail
    dominance theorem with the `erfc` rewrite:
        `α ≥ log((1/2) · erfc((log(K₁/S₀) − μ) / (√v · √2))) / log(l/K₁)`. -/
theorem alpha_lower_bound_erfc
    {l α S₀ μ K₁ a : ℝ} {v : ℝ≥0}
    (hα : 1 < α) (hl : 0 < l) (hK₁ : l < K₁)
    (hS₀ : 0 < S₀) (hv : v ≠ 0) (ha_pos : 0 < a) (ha_lt : a < K₁)
    (h_match : (∫ s in Set.Ioi K₁, survivalLN S₀ μ v s) = callPrice l α K₁)
    (h_butterfly : ∀ᶠ ΔK in 𝓝[>] (0:ℝ),
        callPrice l α (K₁ + ΔK) +
          (∫ s in Set.Ioi (K₁ - ΔK), survivalLN S₀ μ v s)
          ≥ 2 * callPrice l α K₁) :
    Real.log ((1/2) *
        erfc ((Real.log (K₁ / S₀) - μ) /
          (Real.sqrt (v : ℝ) * Real.sqrt 2))) /
      Real.log (l / K₁) ≤ α := by
  have h := BSC_lognormal_tail_dominates_at_match
    hα hl hK₁ hS₀ hv ha_pos ha_lt h_match h_butterfly
  rw [survivalLN_eq_half_erfc hS₀ hv (hl.trans hK₁)] at h
  exact alpha_lower_bound hl hK₁ h

end TailOptionPricing
