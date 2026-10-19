module

/-
  Standard Gaussian Mills-ratio asymptotics for arXiv:1907.11162v3,
  Theorem 1, Thin tails / Eq. 6. The CDF is the actual N(0,1) CDF.
  L'Hopital's rule proves the missing ratio limit from its derivatives.
-/
public import Stats.BlackScholes.StdNormal
public import Mathlib.Analysis.Calculus.LHopital

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory Filter Topology

namespace TailOptionPricing

/-- The standard-normal survival is asymptotic to its PDF divided by
the threshold, supplying the Gaussian case of arXiv:1907.11162v3, Theorem 1. -/
theorem stdNormal_survival_mills_tendsto :
    Tendsto (fun x : ℝ => (1 - stdNormalCdf x) / (gaussianPDFReal 0 1 x / x))
      atTop (𝓝 1) := by
  have hφ (x : ℝ) : HasDerivAt (fun y : ℝ => gaussianPDFReal 0 1 y)
      (-x * gaussianPDFReal 0 1 x) x := by
    convert (hasDerivAt_neg_gaussianPDFReal_std x).neg using 1
    · funext y
      change gaussianPDFReal 0 1 y = -(-gaussianPDFReal 0 1 y)
      ring
    · ring
  have hF : ∀ᶠ x : ℝ in atTop, HasDerivAt (fun y => 1 - stdNormalCdf y)
      (-gaussianPDFReal 0 1 x) x :=
    Filter.Eventually.of_forall (fun x => (stdNormalCdf_hasDerivAt x).const_sub 1)
  have hG : ∀ᶠ x : ℝ in atTop, HasDerivAt (fun y => gaussianPDFReal 0 1 y / y)
      (-gaussianPDFReal 0 1 x * (1 + (x⁻¹) ^ 2)) x := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have hq := (hφ x).div (hasDerivAt_id x) hx.ne'
    change HasDerivAt (fun y : ℝ => gaussianPDFReal 0 1 y / y)
      (((-x * gaussianPDFReal 0 1 x) * x - gaussianPDFReal 0 1 x * 1) / x ^ 2) x at hq
    convert hq using 1
    have hxn := hx.ne'
    field_simp
    ring
  have hn : ∀ᶠ x : ℝ in atTop, -gaussianPDFReal 0 1 x * (1 + (x⁻¹) ^ 2) ≠ 0 := by
    apply Filter.Eventually.of_forall
    intro x
    exact mul_ne_zero (neg_ne_zero.mpr (gaussianPDFReal_pos 0 1 x one_ne_zero).ne')
      (by positivity)
  have hF0 : Tendsto (fun x : ℝ => 1 - stdNormalCdf x) atTop (𝓝 0) := by
    simpa only [sub_self] using
      (tendsto_const_nhds (x := (1 : ℝ))).sub tendsto_stdNormalCdf_atTop_one
  have hG0 : Tendsto (fun x : ℝ => gaussianPDFReal 0 1 x / x) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      tendsto_gaussianPDFReal_std_atTop.mul tendsto_inv_atTop_zero
  have hd0 : Tendsto (fun x : ℝ => 1 + (x⁻¹) ^ 2) atTop (𝓝 1) := by
    have hinv : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 (0 : ℝ)) := tendsto_inv_atTop_zero
    simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero] using
      (hinv.pow 2).const_add 1
  have hdiv : Tendsto (fun x : ℝ => (-gaussianPDFReal 0 1 x) /
      (-gaussianPDFReal 0 1 x * (1 + (x⁻¹) ^ 2))) atTop (𝓝 1) := by
    have hlim : Tendsto (fun x : ℝ => (1 + (x⁻¹) ^ 2)⁻¹) atTop (𝓝 1) := by
      simpa only [inv_one] using hd0.inv₀ (by norm_num)
    apply hlim.congr
    intro x
    have hp : gaussianPDFReal 0 1 x ≠ 0 := (gaussianPDFReal_pos 0 1 x one_ne_zero).ne'
    have hden : 1 + (x⁻¹) ^ 2 ≠ 0 := by positivity
    field_simp
  exact HasDerivAt.lhopital_zero_atTop hF hG hn hF0 hG0 hdiv

/-- The standard Gaussian first-tail-moment ratio tends to one
(arXiv:1907.11162v3, Theorem 1's centered normalized Gaussian case). -/
theorem stdNormal_characteristicScale_tendsto :
    Tendsto (fun x : ℝ => gaussianPDFReal 0 1 x / (x * (1 - stdNormalCdf x)))
      atTop (𝓝 1) := by
  have hlim := stdNormal_survival_mills_tendsto.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  simp only [inv_one] at hlim
  apply hlim.congr
  intro x
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

#print axioms stdNormal_survival_mills_tendsto
#print axioms stdNormal_characteristicScale_tendsto

end TailOptionPricing
