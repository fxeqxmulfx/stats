module

/-
  Actual exponential-law integration and L1 bridges for density payoffs.
  Used to assess arXiv:1907.11162v3, Definition 5, with a normalized
  supported probability density rather than a global unnormalized kernel.
-/
public import Mathlib.Probability.Distributions.Exponential
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory Filter Topology

namespace TailOptionPricing

/-- Integration against the actual supported exponential law equals
the supported density integral, for every real-valued function and set. -/
theorem expMeasure_setIntegral {r : ℝ} (hr : 0 < r) (g : ℝ → ℝ) (s : Set ℝ) :
    (∫ x in s, g x ∂expMeasure r) = ∫ x in s, g x * exponentialPDFReal r x := by
  have hm : Measurable (exponentialPDF r) :=
    ENNReal.measurable_ofReal.comp (measurable_exponentialPDFReal r)
  change (∫ x in s, g x ∂volume.withDensity (exponentialPDF r)) = _
  rw [setIntegral_withDensity_eq_setIntegral_toReal_smul' s hm
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp_rw [smul_eq_mul, exponentialPDF,
    ENNReal.toReal_ofReal (exponentialPDFReal_nonneg hr _)]
  congr 1
  funext x
  exact mul_comm _ _

/-- The actual exponential-law L1 condition is precisely integrability
of the supported density-weighted function on the same measurable set. -/
theorem expMeasure_integrableOn_iff {r : ℝ} (hr : 0 < r) (g : ℝ → ℝ) (s : Set ℝ)
    (hs : MeasurableSet s) :
    IntegrableOn g s (expMeasure r) ↔
      IntegrableOn (fun x => g x * exponentialPDFReal r x) s := by
  have hm : Measurable (exponentialPDF r) :=
    ENNReal.measurable_ofReal.comp (measurable_exponentialPDFReal r)
  change Integrable g ((volume.withDensity (exponentialPDF r)).restrict s) ↔ _
  rw [restrict_withDensity hs, integrable_withDensity_iff hm
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp_rw [exponentialPDF, ENNReal.toReal_ofReal (exponentialPDFReal_nonneg hr _)]
  rfl

/-- The real supported exponential PDF integrates to one for positive rate. -/
theorem integral_exponentialPDFReal {r : ℝ} (hr : 0 < r) :
    (∫ x : ℝ, exponentialPDFReal r x) = 1 := by
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall (exponentialPDFReal_nonneg hr))
    (measurable_exponentialPDFReal r).aestronglyMeasurable]
  change (∫⁻ x : ℝ, exponentialPDF r x).toReal = 1
  rw [lintegral_exponentialPDF_eq_one hr, ENNReal.toReal_one]

/-- The supported real PDF agrees with the exponential kernel on the
nonnegative half-line, including the support boundary. -/
theorem exponentialPDFReal_of_nonneg {r x : ℝ} (hx : 0 ≤ x) :
    exponentialPDFReal r x = r * Real.exp (-(r * x)) := by
  simp [exponentialPDFReal, gammaPDFReal, hx]

end TailOptionPricing
