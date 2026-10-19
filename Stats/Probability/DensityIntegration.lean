module

/-
  Actual-law integration for nonnegative measurable real densities.
  These bridges give arXiv:1907.11162v3, Definition 5 and Theorem 1,
  their density/expectation interpretation without assuming a payoff value.
-/
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Probability.Distributions.Exponential

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory Filter Topology

namespace TailOptionPricing

/-- Restricted integration against the actual density-generated measure. -/
theorem realDensity_setIntegral (f : ℝ → ℝ) (hm : Measurable f)
    (hn : ∀ x, 0 ≤ f x) (g : ℝ → ℝ) (s : Set ℝ) :
    (∫ x in s, g x ∂volume.withDensity (fun x => ENNReal.ofReal (f x))) =
      ∫ x in s, g x * f x := by
  have hmf : Measurable (fun x : ℝ => ENNReal.ofReal (f x)) :=
    ENNReal.measurable_ofReal.comp hm
  rw [setIntegral_withDensity_eq_setIntegral_toReal_smul' s
    hmf
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp_rw [ENNReal.toReal_ofReal (hn _), smul_eq_mul]
  congr 1
  funext x
  exact mul_comm _ _

/-- The genuine tail L1 condition is equivalent to L1 of its density-
weighted payoff on the same measurable set (paper Definition 5). -/
theorem realDensity_integrableOn_iff (f : ℝ → ℝ) (hm : Measurable f)
    (hn : ∀ x, 0 ≤ f x) (g : ℝ → ℝ) {s : Set ℝ} (hs : MeasurableSet s) :
    IntegrableOn g s (volume.withDensity (fun x => ENNReal.ofReal (f x))) ↔
      IntegrableOn (fun x => g x * f x) s := by
  have hmf : Measurable (fun x : ℝ => ENNReal.ofReal (f x)) :=
    ENNReal.measurable_ofReal.comp hm
  rw [IntegrableOn, restrict_withDensity hs,
    integrable_withDensity_iff hmf
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (hn _)]
  rfl

-- The supported, normalized Exp(2) law supplies concrete density hypotheses.
example : (∫ x in Ioi (3 : ℝ), x ∂expMeasure 2) =
    ∫ x in Ioi (3 : ℝ), x * exponentialPDFReal 2 x := by
  change (∫ x in Ioi (3 : ℝ), x ∂volume.withDensity
    (fun x => ENNReal.ofReal (exponentialPDFReal 2 x))) = _
  exact realDensity_setIntegral _ (measurable_exponentialPDFReal 2)
    (exponentialPDFReal_nonneg (by norm_num)) _ _

example : IntegrableOn (fun x : ℝ => x) (Ioi 3) (expMeasure 2) ↔
    IntegrableOn (fun x : ℝ => x * exponentialPDFReal 2 x) (Ioi 3) := by
  change IntegrableOn (fun x : ℝ => x) (Ioi 3)
    (volume.withDensity (fun x => ENNReal.ofReal (exponentialPDFReal 2 x))) ↔ _
  exact realDensity_integrableOn_iff _ (measurable_exponentialPDFReal 2)
    (exponentialPDFReal_nonneg (by norm_num)) _ measurableSet_Ioi

#print axioms realDensity_setIntegral
#print axioms realDensity_integrableOn_iff

end TailOptionPricing
