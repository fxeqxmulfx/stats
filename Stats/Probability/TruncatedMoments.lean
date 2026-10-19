module

/-
  Actual population moments below and above an observed maximum.
  These are the visible/hidden population integrals in arXiv:2004.05894v1,
  opening decomposition. They are distinct from an arithmetic sample mean.
-/
public import Stats.Probability.HiddenMass
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

open Real Set MeasureTheory

namespace TailOptionPricing

/-- The population moment above the maximum of the observed coordinates. -/
noncomputable def sampleHiddenMoment {n : ℕ} [NeZero n] (ν : Measure ℝ) (p : ℝ)
    (x : Fin n → ℝ) : ℝ :=
  ∫ s in Ioi (sampleMaximum x), s ^ p ∂ν

/-- The population moment up to the observed maximum, without rescaling
the population measure. This is not the arithmetic mean of observations. -/
noncomputable def sampleVisibleMoment {n : ℕ} [NeZero n] (ν : Measure ℝ) (p : ℝ)
    (x : Fin n → ℝ) : ℝ :=
  ∫ s in Iic (sampleMaximum x), s ^ p ∂ν

theorem measurable_sampleHiddenMoment {n : ℕ} [NeZero n] (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (p : ℝ) :
    Measurable (sampleHiddenMoment ν p : (Fin n → ℝ) → ℝ) := by
  have hm : Measurable (Function.uncurry (fun (x : Fin n → ℝ) (s : ℝ) =>
      (Ioi (sampleMaximum x)).indicator (fun s => s ^ p) s)) := by
    change Measurable (fun z : (Fin n → ℝ) × ℝ =>
      if sampleMaximum z.1 < z.2 then z.2 ^ p else 0)
    exact Measurable.ite
      (measurableSet_lt (measurable_sampleMaximum.comp measurable_fst) measurable_snd)
      (measurable_snd.pow_const p) measurable_const
  change Measurable (fun x : Fin n → ℝ => ∫ s in Ioi (sampleMaximum x), s ^ p ∂ν)
  simpa only [integral_indicator measurableSet_Ioi] using
    (hm.stronglyMeasurable.integral_prod_right (ν := ν)).measurable

theorem measurable_sampleVisibleMoment {n : ℕ} [NeZero n] (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (p : ℝ) :
    Measurable (sampleVisibleMoment ν p : (Fin n → ℝ) → ℝ) := by
  have hm : Measurable (Function.uncurry (fun (x : Fin n → ℝ) (s : ℝ) =>
      (Iic (sampleMaximum x)).indicator (fun s => s ^ p) s)) := by
    change Measurable (fun z : (Fin n → ℝ) × ℝ =>
      if z.2 ≤ sampleMaximum z.1 then z.2 ^ p else 0)
    exact Measurable.ite
      (measurableSet_le measurable_snd (measurable_sampleMaximum.comp measurable_fst))
      (measurable_snd.pow_const p) measurable_const
  change Measurable (fun x : Fin n → ℝ => ∫ s in Iic (sampleMaximum x), s ^ p ∂ν)
  simpa only [integral_indicator measurableSet_Iic] using
    (hm.stronglyMeasurable.integral_prod_right (ν := ν)).measurable

/-- Integrability of the population moment suffices for its decomposition
at every observed maximum; no independence assumption is needed here. -/
theorem sampleMoment_decomposition {n : ℕ} [NeZero n] (ν : Measure ℝ) (p : ℝ)
    (hp : Integrable (fun s : ℝ => s ^ p) ν) (x : Fin n → ℝ) :
    (∫ s : ℝ, s ^ p ∂ν) = sampleVisibleMoment ν p x + sampleHiddenMoment ν p x := by
  simpa only [sampleVisibleMoment, sampleHiddenMoment, compl_Iic] using
    (integral_add_compl (s := Iic (sampleMaximum x)) measurableSet_Iic hp).symm

/-- The actual hidden moment is an integrable random variable under the
product sample law when the corresponding population moment is integrable. -/
theorem sampleHiddenMoment_integrable {n : ℕ} [NeZero n] (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (p : ℝ) (hp : Integrable (fun s : ℝ => s ^ p) ν) :
    Integrable (sampleHiddenMoment ν p : (Fin n → ℝ) → ℝ) (iidSampleLaw n ν) := by
  apply (integrable_const (∫ s : ℝ, ‖s ^ p‖ ∂ν)).mono'
    (measurable_sampleHiddenMoment ν p).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro x
  exact (norm_integral_le_integral_norm (μ := ν.restrict (Ioi (sampleMaximum x)))
    (fun s : ℝ => s ^ p)).trans
    (setIntegral_le_integral hp.norm (Filter.Eventually.of_forall (fun _ => norm_nonneg _)))

theorem sampleVisibleMoment_integrable {n : ℕ} [NeZero n] (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (p : ℝ) (hp : Integrable (fun s : ℝ => s ^ p) ν) :
    Integrable (sampleVisibleMoment ν p : (Fin n → ℝ) → ℝ) (iidSampleLaw n ν) := by
  apply (integrable_const (∫ s : ℝ, ‖s ^ p‖ ∂ν)).mono'
    (measurable_sampleVisibleMoment ν p).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro x
  exact (norm_integral_le_integral_norm (μ := ν.restrict (Iic (sampleMaximum x)))
    (fun s : ℝ => s ^ p)).trans
    (setIntegral_le_integral hp.norm (Filter.Eventually.of_forall (fun _ => norm_nonneg _)))

/-- The expected visible and hidden population moments sum to the true
population moment, with both sample-space integrals justified by L1. -/
theorem expected_sampleMoment_decomposition {n : ℕ} [NeZero n] (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (p : ℝ) (hp : Integrable (fun s : ℝ => s ^ p) ν) :
    (∫ x : Fin n → ℝ, sampleVisibleMoment ν p x ∂iidSampleLaw n ν) +
      (∫ x : Fin n → ℝ, sampleHiddenMoment ν p x ∂iidSampleLaw n ν) = ∫ s : ℝ, s ^ p ∂ν := by
  rw [← integral_add (sampleVisibleMoment_integrable ν p hp) (sampleHiddenMoment_integrable ν p hp)]
  simp_rw [← sampleMoment_decomposition ν p hp]
  simp

theorem sampleHiddenMoment_zero {n : ℕ} [NeZero n] (ν : Measure ℝ) (x : Fin n → ℝ) :
    sampleHiddenMoment ν 0 x = sampleHiddenMass ν x := by
  simp only [sampleHiddenMoment, sampleHiddenMass, Real.rpow_zero, setIntegral_const,
    smul_eq_mul, mul_one]

end TailOptionPricing
