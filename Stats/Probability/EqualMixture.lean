module

/-
  Actual equal-weight mixture measures for the uncertain-parameter models
  in arXiv:1907.11162v3, Remark 1, and arXiv:1802.05495v3, Eq. 17.
  Normalization and integration are consequences of the measure sum;
  no moment or tail formula is assigned by definition.
-/
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.MeasureTheory.Measure.Prod

@[expose] public section

open Set MeasureTheory

namespace TailOptionPricing

/-- The genuine equal-weight mixture of two population measures. -/
noncomputable def equalMixture {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) : Measure Ω :=
  (1 / 2 : ENNReal) • μ + (1 / 2 : ENNReal) • ν

instance equalMixture_finite {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    IsFiniteMeasure (equalMixture μ ν) := by
  unfold equalMixture
  let := Measure.smul_finite μ (by norm_num : (1 / 2 : ENNReal) ≠ ⊤)
  let := Measure.smul_finite ν (by norm_num : (1 / 2 : ENNReal) ≠ ⊤)
  infer_instance

/-- Both component probabilities give a normalized mixture, as in
the two-component switching models of the cited papers. -/
instance equalMixture_probability {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (equalMixture μ ν) := by
  constructor
  norm_num [equalMixture, Measure.add_apply, Measure.smul_apply, measure_univ]
  exact ENNReal.inv_two_add_inv_two

/-- Real event probabilities are averaged; finiteness is explicit. -/
theorem equalMixture_real {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (s : Set Ω) :
    (equalMixture μ ν).real s = (μ.real s + ν.real s) / 2 := by
  let := Measure.smul_finite μ (by norm_num : (1 / 2 : ENNReal) ≠ ⊤)
  let := Measure.smul_finite ν (by norm_num : (1 / 2 : ENNReal) ≠ ⊤)
  rw [equalMixture, measureReal_add_apply, measureReal_ennreal_smul_apply,
    measureReal_ennreal_smul_apply]
  norm_num
  ring

/-- L1 under the actual mixture is exactly L1 under both components. -/
theorem equalMixture_integrable_iff {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) (f : Ω → ℝ) :
    Integrable f (equalMixture μ ν) ↔ Integrable f μ ∧ Integrable f ν := by
  rw [equalMixture, integrable_add_measure,
    integrable_smul_measure (by norm_num : (1 / 2 : ENNReal) ≠ 0) (by norm_num),
    integrable_smul_measure (by norm_num : (1 / 2 : ENNReal) ≠ 0) (by norm_num)]

/-- Actual mixture expectations are averages only after component L1
has been proved, rather than being defined to be those averages. -/
theorem equalMixture_integral {Ω : Type*} [MeasurableSpace Ω]
    {μ ν : Measure Ω} {f : Ω → ℝ} (hμ : Integrable f μ) (hν : Integrable f ν) :
    (∫ x, f x ∂equalMixture μ ν) = ((∫ x, f x ∂μ) + (∫ x, f x ∂ν)) / 2 := by
  rw [equalMixture, integral_add_measure (hμ.smul_measure (by norm_num))
    (hν.smul_measure (by norm_num)), integral_smul_measure, integral_smul_measure]
  norm_num
  ring

/-- Restricting a mixture restricts its actual component measures. -/
theorem equalMixture_restrict {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) (s : Set Ω) :
    (equalMixture μ ν).restrict s = equalMixture (μ.restrict s) (ν.restrict s) := by
  simp only [equalMixture, Measure.restrict_add, Measure.restrict_smul]

/-- The same integration rule applies to actual truncated payoffs. -/
theorem equalMixture_setIntegral {Ω : Type*} [MeasurableSpace Ω]
    {μ ν : Measure Ω} {s : Set Ω} {f : Ω → ℝ}
    (hμ : IntegrableOn f s μ) (hν : IntegrableOn f s ν) :
    (∫ x in s, f x ∂equalMixture μ ν) =
      ((∫ x in s, f x ∂μ) + (∫ x in s, f x ∂ν)) / 2 := by
  rw [equalMixture_restrict]
  exact equalMixture_integral hμ hν

/-- Measurable population maps preserve the actual mixture construction. -/
theorem equalMixture_map {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ ν : Measure Ω) {f : Ω → Ξ} (hf : Measurable f) :
    (equalMixture μ ν).map f = equalMixture (μ.map f) (ν.map f) := by
  rw [equalMixture, Measure.map_add _ _ hf, Measure.map_smul _ hf.aemeasurable,
    Measure.map_smul _ hf.aemeasurable, equalMixture]

/-- Independent sampling from another law commutes with equal mixing.
This supplies an explicit latent-parameter product model. -/
theorem equalMixture_prod {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ ν : Measure Ω) (ρ : Measure Ξ) [SFinite μ] [SFinite ν] [SFinite ρ] :
    (equalMixture μ ν).prod ρ = equalMixture (μ.prod ρ) (ν.prod ρ) := by
  rw [equalMixture, Measure.add_prod, Measure.prod_smul_left, Measure.prod_smul_left,
    equalMixture]

example : IsProbabilityMeasure (equalMixture (Measure.dirac (3 : ℝ)) (Measure.dirac 7)) :=
  inferInstance

example : Integrable (fun x : ℝ => x)
    (equalMixture (Measure.dirac 3) (Measure.dirac 7)) := by
  rw [equalMixture_integrable_iff]
  constructor <;> exact integrable_dirac (by finiteness)

example : (∫ x : ℝ, x ∂equalMixture (Measure.dirac 3) (Measure.dirac 7)) = 5 := by
  rw [equalMixture_integral (integrable_dirac (by finiteness)) (integrable_dirac (by finiteness))]
  norm_num

example : (∫ x in Ioi (4 : ℝ), x ∂equalMixture (Measure.dirac 3) (Measure.dirac 7)) =
    ((∫ x in Ioi (4 : ℝ), x ∂Measure.dirac 3) +
      (∫ x in Ioi (4 : ℝ), x ∂Measure.dirac 7)) / 2 :=
  equalMixture_setIntegral (integrable_dirac (by finiteness)).integrableOn
    (integrable_dirac (by finiteness)).integrableOn

#print axioms equalMixture_integrable_iff
#print axioms equalMixture_integral
#print axioms equalMixture_setIntegral
#print axioms equalMixture_map

end TailOptionPricing
