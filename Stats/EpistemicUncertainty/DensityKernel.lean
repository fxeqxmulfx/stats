module

/-
  Conditional dispersion kernels from density inputs, arXiv:1912.00277v2,
  Section II's f_i. Joint measurability constructs the actual kernel;
  each density's positive-half-line integral one gives its Markov law.
-/
public import Stats.EpistemicUncertainty.HierarchyDensity
public import Mathlib.Probability.Kernel.WithDensity

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory

namespace TailOptionPricing

/-- A source positive-dispersion prior from its nonnegative Lebesgue
density (Section II, Eq. 1 and the outer uncertainty layer). -/
noncomputable def epistemicDensityScalePrior (p : ℝ → ENNReal) : Measure ℝ :=
  (volume.restrict (Ioi (0 : ℝ))).withDensity p

theorem epistemicDensityScalePrior_probability (p : ℝ → ENNReal)
    (hn : (∫⁻ s in Ioi (0 : ℝ), p s) = 1) :
    IsProbabilityMeasure (epistemicDensityScalePrior p) := by
  constructor
  simpa only [epistemicDensityScalePrior, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ] using hn

theorem epistemicDensityScalePrior_ae_pos (p : ℝ → ENNReal) :
    ∀ᵐ s ∂epistemicDensityScalePrior p, 0 < s := by
  have hp : ∀ᵐ s ∂volume.restrict (Ioi (0 : ℝ)), 0 < s := by
    simpa only [Set.mem_Ioi] using
      (ae_restrict_mem (μ := volume) (s := Ioi (0 : ℝ)) measurableSet_Ioi)
  exact Filter.Eventually.filter_mono (withDensity_absolutelyContinuous _ _).ae_le hp

/-- Section II's conditional scale kernel built from its density on
the positive half-line. The input measurability and normalization
conditions are used in the proved kernel evaluation and Markov theorem. -/
noncomputable def epistemicDensityScaleKernel (f : ℝ → ℝ → ENNReal) : Kernel ℝ ℝ :=
  (Kernel.const ℝ (volume.restrict (Ioi (0 : ℝ)))).withDensity f

/-- The constructed conditional measure really has the prescribed
positive-scale density f_i (Section II). -/
theorem epistemicDensityScaleKernel_apply (f : ℝ → ℝ → ENNReal)
    (hf : Measurable (Function.uncurry f)) (s : ℝ) :
    epistemicDensityScaleKernel f s = (volume.restrict (Ioi (0 : ℝ))).withDensity (f s) := by
  rw [epistemicDensityScaleKernel, Kernel.withDensity_apply _ hf]
  rfl

/-- Normalized conditional density inputs give genuine Markov scale
transitions (Section II). This derives probability laws from the
source density assumptions, rather than assuming the desired marginal. -/
theorem epistemicDensityScaleKernel_markov (f : ℝ → ℝ → ENNReal)
    (hf : Measurable (Function.uncurry f))
    (hn : ∀ s : ℝ, (∫⁻ t in Ioi (0 : ℝ), f s t) = 1) :
    IsMarkovKernel (epistemicDensityScaleKernel f) := by
  constructor
  intro s
  rw [epistemicDensityScaleKernel_apply f hf s]
  constructor
  simpa only [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] using hn s

/-- Every constructed conditional scale law is supported on positive
scales, independently of its incoming state (Section II's R+ domain). -/
theorem epistemicDensityScaleKernel_ae_pos (f : ℝ → ℝ → ENNReal)
    (hf : Measurable (Function.uncurry f)) (s : ℝ) :
    ∀ᵐ t ∂epistemicDensityScaleKernel f s, 0 < t := by
  rw [epistemicDensityScaleKernel_apply f hf s]
  have hp : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), 0 < t := by
    simpa only [Set.mem_Ioi] using
      (ae_restrict_mem (μ := volume) (s := Ioi (0 : ℝ)) measurableSet_Ioi)
  exact Filter.Eventually.filter_mono (withDensity_absolutelyContinuous _ _).ae_le hp

/-- Conditional integration is the actual source density-weighted
positive-half-line integral (Section II). This is the step that turns
the Markov hierarchy's kernel integrals into the literal products of f_i. -/
theorem epistemicDensityScaleKernel_lintegral (f : ℝ → ℝ → ENNReal)
    (hf : Measurable (Function.uncurry f)) (s : ℝ) (g : ℝ → ENNReal) (hg : Measurable g) :
    (∫⁻ t : ℝ, g t ∂epistemicDensityScaleKernel f s) =
      ∫⁻ t in Ioi (0 : ℝ), f s t * g t := by
  simpa only [epistemicDensityScaleKernel, Kernel.const_apply] using
    Kernel.lintegral_withDensity (Kernel.const ℝ (volume.restrict (Ioi (0 : ℝ)))) hf s hg

/-- A concrete continuous conditional dispersion density witnessing
Section II's kernel assumptions. The parent scale shifts its positive
unit interval to (1+s^2,2+s^2], so the transition depends on that scale. -/
noncomputable def epistemicUnitIntervalScalePDF (s t : ℝ) : ENNReal :=
  (Ioc (1 + s ^ 2) (2 + s ^ 2)).indicator (fun _ : ℝ => 1) t

/-- Joint measurability of the concrete conditional density witness. -/
theorem epistemicUnitIntervalScalePDF_measurable :
    Measurable (Function.uncurry epistemicUnitIntervalScalePDF) := by
  classical
  have hA : MeasurableSet {p : ℝ × ℝ | 1 + p.1 ^ 2 < p.2 ∧ p.2 ≤ 2 + p.1 ^ 2} :=
    (measurableSet_lt (by fun_prop) measurable_snd).inter
      (measurableSet_le measurable_snd (by fun_prop))
  simpa only [Function.uncurry_def, epistemicUnitIntervalScalePDF, Set.indicator,
    Set.mem_Ioc] using Measurable.ite hA (measurable_const : Measurable (fun _ : ℝ × ℝ =>
      (1 : ENNReal))) measurable_const

/-- The source-domain integral of each concrete conditional density
is one, proved from positive interval containment and Lebesgue length. -/
theorem epistemicUnitIntervalScalePDF_lintegral (s : ℝ) :
    (∫⁻ t in Ioi (0 : ℝ), epistemicUnitIntervalScalePDF s t) = 1 := by
  unfold epistemicUnitIntervalScalePDF
  rw [lintegral_indicator measurableSet_Ioc, lintegral_one, Measure.restrict_apply_univ,
    Measure.restrict_apply measurableSet_Ioc]
  have hsub : Ioc (1 + s ^ 2) (2 + s ^ 2) ⊆ Ioi (0 : ℝ) := by
    intro t ht
    have h := ht.1
    change 0 < t
    nlinarith [sq_nonneg s]
  rw [Set.inter_eq_left.mpr hsub, Real.volume_Ioc,
    show (2 + s ^ 2) - (1 + s ^ 2) = (1 : ℝ) by ring, ENNReal.ofReal_one]

instance epistemicUnitIntervalScaleKernel_markov :
    IsMarkovKernel (epistemicDensityScaleKernel epistemicUnitIntervalScalePDF) :=
  epistemicDensityScaleKernel_markov _ epistemicUnitIntervalScalePDF_measurable
    epistemicUnitIntervalScalePDF_lintegral

instance epistemicUnitIntervalScalePrior_probability :
    IsProbabilityMeasure (epistemicDensityScalePrior (epistemicUnitIntervalScalePDF 0)) :=
  epistemicDensityScalePrior_probability _ (epistemicUnitIntervalScalePDF_lintegral 0)

/-- A source density specified only at valid positive parents. Its
zero values at nonpositive parents deliberately fail normalization,
so it witnesses the need for the source-domain extension theorem. -/
noncomputable def epistemicPositiveUnitIntervalPDF (s t : ℝ) : ENNReal :=
  if 0 < s then epistemicUnitIntervalScalePDF s t else 0

theorem epistemicPositiveUnitIntervalPDF_measurable :
    Measurable (Function.uncurry epistemicPositiveUnitIntervalPDF) := by
  simpa only [Function.uncurry_def, epistemicPositiveUnitIntervalPDF] using
    Measurable.ite (measurableSet_lt measurable_const measurable_fst)
      epistemicUnitIntervalScalePDF_measurable measurable_const

theorem epistemicPositiveUnitIntervalPDF_lintegral {s : ℝ} (hs : 0 < s) :
    (∫⁻ t in Ioi (0 : ℝ), epistemicPositiveUnitIntervalPDF s t) = 1 := by
  simpa [epistemicPositiveUnitIntervalPDF, hs] using epistemicUnitIntervalScalePDF_lintegral s

example : (∫⁻ t in Ioi (0 : ℝ), epistemicPositiveUnitIntervalPDF 0 t) = 0 := by
  simp [epistemicPositiveUnitIntervalPDF]

example : epistemicDensityScaleKernel epistemicUnitIntervalScalePDF 2 =
    (volume.restrict (Ioi (0 : ℝ))).withDensity (epistemicUnitIntervalScalePDF 2) :=
  epistemicDensityScaleKernel_apply _ epistemicUnitIntervalScalePDF_measurable _

example : IsMarkovKernel (epistemicDensityScaleKernel epistemicUnitIntervalScalePDF) := inferInstance

example : ∀ᵐ t ∂epistemicDensityScaleKernel epistemicUnitIntervalScalePDF 2, 0 < t :=
  epistemicDensityScaleKernel_ae_pos _ epistemicUnitIntervalScalePDF_measurable _

example : (∫⁻ t : ℝ, ENNReal.ofReal (t ^ 2)
    ∂epistemicDensityScaleKernel epistemicUnitIntervalScalePDF 2) =
      ∫⁻ t in Ioi (0 : ℝ), epistemicUnitIntervalScalePDF 2 t * ENNReal.ofReal (t ^ 2) := by
  apply epistemicDensityScaleKernel_lintegral _ epistemicUnitIntervalScalePDF_measurable
  fun_prop

#print axioms epistemicDensityScaleKernel_markov
#print axioms epistemicDensityScaleKernel_ae_pos
#print axioms epistemicUnitIntervalScaleKernel_markov
#print axioms epistemicPositiveUnitIntervalPDF_lintegral

end TailOptionPricing
