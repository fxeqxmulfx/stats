module

/-
  Source-domain conditional density inputs, arXiv:1912.00277v2, Section II.
  Normalization is required only at positive parent scales. Extending
  the input at nonpositive parents constructs global Markov kernels;
  the actual density integral is proved independent of that extension.
-/
public import Stats.EpistemicUncertainty.DensityInputs

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory

namespace TailOptionPricing

/-- Extend a source conditional density to invalid nonpositive parent
scales by a normalized positive continuous law. Positive parent values
are preserved, and the actual hierarchy never uses the extension. -/
noncomputable def epistemicExtendScalePDF (f : ℝ → ℝ → ENNReal) (s t : ℝ) : ENNReal :=
  if 0 < s then f s t else epistemicUnitIntervalScalePDF s t

theorem epistemicExtendScalePDF_of_pos (f : ℝ → ℝ → ENNReal) {s : ℝ} (hs : 0 < s) (t : ℝ) :
    epistemicExtendScalePDF f s t = f s t := by simp [epistemicExtendScalePDF, hs]

theorem epistemicExtendScalePDF_measurable (f : ℝ → ℝ → ENNReal)
    (hf : Measurable (Function.uncurry f)) :
    Measurable (Function.uncurry (epistemicExtendScalePDF f)) := by
  simpa only [Function.uncurry_def, epistemicExtendScalePDF] using
    Measurable.ite (measurableSet_lt measurable_const measurable_fst) hf
      epistemicUnitIntervalScalePDF_measurable

theorem epistemicExtendScalePDF_lintegral (f : ℝ → ℝ → ENNReal)
    (hn : ∀ s : ℝ, 0 < s → (∫⁻ t in Ioi (0 : ℝ), f s t) = 1) (s : ℝ) :
    (∫⁻ t in Ioi (0 : ℝ), epistemicExtendScalePDF f s t) = 1 := by
  by_cases hs : 0 < s
  · simpa [epistemicExtendScalePDF, hs] using hn s hs
  · simpa [epistemicExtendScalePDF, hs] using epistemicUnitIntervalScalePDF_lintegral s

/-- The source's repeated positive-scale density integral depends only
on positive parent and child values. Thus a global kernel extension
cannot alter the actual source-domain marginal (Section II). -/
theorem epistemicDensityHierarchyIntegral_congr_pos (n : ℕ) (ν : Measure ℝ)
    (f f' : ℕ → ℝ → ℝ → ENNReal) (hν : ∀ᵐ s ∂ν, 0 < s)
    (hf : ∀ i s, 0 < s → ∀ t, 0 < t → f i s t = f' i s t)
    (g g' : ℝ → ENNReal) (hg : ∀ s, 0 < s → g s = g' s) :
    epistemicDensityHierarchyIntegral n ν f g = epistemicDensityHierarchyIntegral n ν f' g' := by
  induction n generalizing g g' with
  | zero =>
    apply lintegral_congr_ae
    filter_upwards [hν] with s hs
    exact hg s hs
  | succ n ih =>
    change epistemicDensityHierarchyIntegral n ν f _ = epistemicDensityHierarchyIntegral n ν f' _
    apply ih
    intro s hs
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem (μ := volume) (s := Ioi (0 : ℝ)) measurableSet_Ioi] with t ht
    have ht₀ : 0 < t := by simpa only [Set.mem_Ioi] using ht
    rw [hf n s hs t ht₀, hg t ht₀]

/-- The global positive-input extension preserves every source density
integral, for an actual prior concentrated on positive dispersion. -/
theorem epistemicDensityHierarchyIntegral_extend (n : ℕ) (ν : Measure ℝ)
    (f : ℕ → ℝ → ℝ → ENNReal) (g : ℝ → ENNReal) (hν : ∀ᵐ s ∂ν, 0 < s) :
    epistemicDensityHierarchyIntegral n ν (fun i => epistemicExtendScalePDF (f i)) g =
      epistemicDensityHierarchyIntegral n ν f g := by
  apply epistemicDensityHierarchyIntegral_congr_pos n ν _ _ hν
  · intro i s hs t ht
    exact epistemicExtendScalePDF_of_pos (f i) hs t
  · intro s hs
    rfl

/-- Actual source-domain hierarchy from positive-parent density inputs,
using the proved harmless global kernel extension (Section II). -/
noncomputable def epistemicPositiveDensityHierarchyLaw (n : ℕ) (μ : ℝ) (ν : Measure ℝ)
    (f : ℕ → ℝ → ℝ → ENNReal) : Measure ℝ :=
  epistemicDensityHierarchyLaw n μ ν (fun i => epistemicExtendScalePDF (f i))

/-- The source assumptions on positive parents suffice to construct
a genuine probability population; no normalization outside R+ is required. -/
theorem epistemicPositiveDensityHierarchyLaw_probability (n : ℕ) (μ : ℝ) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (f : ℕ → ℝ → ℝ → ENNReal)
    (hf : ∀ i, Measurable (Function.uncurry (f i)))
    (hn : ∀ i s, 0 < s → (∫⁻ t in Ioi (0 : ℝ), f i s t) = 1) :
    IsProbabilityMeasure (epistemicPositiveDensityHierarchyLaw n μ ν f) :=
  epistemicDensityHierarchyLaw_probability n μ ν _
    (fun i => epistemicExtendScalePDF_measurable (f i) (hf i))
    (fun i => epistemicExtendScalePDF_lintegral (f i) (hn i))

/-- Section II's corrected actual nested density formula under its
positive-parent assumptions. The final density uses the original f_i,
not the auxiliary extension used to make the global Markov kernels. -/
theorem epistemicPositiveDensityHierarchyLaw_eq_withDensity (n : ℕ) (μ : ℝ) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (f : ℕ → ℝ → ℝ → ENNReal)
    (hf : ∀ i, Measurable (Function.uncurry (f i)))
    (hn : ∀ i s, 0 < s → (∫⁻ t in Ioi (0 : ℝ), f i s t) = 1)
    (hν : ∀ᵐ s ∂ν, 0 < s) :
    epistemicPositiveDensityHierarchyLaw n μ ν f =
      volume.withDensity (epistemicDensityHierarchyPDF n μ ν f) := by
  have h := epistemicDensityHierarchyLaw_eq_withDensity n μ ν _
    (fun i => epistemicExtendScalePDF_measurable (f i) (hf i))
    (fun i => epistemicExtendScalePDF_lintegral (f i) (hn i)) hν
  have he : epistemicDensityHierarchyPDF n μ ν (fun i => epistemicExtendScalePDF (f i)) =
      epistemicDensityHierarchyPDF n μ ν f := by
    funext x
    exact epistemicDensityHierarchyIntegral_extend n ν f _ hν
  rw [he] at h
  exact h

/-- The original source-domain repeated density is measurable, by
its equality with the genuine globally constructed kernel density. -/
theorem epistemicPositiveDensityHierarchyPDF_measurable (n : ℕ) (μ : ℝ) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (f : ℕ → ℝ → ℝ → ENNReal)
    (hf : ∀ i, Measurable (Function.uncurry (f i)))
    (hn : ∀ i s, 0 < s → (∫⁻ t in Ioi (0 : ℝ), f i s t) = 1)
    (hν : ∀ᵐ s ∂ν, 0 < s) : Measurable (epistemicDensityHierarchyPDF n μ ν f) := by
  have hm := epistemicDensityHierarchyPDF_measurable n μ ν _
    (fun i => epistemicExtendScalePDF_measurable (f i) (hf i))
    (fun i => epistemicExtendScalePDF_lintegral (f i) (hn i))
  have he : epistemicDensityHierarchyPDF n μ ν (fun i => epistemicExtendScalePDF (f i)) =
      epistemicDensityHierarchyPDF n μ ν f :=
    funext (fun _ => epistemicDensityHierarchyIntegral_extend n ν f _ hν)
  rwa [he] at hm

/-- The original source-domain repeated density integral is normalized,
deduced from the actual constructed probability population (Section II). -/
theorem epistemicPositiveDensityHierarchyPDF_lintegral (n : ℕ) (μ : ℝ) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (f : ℕ → ℝ → ℝ → ENNReal)
    (hf : ∀ i, Measurable (Function.uncurry (f i)))
    (hn : ∀ i s, 0 < s → (∫⁻ t in Ioi (0 : ℝ), f i s t) = 1)
    (hν : ∀ᵐ s ∂ν, 0 < s) :
    (∫⁻ x : ℝ, epistemicDensityHierarchyPDF n μ ν f x) = 1 := by
  let := epistemicPositiveDensityHierarchyLaw_probability n μ ν f hf hn
  have h := congrArg (fun ρ : Measure ℝ => ρ univ)
    (epistemicPositiveDensityHierarchyLaw_eq_withDensity n μ ν f hf hn hν)
  simpa only [measure_univ, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ] using h.symm

/-- The actual source density is finite Lebesgue-a.e., without a
pointwise finiteness assumption on every nested density integral. -/
theorem epistemicPositiveDensityHierarchyPDF_ae_lt_top (n : ℕ) (μ : ℝ) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (f : ℕ → ℝ → ℝ → ENNReal)
    (hf : ∀ i, Measurable (Function.uncurry (f i)))
    (hn : ∀ i s, 0 < s → (∫⁻ t in Ioi (0 : ℝ), f i s t) = 1)
    (hν : ∀ᵐ s ∂ν, 0 < s) : ∀ᵐ x : ℝ, epistemicDensityHierarchyPDF n μ ν f x < ⊤ := by
  apply ae_lt_top (epistemicPositiveDensityHierarchyPDF_measurable n μ ν f hf hn hν)
  rw [epistemicPositiveDensityHierarchyPDF_lintegral n μ ν f hf hn hν]
  norm_num

example : IsProbabilityMeasure (epistemicPositiveDensityHierarchyLaw 2 1
    (epistemicDensityScalePrior (epistemicUnitIntervalScalePDF 0))
    (fun _ => epistemicPositiveUnitIntervalPDF)) :=
  epistemicPositiveDensityHierarchyLaw_probability _ _ _ _
    (fun _ => epistemicPositiveUnitIntervalPDF_measurable)
    (fun _ _ hs => epistemicPositiveUnitIntervalPDF_lintegral hs)

example (n : ℕ) : (∫⁻ x : ℝ, epistemicDensityHierarchyPDF n 1 (Measure.dirac (2 : ℝ))
    (fun _ => epistemicPositiveUnitIntervalPDF) x) = 1 := by
  apply epistemicPositiveDensityHierarchyPDF_lintegral _ _ _ _
    (fun _ => epistemicPositiveUnitIntervalPDF_measurable)
    (fun _ _ hs => epistemicPositiveUnitIntervalPDF_lintegral hs)
  simpa only [ae_dirac_iff measurableSet_Ioi] using (show (0 : ℝ) < 2 by norm_num)

example : epistemicPositiveDensityHierarchyLaw 2 1 (Measure.dirac (2 : ℝ))
    (fun _ => epistemicPositiveUnitIntervalPDF) = volume.withDensity
      (epistemicDensityHierarchyPDF 2 1 (Measure.dirac (2 : ℝ)) (fun _ => epistemicPositiveUnitIntervalPDF)) := by
  apply epistemicPositiveDensityHierarchyLaw_eq_withDensity _ _ _ _
    (fun _ => epistemicPositiveUnitIntervalPDF_measurable)
    (fun _ _ hs => epistemicPositiveUnitIntervalPDF_lintegral hs)
  simpa only [ae_dirac_iff measurableSet_Ioi] using (show (0 : ℝ) < 2 by norm_num)

example : (∫⁻ t in Ioi (0 : ℝ), epistemicExtendScalePDF epistemicPositiveUnitIntervalPDF 0 t) = 1 :=
  epistemicExtendScalePDF_lintegral _ (fun _ hs => epistemicPositiveUnitIntervalPDF_lintegral hs) _

example : ∀ᵐ x : ℝ, epistemicDensityHierarchyPDF 2 1
    (epistemicDensityScalePrior (epistemicUnitIntervalScalePDF 0))
    (fun _ => epistemicPositiveUnitIntervalPDF) x < ⊤ := by
  apply epistemicPositiveDensityHierarchyPDF_ae_lt_top _ _ _ _
    (fun _ => epistemicPositiveUnitIntervalPDF_measurable)
    (fun _ _ hs => epistemicPositiveUnitIntervalPDF_lintegral hs)
  exact epistemicDensityScalePrior_ae_pos _

example : epistemicDensityHierarchyIntegral 2 (Measure.dirac (2 : ℝ))
    (fun _ => epistemicExtendScalePDF epistemicPositiveUnitIntervalPDF) (fun s => ENNReal.ofReal (s ^ 2)) =
      epistemicDensityHierarchyIntegral 2 (Measure.dirac (2 : ℝ))
        (fun _ => epistemicPositiveUnitIntervalPDF) (fun s => ENNReal.ofReal (s ^ 2)) := by
  apply epistemicDensityHierarchyIntegral_extend
  simpa only [ae_dirac_iff measurableSet_Ioi] using (show (0 : ℝ) < 2 by norm_num)

#print axioms epistemicDensityHierarchyIntegral_extend
#print axioms epistemicPositiveDensityHierarchyLaw_eq_withDensity
#print axioms epistemicPositiveDensityHierarchyPDF_lintegral

end TailOptionPricing
