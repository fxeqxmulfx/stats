module

/-
  The actual hidden mass under the true finite iid Pareto sample has the
  Beta(1,n) measure. This corrects arXiv:2004.05894v1, Remark 1
  and supplies a law from which genuine moments can be calculated.
-/
public import Stats.HiddenMoments.BetaKernel
public import Stats.HiddenMoments.SurvivalMass

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory

namespace TailOptionPricing

/-- The actual hidden-mass pushforward is the normalized supported
Beta(1,n) measure, correcting the exponential claim in arXiv:2004.05894v1, Remark 1. -/
theorem paretoHiddenMass_map_beta {n : ℕ} [NeZero n] {l a : ℝ} (hl : 0 < l) (ha : 0 < a) :
    (iidSampleLaw n (paretoMeasure l a)).map
      (sampleHiddenMass (paretoMeasure l a)) =
        betaMeasure 1 n := by
  let : IsProbabilityMeasure (paretoMeasure l a) :=
    instIsProbabilityMeasureParetoMeasure l a hl ha
  let : IsProbabilityMeasure (betaMeasure 1 n) :=
    isProbabilityMeasureBeta (by norm_num) (Nat.cast_pos.mpr (NeZero.pos n))
  apply Measure.ext_of_Iic
  intro y
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  rw [Measure.map_apply (measurable_sampleHiddenMass _) measurableSet_Iic]
  change (iidSampleLaw n (paretoMeasure l a)).real
      {x | sampleHiddenMass (paretoMeasure l a) x ≤ y} =
      (betaMeasure 1 n).real (Iic y)
  rw [paretoHiddenMass_cdf hl ha, betaMeasure_one_nat_cdf (NeZero.pos n)]

/-- Identical distribution with the identity under Beta(1,n), from the
actual pushforward equality (arXiv:2004.05894v1, Remark 1 correction). -/
theorem paretoHiddenMass_identDistrib_beta {n : ℕ} [NeZero n] {l a : ℝ}
    (hl : 0 < l) (ha : 0 < a) :
    IdentDistrib (sampleHiddenMass (paretoMeasure l a)) (id : ℝ → ℝ)
      (iidSampleLaw n (paretoMeasure l a)) (betaMeasure 1 n) := by
  let : IsProbabilityMeasure (paretoMeasure l a) :=
    instIsProbabilityMeasureParetoMeasure l a hl ha
  exact ⟨(measurable_sampleHiddenMass _).aemeasurable, measurable_id.aemeasurable,
    by simpa using paretoHiddenMass_map_beta hl ha⟩

/-- Integrability of actual hidden-mass powers above -1, obtained from
the true Beta law (arXiv:2004.05894v1, Remark 1 correction). -/
theorem paretoHiddenMass_integrable_rpow {n : ℕ} [NeZero n] {l a q : ℝ}
    (hl : 0 < l) (ha : 0 < a) (hq : 0 < 1 + q) :
    Integrable (fun x : Fin n → ℝ => (sampleHiddenMass (paretoMeasure l a) x) ^ q)
      (iidSampleLaw n (paretoMeasure l a)) := by
  exact ((paretoHiddenMass_identDistrib_beta hl ha).comp
    (measurable_id.pow_const q)).integrable_iff.mpr
    (betaMeasure_integrable_rpow (by norm_num) (Nat.cast_pos.mpr (NeZero.pos n)) hq)

/-- Actual hidden-mass power expectation from its proved Beta law,
for powers above -1 (arXiv:2004.05894v1, Proposition 1 and Remark 1 correction). -/
theorem paretoHiddenMass_integral_rpow {n : ℕ} [NeZero n] {l a q : ℝ}
    (hl : 0 < l) (ha : 0 < a) (hq : 0 < 1 + q) :
    ∫ x : Fin n → ℝ, (sampleHiddenMass
      (paretoMeasure l a) x) ^ q
      ∂iidSampleLaw n (paretoMeasure l a) =
      ProbabilityTheory.beta (1 + q) n / ProbabilityTheory.beta 1 n := by
  have hd := paretoHiddenMass_identDistrib_beta (n := n) hl ha
  have he := (hd.comp (measurable_id.pow_const q)).integral_eq
  change (∫ x : Fin n → ℝ, (sampleHiddenMass
      (paretoMeasure l a) x) ^ q
      ∂iidSampleLaw n (paretoMeasure l a)) =
      ∫ y : ℝ, y ^ q ∂betaMeasure 1 n at he
  rw [he, betaMeasure_integral_rpow (by norm_num) (Nat.cast_pos.mpr (NeZero.pos n)) hq]

end TailOptionPricing
