module

/-
  Actual finite-sample density of the hidden p-th moment,
  arXiv:2004.05894v1, Proposition 1 correction. For a proper
  strong-Pareto population and p<a, set C=a*l^p/(a-p) and
  r=(a-p)/a>0. The actual moment equals C*H^r for H~Beta(1,n).
  The resulting density is supported on (0,C), with its exact
  finite Beta factor. The source's exponential factor instead
  comes from a Frechet approximation to the sample maximum.
  The finite support bound is also proved from the actual observed
  maximum, independently of choosing a density representative.
-/
public import Stats.HiddenMoments.MomentMean
public import Stats.Probability.PowerBeta

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory Filter

namespace TailOptionPricing

/-- The explicit finite hidden-moment density. Expanding powerBetaPDF
gives n/(r*C)*(z/C)^(1/r-1)*(1-(z/C)^(1/r))^(n-1) on (0,C),
zero elsewhere, where C=a*l^p/(a-p), r=(a-p)/a (Proposition 1). -/
noncomputable def paretoHiddenMomentPDF (n : ℕ) (l a p z : ℝ) : ℝ :=
  powerBetaPDF n (a * l ^ p / (a - p)) ((a - p) / a) z

/-- Both transform parameters are positive on Proposition 1's proper
Pareto moment domain; negative orders p are allowed. -/
theorem paretoHiddenMoment_power_parameters_pos {l a p : ℝ}
    (hl : 0 < l) (ha : 0 < a) (hp : p < a) :
    0 < a * l ^ p / (a - p) ∧ 0 < (a - p) / a :=
  ⟨div_pos (mul_pos ha (Real.rpow_pos_of_pos hl p)) (sub_pos.mpr hp),
    div_pos (sub_pos.mpr hp) ha⟩

theorem measurable_paretoHiddenMomentPDF (n : ℕ) (l a p : ℝ) :
    Measurable (paretoHiddenMomentPDF n l a p) := measurable_powerBetaPDF _ _ _

/-- Whole probability law of the actual hidden p-th moment under
the iid sample, with the explicit supported density and Jacobian.
This replaces the finite-sample reading of the printed Frechet density
in arXiv:2004.05894v1, Proposition 1. No desired PDF law is assumed. -/
theorem paretoHiddenMoment_map_density {n : ℕ} [NeZero n] {l a p : ℝ}
    (hl : 0 < l) (ha : 0 < a) (hp : p < a) :
    (iidSampleLaw n (paretoMeasure l a)).map (sampleHiddenMoment (paretoMeasure l a) p) =
      volume.withDensity (fun z => ENNReal.ofReal (paretoHiddenMomentPDF n l a p z)) := by
  obtain ⟨hC, hr⟩ := paretoHiddenMoment_power_parameters_pos hl ha hp
  rw [paretoHiddenMoment_map_beta_rpow hl ha hp]
  change (betaMeasure 1 n).map
    (positivePower (a * l ^ p / (a - p)) ((a - p) / a)) = _
  exact betaMeasure_map_positivePower (NeZero.pos n) hC hr

/-- The corrected finite density is nonnegative everywhere, with no
restriction on p beyond p<a (Proposition 1). -/
theorem paretoHiddenMomentPDF_nonneg {n : ℕ} [NeZero n] {l a p : ℝ}
    (hl : 0 < l) (ha : 0 < a) (hp : p < a) (z : ℝ) :
    0 ≤ paretoHiddenMomentPDF n l a p z := by
  obtain ⟨hC, hr⟩ := paretoHiddenMoment_power_parameters_pos hl ha hp
  exact powerBetaPDF_nonneg (NeZero.pos n) hC hr z

/-- Strict positivity on the true finite support, rather than all
positive z as in the printed Frechet-model formula (Proposition 1). -/
theorem paretoHiddenMomentPDF_pos {n : ℕ} [NeZero n] {l a p z : ℝ}
    (hl : 0 < l) (ha : 0 < a) (hp : p < a) (hz : z ∈ Ioo 0 (a * l ^ p / (a - p))) :
    0 < paretoHiddenMomentPDF n l a p z := by
  obtain ⟨hC, hr⟩ := paretoHiddenMoment_power_parameters_pos hl ha hp
  exact powerBetaPDF_pos (NeZero.pos n) hC hr hz

/-- The actual finite density is zero outside (0,C); the endpoint
values are a chosen density representative, not claims about atoms. -/
theorem paretoHiddenMomentPDF_eq_zero {n : ℕ} {l a p z : ℝ}
    (hz : z ∉ Ioo 0 (a * l ^ p / (a - p))) : paretoHiddenMomentPDF n l a p z = 0 := by
  unfold paretoHiddenMomentPDF powerBetaPDF
  exact indicator_of_notMem hz _

/-- Unit mass of the corrected density follows from the actual Beta
law and the proved measurable transformation (Proposition 1). -/
theorem paretoHiddenMomentPDF_probability {n : ℕ} [NeZero n] {l a p : ℝ}
    (hl : 0 < l) (ha : 0 < a) (hp : p < a) :
    IsProbabilityMeasure (volume.withDensity
      (fun z => ENNReal.ofReal (paretoHiddenMomentPDF n l a p z))) := by
  obtain ⟨hC, hr⟩ := paretoHiddenMoment_power_parameters_pos hl ha hp
  exact powerBetaPDF_probability (NeZero.pos n) hC hr

/-- The actual displayed density is L1 and has integral one, proved
after constructing its genuine probability measure (Proposition 1). -/
theorem paretoHiddenMomentPDF_integrable_integral {n : ℕ} [NeZero n] {l a p : ℝ}
    (hl : 0 < l) (ha : 0 < a) (hp : p < a) :
    Integrable (paretoHiddenMomentPDF n l a p) ∧
      (∫ z : ℝ, paretoHiddenMomentPDF n l a p z) = 1 := by
  obtain ⟨hC, hr⟩ := paretoHiddenMoment_power_parameters_pos hl ha hp
  exact powerBetaPDF_integrable_integral (NeZero.pos n) hC hr

/-- The actual sample hidden moment lies strictly between zero and
its population p-th moment almost surely. This support is proved
from the actual maximum and Eq. 2, independently of a PDF definition. -/
theorem sampleHiddenMoment_pareto_ae_mem_Ioo {n : ℕ} [NeZero n] {l a p : ℝ}
    (hl : 0 < l) (ha : 0 < a) (hp : p < a) :
    ∀ᵐ x ∂iidSampleLaw n (paretoMeasure l a),
      sampleHiddenMoment (paretoMeasure l a) p x ∈ Ioo 0 (a * l ^ p / (a - p)) := by
  obtain ⟨hC, hr⟩ := paretoHiddenMoment_power_parameters_pos hl ha hp
  filter_upwards [sampleHiddenMoment_pareto_eq_hiddenMass_rpow hl ha hp,
    sampleHiddenMass_pareto_eq hl ha, paretoSampleMaximum_ae_gt hl ha] with x hx hH hK
  have hK₀ := hl.trans hK
  have hH₀ : 0 < sampleHiddenMass (paretoMeasure l a) x := by
    rw [hH]
    exact Real.rpow_pos_of_pos (div_pos hl hK₀) a
  have hH₁ : sampleHiddenMass (paretoMeasure l a) x < 1 := by
    rw [hH]
    exact Real.rpow_lt_one (div_pos hl hK₀).le ((div_lt_one hK₀).mpr hK) ha
  have ht := Real.rpow_lt_one hH₀.le hH₁ hr
  rw [hx]
  exact ⟨mul_pos hC (Real.rpow_pos_of_pos hH₀ _), by nlinarith⟩

example : 0 < (2 : ℝ) * 1 ^ (1 : ℝ) / (2 - 1) ∧ 0 < ((2 : ℝ) - 1) / 2 :=
  paretoHiddenMoment_power_parameters_pos (by norm_num) (by norm_num) (by norm_num)

example : (iidSampleLaw 2 (paretoMeasure 1 2)).map (sampleHiddenMoment (paretoMeasure 1 2) 1) =
    volume.withDensity (fun z => ENNReal.ofReal (paretoHiddenMomentPDF 2 1 2 1 z)) :=
  paretoHiddenMoment_map_density (by norm_num) (by norm_num) (by norm_num)

example (z : ℝ) : 0 ≤ paretoHiddenMomentPDF 2 1 2 1 z :=
  paretoHiddenMomentPDF_nonneg (by norm_num) (by norm_num) (by norm_num) _

example : 0 < paretoHiddenMomentPDF 2 1 2 1 1 :=
  paretoHiddenMomentPDF_pos (by norm_num) (by norm_num) (by norm_num) (by norm_num)

example : paretoHiddenMomentPDF 2 1 2 1 3 = 0 := paretoHiddenMomentPDF_eq_zero (by norm_num)

example : IsProbabilityMeasure (volume.withDensity
    (fun z => ENNReal.ofReal (paretoHiddenMomentPDF 2 1 2 1 z))) :=
  paretoHiddenMomentPDF_probability (by norm_num) (by norm_num) (by norm_num)

example : Integrable (paretoHiddenMomentPDF 2 1 2 1) ∧
    (∫ z : ℝ, paretoHiddenMomentPDF 2 1 2 1 z) = 1 :=
  paretoHiddenMomentPDF_integrable_integral (by norm_num) (by norm_num) (by norm_num)

example : ∀ᵐ x ∂iidSampleLaw 2 (paretoMeasure 1 2),
    sampleHiddenMoment (paretoMeasure 1 2) 1 x ∈ Ioo 0 ((2 : ℝ) * 1 ^ (1 : ℝ) / (2 - 1)) :=
  sampleHiddenMoment_pareto_ae_mem_Ioo (by norm_num) (by norm_num) (by norm_num)

#print axioms paretoHiddenMoment_map_density
#print axioms paretoHiddenMomentPDF_nonneg
#print axioms paretoHiddenMomentPDF_pos
#print axioms paretoHiddenMomentPDF_probability
#print axioms paretoHiddenMomentPDF_integrable_integral
#print axioms sampleHiddenMoment_pareto_ae_mem_Ioo

end TailOptionPricing
