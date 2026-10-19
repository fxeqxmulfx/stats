module

/-
  Exact finite-sample hidden p-th moment law and expectation for an iid
  strong Pareto sample (arXiv:2004.05894v1, Eq. 2 and Proposition 1).
  The source uses a Frechet approximation; the corrected exact mean is
  l^p * Gamma(r) * Gamma(n+1) / Gamma(n+1+r), with r=(alpha-p)/alpha>0.
-/
public import Stats.HiddenMoments.Decomposition
public import Stats.HiddenMoments.BetaLaw

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory

namespace TailOptionPricing

/-- Eq. 2 as a power of the actual hidden probability mass, almost surely
under the genuine iid sample law (arXiv:2004.05894v1, section 1). -/
theorem sampleHiddenMoment_pareto_eq_hiddenMass_rpow {n : ℕ} [NeZero n] {l a p : ℝ}
    (hl : 0 < l) (ha : 0 < a) (hp : p < a) :
    ∀ᵐ x ∂iidSampleLaw n (paretoMeasure l a),
      sampleHiddenMoment (paretoMeasure l a) p x =
      (a * l ^ p / (a - p)) *
        (sampleHiddenMass (paretoMeasure l a) x) ^
          ((a - p) / a) := by
  filter_upwards [sampleHiddenMoment_pareto_closed_form (n := n) hl ha hp,
    sampleHiddenMass_pareto_eq (n := n) hl ha,
    paretoSampleMaximum_ae_gt (n := n) hl ha] with x hm hh hk
  have hk0 := hl.trans hk
  rw [hm, hh, ← Real.rpow_mul (div_nonneg hl.le hk0.le)]
  have he : a * ((a - p) / a) = a - p := by field_simp
  rw [he, Real.div_rpow hl.le hk0.le, Real.rpow_sub hl]
  rw [show p - a = -(a - p) by ring, Real.rpow_neg hk0.le]
  field_simp

/-- The genuine general-p hidden-moment law is a scaled power of a
Beta(1,n) measure, rather than the Frechet density in arXiv:2004.05894v1, Proposition 1. -/
theorem paretoHiddenMoment_map_beta_rpow {n : ℕ} [NeZero n] {l a p : ℝ}
    (hl : 0 < l) (ha : 0 < a) (hp : p < a) :
    (iidSampleLaw n (paretoMeasure l a)).map
      (sampleHiddenMoment (paretoMeasure l a) p) =
      (betaMeasure 1 n).map
        (fun y : ℝ => (a * l ^ p / (a - p)) * y ^ ((a - p) / a)) := by
  let : IsProbabilityMeasure (paretoMeasure l a) :=
    instIsProbabilityMeasureParetoMeasure l a hl ha
  rw [Measure.map_congr (sampleHiddenMoment_pareto_eq_hiddenMass_rpow hl ha hp)]
  have hm : Measurable (fun y : ℝ => (a * l ^ p / (a - p)) * y ^ ((a - p) / a)) :=
    measurable_const.mul (measurable_id.pow_const _)
  change Measure.map ((fun y : ℝ => (a * l ^ p / (a - p)) * y ^ ((a - p) / a)) ∘
      sampleHiddenMass (paretoMeasure l a)) _ = _
  rw [← Measure.map_map hm
    (measurable_sampleHiddenMass _), paretoHiddenMass_map_beta hl ha]

/-- The actual general-p hidden-moment expectation as an exact Beta ratio,
correcting the finite-sample reading of arXiv:2004.05894v1, Proposition 1. -/
theorem paretoHiddenMoment_mean_beta {n : ℕ} [NeZero n] {l a p : ℝ}
    (hl : 0 < l) (ha : 0 < a) (hp : p < a) :
    (∫ x : Fin n → ℝ, sampleHiddenMoment
      (paretoMeasure l a) p x
      ∂iidSampleLaw n (paretoMeasure l a)) =
      (a * l ^ p / (a - p)) * (ProbabilityTheory.beta (1 + (a - p) / a) n /
        ProbabilityTheory.beta 1 n) := by
  rw [integral_congr_ae (sampleHiddenMoment_pareto_eq_hiddenMass_rpow hl ha hp), integral_const_mul]
  rw [paretoHiddenMass_integral_rpow hl ha (by positivity : 0 < 1 + (a - p) / a)]

/-- The exact finite-sample Gamma-ratio expectation. The printed
`l^p*n^(p/alpha-1)*Gamma(1-p/alpha)` following Proposition 1 in
arXiv:2004.05894v1 is a Frechet expression; it is not this finite-sample value. -/
theorem paretoHiddenMoment_mean_gamma {n : ℕ} [NeZero n] {l a p : ℝ}
    (hl : 0 < l) (ha : 0 < a) (hp : p < a) :
    (∫ x : Fin n → ℝ, sampleHiddenMoment
      (paretoMeasure l a) p x
      ∂iidSampleLaw n (paretoMeasure l a)) =
      l ^ p * Real.Gamma ((a - p) / a) * Real.Gamma ((n : ℝ) + 1) /
        Real.Gamma ((n : ℝ) + 1 + (a - p) / a) := by
  let r := (a - p) / a
  have hr : 0 < r := div_pos (sub_pos.mpr hp) ha
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (NeZero.pos n)
  rw [paretoHiddenMoment_mean_beta hl ha hp, beta_one_nat n (NeZero.pos n)]
  change (a * l ^ p / (a - p)) * (ProbabilityTheory.beta (1 + r) n / (1 / (n : ℝ))) = _
  unfold ProbabilityTheory.beta
  rw [show 1 + r = r + 1 by ring, Real.Gamma_add_one hr.ne', Real.Gamma_add_one hn.ne']
  rw [show r + 1 + (n : ℝ) = (n : ℝ) + 1 + r by ring]
  dsimp [r]
  field_simp

end TailOptionPricing
