module

/-
  Actual scaled-power Beta(1,n) density for arXiv:2004.05894v1,
  Proposition 1. Its support is (0,C); the exact finite-sample
  factor is (1-(z/C)^(1/r))^(n-1), rather than the exponential
  factor obtained by substituting a Frechet maximum. Normalization
  follows from the independently normalized Beta law and the proved
  positive-axis Jacobian change of variables.
-/
public import Stats.Probability.PowerPushforward
public import Stats.HiddenMoments.BetaKernel
public import Stats.Probability.DensityIntegration

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory Filter

namespace TailOptionPricing

/-- Explicit density of C times the r-th power of a Beta(1,n)
observation. The full finite support is part of the formula. -/
noncomputable def powerBetaPDF (n : ℕ) (C r z : ℝ) : ℝ :=
  (Ioo 0 C).indicator (fun z =>
    ((n : ℝ) * (1 / r / C)) * (z / C) ^ (1 / r - 1) *
      (1 - (z / C) ^ (1 / r)) ^ (n - 1)) z

theorem measurable_powerBetaPDF (n : ℕ) (C r : ℝ) : Measurable (powerBetaPDF n C r) := by
  unfold powerBetaPDF
  apply Measurable.indicator _ measurableSet_Ioo
  fun_prop

/-- The inverse-Jacobian density equals the explicit supported
finite Beta-power formula (Proposition 1 correction). -/
theorem positivePowerDensity_beta_eq {n : ℕ} (hn : 0 < n) {C r : ℝ}
    (hC : 0 < C) (hr : 0 < r) (z : ℝ) :
    positivePowerDensity C r (betaPDFReal 1 n) z = powerBetaPDF n C r z := by
  unfold positivePowerDensity powerBetaPDF
  by_cases hz : 0 < z
  · rw [indicator_of_mem (s := Ioi (0 : ℝ)) hz, betaPDFReal_one_nat_eq n hn]
    by_cases hzC : z < C
    · have hy : positivePowerInverse C r z ∈ Ioo (0 : ℝ) 1 :=
        ⟨positivePowerInverse_pos hC hz, (positivePowerInverse_lt_one_iff hC hr hz).mpr hzC⟩
      rw [indicator_of_mem (s := Ioo (0 : ℝ) 1) hy,
        indicator_of_mem (s := Ioo 0 C) ⟨hz, hzC⟩]
      unfold paretoSampleSurvivalRatioPDF positivePowerJacobian positivePowerInverse
      ring
    · have hy : positivePowerInverse C r z ∉ Ioo (0 : ℝ) 1 :=
        fun h => hzC ((positivePowerInverse_lt_one_iff hC hr hz).mp h.2)
      rw [indicator_of_notMem (s := Ioo (0 : ℝ) 1) hy, mul_zero,
        indicator_of_notMem (s := Ioo 0 C) (fun h => hzC h.2)]
  · rw [indicator_of_notMem (s := Ioi (0 : ℝ)) hz,
      indicator_of_notMem (s := Ioo 0 C) (fun h => hz h.1)]

/-- The whole scaled-power Beta law has the displayed actual density,
including support and Jacobian (Proposition 1 correction). -/
theorem betaMeasure_map_positivePower {n : ℕ} (hn : 0 < n) {C r : ℝ}
    (hC : 0 < C) (hr : 0 < r) :
    (betaMeasure 1 n).map (positivePower C r) =
      volume.withDensity (fun z => ENNReal.ofReal (powerBetaPDF n C r z)) := by
  change (volume.withDensity (fun y => ENNReal.ofReal (betaPDFReal 1 n y))).map
    (positivePower C r) = _
  have hz (y : ℝ) (hy : y ≤ 0) : betaPDFReal 1 n y = 0 := by
    rw [betaPDFReal_one_nat_eq n hn]
    exact indicator_of_notMem (s := Ioo (0 : ℝ) 1)
      (fun h => (not_lt_of_ge hy) h.1) _
  rw [map_positivePower_realDensity hC hr _ hz]
  apply withDensity_congr_ae
  exact Eventually.of_forall (fun z => congrArg ENNReal.ofReal
    (positivePowerDensity_beta_eq hn hC hr z))

/-- The actual supported Beta-power density is nonnegative throughout
the real line, including both exterior support branches. -/
theorem powerBetaPDF_nonneg {n : ℕ} (hn : 0 < n) {C r : ℝ}
    (hC : 0 < C) (hr : 0 < r) (z : ℝ) : 0 ≤ powerBetaPDF n C r z := by
  rw [← positivePowerDensity_beta_eq hn hC hr]
  exact positivePowerDensity_nonneg hC hr
    (betaPDFReal_nonneg (by norm_num) (Nat.cast_pos.mpr hn)) z

/-- The density's unit mass is inherited from the actual Beta
probability measure by measurable generation, not assumed in the PDF. -/
theorem powerBetaPDF_probability {n : ℕ} (hn : 0 < n) {C r : ℝ}
    (hC : 0 < C) (hr : 0 < r) :
    IsProbabilityMeasure (volume.withDensity (fun z => ENNReal.ofReal (powerBetaPDF n C r z))) := by
  let := isProbabilityMeasureBeta (show (0 : ℝ) < 1 by norm_num) (Nat.cast_pos.mpr hn)
  have h : IsProbabilityMeasure ((betaMeasure 1 n).map (positivePower C r)) :=
    (Measure.isProbabilityMeasure_map_iff (measurable_positivePower C r).aemeasurable).mpr
      inferInstance
  rwa [betaMeasure_map_positivePower hn hC hr] at h

/-- The actual density is strictly positive throughout the interior
of its finite support (Proposition 1 correction). -/
theorem powerBetaPDF_pos {n : ℕ} (hn : 0 < n) {C r z : ℝ}
    (hC : 0 < C) (hr : 0 < r) (hz : z ∈ Ioo 0 C) : 0 < powerBetaPDF n C r z := by
  unfold powerBetaPDF
  rw [indicator_of_mem (s := Ioo 0 C) hz]
  have hu : 0 < 1 - (z / C) ^ (1 / r) :=
    sub_pos.mpr ((positivePowerInverse_lt_one_iff hC hr hz.1).mpr hz.2)
  exact mul_pos (mul_pos (mul_pos (Nat.cast_pos.mpr hn) (div_pos (one_div_pos.mpr hr) hC))
    (Real.rpow_pos_of_pos (div_pos hz.1 hC) _)) (pow_pos hu _)

/-- Actual L1 and unit integral of the explicit Beta-power density.
Normalization was proved from the independent Beta population first;
L1 is then obtained by integrating the constant one under that law. -/
theorem powerBetaPDF_integrable_integral {n : ℕ} (hn : 0 < n) {C r : ℝ}
    (hC : 0 < C) (hr : 0 < r) :
    Integrable (powerBetaPDF n C r) ∧ (∫ z : ℝ, powerBetaPDF n C r z) = 1 := by
  let := powerBetaPDF_probability hn hC hr
  have hm := measurable_powerBetaPDF n C r
  have hnonneg := powerBetaPDF_nonneg hn hC hr
  have hi := (realDensity_integrableOn_iff _ hm hnonneg (fun _ => (1 : ℝ))
    MeasurableSet.univ).mp (integrable_const 1).integrableOn
  have he := realDensity_setIntegral _ hm hnonneg (fun _ => (1 : ℝ)) univ
  simp only [IntegrableOn, Measure.restrict_univ, one_mul] at hi he
  refine ⟨hi, ?_⟩
  rw [← he]
  simp

example (z : ℝ) : positivePowerDensity 2 3 (betaPDFReal 1 2) z = powerBetaPDF 2 2 3 z :=
  positivePowerDensity_beta_eq (by norm_num) (by norm_num) (by norm_num) _

example : (betaMeasure 1 2).map (positivePower 2 3) =
    volume.withDensity (fun z => ENNReal.ofReal (powerBetaPDF 2 2 3 z)) :=
  betaMeasure_map_positivePower (by norm_num) (by norm_num) (by norm_num)

example (z : ℝ) : 0 ≤ powerBetaPDF 2 2 3 z :=
  powerBetaPDF_nonneg (by norm_num) (by norm_num) (by norm_num) _

example : IsProbabilityMeasure
    (volume.withDensity (fun z => ENNReal.ofReal (powerBetaPDF 2 2 3 z))) :=
  powerBetaPDF_probability (by norm_num) (by norm_num) (by norm_num)

#print axioms positivePowerDensity_beta_eq
#print axioms betaMeasure_map_positivePower
#print axioms powerBetaPDF_nonneg
#print axioms powerBetaPDF_probability

example : 0 < powerBetaPDF 2 2 3 1 :=
  powerBetaPDF_pos (by norm_num) (by norm_num) (by norm_num) (by norm_num)

example : Integrable (powerBetaPDF 2 2 3) ∧ (∫ z : ℝ, powerBetaPDF 2 2 3 z) = 1 :=
  powerBetaPDF_integrable_integral (by norm_num) (by norm_num) (by norm_num)

example : powerBetaPDF 2 2 (1 / 2) 1 = 3 / 4 := by
  norm_num [powerBetaPDF, Real.rpow_ofNat]

#print axioms powerBetaPDF_pos
#print axioms powerBetaPDF_integrable_integral

end TailOptionPricing
