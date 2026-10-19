module

/-
  Actual supported exponential tails and normalized conditional means
  for arXiv:1907.11162v3, Definition 4. The first moment, L1 conditions,
  conditional normalization and characteristic-scale limits are proved.
  The raw kernel agrees with the law only on its nonnegative support.
-/
public import Stats.BinaryForecasts.Exponential
public import Stats.Probability.Exponential
public import Stats.Probability.ExponentialIntegration
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory Filter Topology

namespace TailOptionPricing

/-- The raw tail integral equals the actual exponential-law survival
only on the nonnegative support domain (arXiv:1907.11162v3, Definition 4). -/
theorem exp_survival_eq_measure {lam K : ℝ} (hlam : 0 < lam) (hK : 0 ≤ K) :
    (∫ x in Ioi K, expDensity lam x) = (expMeasure lam).real (Ioi K) := by
  rw [exp_survival_eq hlam, expMeasure_real_Ioi hlam, ite_eq_left hK]

example : (∫ x in Ioi (1 : ℝ), expDensity 1 x) = (expMeasure 1).real (Ioi 1) :=
  exp_survival_eq_measure (by norm_num) (by norm_num)

-- The omitted support case cannot be given a probability interpretation.
example : (expMeasure 1).real (Ioi (-1)) < ∫ x in Ioi (-1 : ℝ), expDensity 1 x := by
  rw [exp_survival_eq (by norm_num), expMeasure_real_Ioi (by norm_num)]
  norm_num

/-- The density tail-moment formula equals the actual supported
exponential-law tail expectation (arXiv:1907.11162v3, Definition 4). -/
theorem expMeasure_tail_mean {r K : ℝ} (hr : 0 < r) (hK : 0 ≤ K) :
    (∫ x in Ioi K, x ∂expMeasure r) = (K + 1 / r) * Real.exp (-(r * K)) := by
  rw [expMeasure_setIntegral hr]
  have he : (∫ x in Ioi K, x * exponentialPDFReal r x) =
      ∫ x in Ioi K, x * expDensity r x := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    dsimp only
    rw [exponentialPDFReal_of_nonneg (hK.trans hx.le)]
    rfl
  rw [he, exp_tail_expectation_eq hr hK]

/-- The actual first tail moment is L1 on the nonnegative threshold
domain, supplying the expectation hypothesis in arXiv:1907.11162v3, Definition 4. -/
theorem expMeasure_tail_integrable_id {r K : ℝ} (hr : 0 < r) (hK : 0 ≤ K) :
    IntegrableOn (fun x : ℝ => x) (Ioi K) (expMeasure r) := by
  rw [expMeasure_integrableOn_iff hr _ _ measurableSet_Ioi]
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := 1) (p := 1) (b := r)
    (by norm_num) (by norm_num) hr
  simp only [Real.rpow_one] at h
  have ht : IntegrableOn (fun x : ℝ => r * (x * Real.exp (-r * x))) (Ioi K) :=
    (h.mono_set (Ioi_subset_Ioi hK)).const_mul r
  apply ht.congr_fun
  · intro x hx
    dsimp only
    rw [exponentialPDFReal_of_nonneg (hK.trans hx.le)]
    ring_nf
  · exact measurableSet_Ioi

/-- The actual exponential law has positive upper-tail probability at
every finite real threshold, including thresholds below its support. -/
theorem expMeasure_real_Ioi_pos {r : ℝ} (hr : 0 < r) (K : ℝ) :
    0 < (expMeasure r).real (Ioi K) := by
  rw [expMeasure_real_Ioi hr]
  split_ifs
  · exact Real.exp_pos _
  · norm_num

/-- Conditioning the actual exponential law above any finite threshold
gives a probability measure, as needed in arXiv:1907.11162v3, Definition 4. -/
theorem expMeasure_cond_probability {r : ℝ} (hr : 0 < r) (K : ℝ) :
    IsProbabilityMeasure ((expMeasure r)[|Ioi K]) := by
  have h := ENNReal.toReal_pos_iff.mp (expMeasure_real_Ioi_pos hr K)
  exact cond_isProbabilityMeasure_of_finite h.1.ne' h.2.ne

/-- The conditional observation is genuinely L1 under the normalized
tail law (arXiv:1907.11162v3, Definition 4); no mean value is assumed. -/
theorem expMeasure_cond_integrable_id {r K : ℝ} (hr : 0 < r) (hK : 0 ≤ K) :
    Integrable (fun x : ℝ => x) ((expMeasure r)[|Ioi K]) := by
  rw [ProbabilityTheory.cond]
  apply (expMeasure_tail_integrable_id hr hK).smul_measure
  exact ENNReal.inv_ne_top.mpr (ENNReal.toReal_pos_iff.mp (expMeasure_real_Ioi_pos hr K)).1.ne'

/-- Actual conditional mean above a nonnegative threshold, computed
under the normalized restriction (arXiv:1907.11162v3, Definition 4). -/
theorem expMeasure_cond_mean {r K : ℝ} (hr : 0 < r) (hK : 0 ≤ K) :
    (∫ x : ℝ, x ∂(expMeasure r)[|Ioi K]) = K + 1 / r := by
  rw [ProbabilityTheory.cond, integral_smul_measure, ENNReal.toReal_inv, smul_eq_mul]
  change ((expMeasure r).real (Ioi K))⁻¹ * (∫ x in Ioi K, x ∂expMeasure r) = _
  rw [expMeasure_tail_mean hr hK, expMeasure_real_Ioi hr, ite_eq_left hK]
  have he := (Real.exp_pos (-(r * K))).ne'
  field_simp

/-- Actual mean excess under the normalized tail law equals the
reciprocal rate (arXiv:1907.11162v3, Definition 4, borderline exponential case). -/
theorem expMeasure_cond_mean_excess {r K : ℝ} (hr : 0 < r) (hK : 0 ≤ K) :
    (∫ x : ℝ, x - K ∂(expMeasure r)[|Ioi K]) = 1 / r := by
  let : IsProbabilityMeasure ((expMeasure r)[|Ioi K]) := expMeasure_cond_probability hr K
  rw [integral_sub (expMeasure_cond_integrable_id hr hK) (integrable_const K),
    expMeasure_cond_mean hr hK, integral_const, probReal_univ, smul_eq_mul, one_mul]
  ring

/-- The source's positive limiting conditional excess is obtained from
actual conditional laws, with limit `1/r` (arXiv:1907.11162v3, Definition 4). -/
theorem expMeasure_cond_mean_excess_tendsto {r : ℝ} (hr : 0 < r) :
    Tendsto (fun K : ℝ => ∫ x : ℝ, x - K ∂(expMeasure r)[|Ioi K]) atTop (𝓝 (1 / r)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with K hK
  exact (expMeasure_cond_mean_excess hr hK).symm

/-- The actual conditional mean divided by the threshold tends to one,
verifying the exponential case of arXiv:1907.11162v3, Definition 4.
This is an actual-law limit, not a general classification of all thin-tailed laws. -/
theorem expMeasure_cond_characteristicScale_tendsto {r : ℝ} (hr : 0 < r) :
    Tendsto (fun K : ℝ => (∫ x : ℝ, x ∂(expMeasure r)[|Ioi K]) / K) atTop (𝓝 1) := by
  have hlim : Tendsto (fun K : ℝ => 1 + (1 / r) * K⁻¹) atTop (𝓝 1) := by
    simpa only [mul_zero, add_zero] using
      tendsto_const_nhds.add (tendsto_inv_atTop_zero.const_mul (1 / r))
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with K hK
  rw [expMeasure_cond_mean hr hK.le]
  field_simp

-- A genuine rate-two law conditioned above three, with finite mean 7/2.
example : (∫ x in Ioi (3 : ℝ), x ∂expMeasure 2) = (7 / 2) * Real.exp (-6) := by
  have h := expMeasure_tail_mean (r := 2) (K := 3) (by norm_num) (by norm_num)
  norm_num at h
  exact h

example : IntegrableOn (fun x : ℝ => x) (Ioi 3) (expMeasure 2) :=
  expMeasure_tail_integrable_id (by norm_num) (by norm_num)

example : 0 < (expMeasure 2).real (Ioi (-1)) :=
  expMeasure_real_Ioi_pos (by norm_num) _

example : IsProbabilityMeasure ((expMeasure 2)[|Ioi (3 : ℝ)]) :=
  expMeasure_cond_probability (by norm_num) _

example : ∀ᵐ x ∂(expMeasure 2)[|Ioi (3 : ℝ)], 3 < x := ae_cond_mem measurableSet_Ioi

example : Integrable (fun x : ℝ => x) ((expMeasure 2)[|Ioi 3]) :=
  expMeasure_cond_integrable_id (by norm_num) (by norm_num)

example : (∫ x : ℝ, x ∂(expMeasure 2)[|Ioi 3]) = 7 / 2 := by
  rw [expMeasure_cond_mean (by norm_num) (by norm_num)]
  norm_num

example : (∫ x : ℝ, x - 3 ∂(expMeasure 2)[|Ioi 3]) = 1 / 2 :=
  expMeasure_cond_mean_excess (by norm_num) (by norm_num)

example : Tendsto (fun K : ℝ => ∫ x : ℝ, x - K ∂(expMeasure 2)[|Ioi K])
    atTop (𝓝 (1 / 2 : ℝ)) := expMeasure_cond_mean_excess_tendsto (by norm_num)

example : Tendsto (fun K : ℝ => (∫ x : ℝ, x ∂(expMeasure 2)[|Ioi K]) / K)
    atTop (𝓝 1) := expMeasure_cond_characteristicScale_tendsto (by norm_num)

#print axioms expMeasure_tail_mean
#print axioms expMeasure_cond_probability
#print axioms expMeasure_cond_integrable_id
#print axioms expMeasure_cond_mean_excess
#print axioms expMeasure_cond_characteristicScale_tendsto

end TailOptionPricing
