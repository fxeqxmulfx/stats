module

/-
  Correct Frechet asymptotic of the actual iid strong-Pareto maximum,
  arXiv:2004.05894v1, Proposition 1. With n+1 observations, divide
  the actual sample maximum by l*(n+1)^(1/a). Its genuine probability
  law converges weakly to the independently constructed Frechet law.
  The finite-sample Frechet substitution is separately refuted.
-/
public import Stats.HiddenMoments.Maximum
public import Stats.Probability.Frechet
public import Stats.Probability.WeakCDF
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory Filter Topology

namespace TailOptionPricing

/-- Actual normalized maximum law, with n+1 nonempty iid observations.
No Frechet formula is used in its construction (Proposition 1). -/
noncomputable def paretoNormalizedMaximumProba (n : ℕ) (l a : ℝ) (hl : 0 < l) (ha : 0 < a) :
    ProbabilityMeasure ℝ := by
  let : IsProbabilityMeasure (paretoMeasure l a) := instIsProbabilityMeasureParetoMeasure l a hl ha
  exact ⟨(iidSampleLaw (n + 1) (paretoMeasure l a)).map
    (fun x => sampleMaximum x / (l * ((n + 1 : ℕ) : ℝ) ^ (1 / a))),
      (Measure.isProbabilityMeasure_map_iff (measurable_sampleMaximum.div_const _).aemeasurable).mpr
        inferInstance⟩

/-- CDF of the actual normalized maximum, including its finite support
boundary. This comes from the genuine maximum law (Proposition 1). -/
theorem paretoNormalizedMaximumProba_cdf (n : ℕ) {l a : ℝ} (hl : 0 < l) (ha : 0 < a) (t : ℝ) :
    cdf (paretoNormalizedMaximumProba n l a hl ha : Measure ℝ) t =
      if t * (l * ((n + 1 : ℕ) : ℝ) ^ (1 / a)) < l then 0 else
        paretoSampleMaxCDF (n + 1) l a (t * (l * ((n + 1 : ℕ) : ℝ) ^ (1 / a))) := by
  let : IsProbabilityMeasure (paretoMeasure l a) := instIsProbabilityMeasureParetoMeasure l a hl ha
  have hN : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (Nat.succ_pos n)
  have hs : 0 < l * ((n + 1 : ℕ) : ℝ) ^ (1 / a) :=
    mul_pos hl (Real.rpow_pos_of_pos hN _)
  rw [cdf_eq_real]
  change ((iidSampleLaw (n + 1) (paretoMeasure l a)).map
    (fun x => sampleMaximum x / (l * ((n + 1 : ℕ) : ℝ) ^ (1 / a)))).real (Iic t) = _
  rw [measureReal_def, Measure.map_apply (measurable_sampleMaximum.div_const _) measurableSet_Iic]
  have he : (fun x : Fin (n + 1) → ℝ =>
      sampleMaximum x / (l * ((n + 1 : ℕ) : ℝ) ^ (1 / a))) ⁻¹' Iic t =
      {x | sampleMaximum x ≤ t * (l * ((n + 1 : ℕ) : ℝ) ^ (1 / a))} := by
    ext x
    exact div_le_iff₀ hs
  rw [he]
  exact paretoSampleMaximum_cdf hl ha _

/-- Exact cancellation of the sample-size normalization in the
Pareto survival power. All bases here are independently positive. -/
theorem pareto_normalized_survival_power {l a N t : ℝ}
    (hl : 0 < l) (ha : 0 < a) (hN : 0 < N) (ht : 0 < t) :
    (l / (t * (l * N ^ (1 / a)))) ^ a = t ^ (-a) / N := by
  have hpow : (N ^ (1 / a)) ^ a = N := by
    rw [← Real.rpow_mul hN.le, div_mul_cancel₀ 1 ha.ne', Real.rpow_one]
  have hs : N ^ (1 / a) ≠ 0 := (Real.rpow_pos_of_pos hN _).ne'
  have he : l / (t * (l * N ^ (1 / a))) = (t * N ^ (1 / a))⁻¹ := by
    field_simp
  rw [he, Real.inv_rpow (mul_pos ht (Real.rpow_pos_of_pos hN _)).le,
    Real.mul_rpow ht.le (Real.rpow_nonneg hN.le _), hpow, Real.rpow_neg ht.le]
  ring

/-- Nonpositive thresholds have zero probability under every actual
normalized maximum, not just in the limiting CDF (Proposition 1). -/
theorem paretoNormalizedMaximumProba_cdf_nonpos (n : ℕ) {l a t : ℝ}
    (hl : 0 < l) (ha : 0 < a) (ht : t ≤ 0) :
    cdf (paretoNormalizedMaximumProba n l a hl ha : Measure ℝ) t = 0 := by
  rw [paretoNormalizedMaximumProba_cdf n hl ha]
  have hs : 0 ≤ l * ((n + 1 : ℕ) : ℝ) ^ (1 / a) := by positivity
  exact ite_eq_left ((mul_nonpos_of_nonpos_of_nonneg ht hs).trans_lt hl)

/-- The positive-threshold CDF limit of the actual normalized
maximum. The binomial finite CDF tends to the Frechet exponential
by the classical exponential limit (Proposition 1 correction). -/
theorem paretoNormalizedMaximumProba_cdf_tendsto_pos {l a t : ℝ}
    (hl : 0 < l) (ha : 0 < a) (ht : 0 < t) :
    Tendsto (fun n : ℕ => cdf (paretoNormalizedMaximumProba n l a hl ha : Measure ℝ) t)
      atTop (𝓝 (Real.exp (-(t ^ (-a))))) := by
  have hlim := (Real.tendsto_one_add_div_pow_exp (-(t ^ (-a)))).comp (tendsto_add_atTop_nat 1)
  have hN : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hscale : Tendsto (fun n : ℕ => t * (l * ((n + 1 : ℕ) : ℝ) ^ (1 / a)))
      atTop atTop :=
    ((tendsto_rpow_atTop (one_div_pos.mpr ha)).comp hN).const_mul_atTop hl |>.const_mul_atTop ht
  apply hlim.congr'
  filter_upwards [hscale.eventually (eventually_ge_atTop l)] with n hn
  simp only [Function.comp_def]
  rw [paretoNormalizedMaximumProba_cdf n hl ha, ite_eq_right (not_lt.mpr hn)]
  unfold paretoSampleMaxCDF
  rw [pareto_normalized_survival_power hl ha (Nat.cast_pos.mpr (Nat.succ_pos n)) ht]
  congr 1
  ring

/-- CDF convergence at every real threshold to the independently
constructed actual Frechet probability law (Proposition 1 correction). -/
theorem paretoNormalizedMaximumProba_cdf_tendsto {l a : ℝ} (hl : 0 < l) (ha : 0 < a) (t : ℝ) :
    Tendsto (fun n : ℕ => cdf (paretoNormalizedMaximumProba n l a hl ha : Measure ℝ) t)
      atTop (𝓝 (cdf (frechetMeasure a) t)) := by
  rw [frechetMeasure_cdf ha]
  split_ifs with ht
  · exact paretoNormalizedMaximumProba_cdf_tendsto_pos hl ha ht
  · simp_rw [paretoNormalizedMaximumProba_cdf_nonpos _ hl ha (le_of_not_gt ht)]
    exact tendsto_const_nhds

/-- Actual weak Frechet limit of normalized iid strong-Pareto maxima.
Every positive scale and index is allowed, including infinite-mean
populations. This is an asymptotic, not a finite density identity. -/
theorem paretoNormalizedMaximumProba_tendsto {l a : ℝ} (hl : 0 < l) (ha : 0 < a) :
    Tendsto (fun n => paretoNormalizedMaximumProba n l a hl ha) atTop (𝓝 (frechetProba a)) :=
  probabilityMeasure_tendsto_of_cdf (paretoNormalizedMaximumProba_cdf_tendsto hl ha)

/-- At every finite threshold above the support, the exact maximum
CDF is strictly below the Frechet substitute. Thus moving the cutoff
farther into the tail cannot make the finite substitution an identity. -/
theorem paretoSampleMaximum_cdf_lt_frechet {n : ℕ} [NeZero n] {l a t : ℝ}
    (hl : 0 < l) (ha : 0 < a) (ht : l ≤ t) :
    (iidSampleLaw n (paretoMeasure l a)).real {x | sampleMaximum x ≤ t} <
      Real.exp (-((n : ℝ) * (l / t) ^ a)) := by
  have ht₀ : 0 < t := hl.trans_le ht
  have hp : 0 < (l / t) ^ a := Real.rpow_pos_of_pos (div_pos hl ht₀) a
  have hb : 0 ≤ 1 - (l / t) ^ a := sub_nonneg.mpr
    (Real.rpow_le_one (div_pos hl ht₀).le ((div_le_one ht₀).mpr ht) ha.le)
  have he : 1 - (l / t) ^ a < Real.exp (-((l / t) ^ a)) := by
    linarith only [Real.add_one_lt_exp (neg_ne_zero.mpr hp.ne')]
  rw [paretoSampleMaximum_cdf hl ha, ite_eq_right (not_lt.mpr ht)]
  unfold paretoSampleMaxCDF
  calc
    _ < (Real.exp (-((l / t) ^ a))) ^ n := pow_lt_pow_left₀ he hb (NeZero.ne n)
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring

/-- The exact finite maximum CDF is zero at l, whereas the source's
Frechet substitute is exp(-n)>0. Hence Proposition 1 cannot use this
substitution as an exact finite-sample equality. -/
theorem paretoSampleMaximum_not_exact_frechet {n : ℕ} [NeZero n] {l a : ℝ}
    (hl : 0 < l) (ha : 0 < a) :
    (iidSampleLaw n (paretoMeasure l a)).real {x | sampleMaximum x ≤ l} ≠
      Real.exp (-((n : ℝ) * (l / l) ^ a)) := by
  rw [paretoSampleMaximum_cdf hl ha, ite_eq_right (lt_irrefl l)]
  simp only [paretoSampleMaxCDF, div_self hl.ne', Real.one_rpow, sub_self,
    zero_pow (NeZero.ne n), mul_one]
  exact (Real.exp_pos _).ne

example (t : ℝ) : cdf (paretoNormalizedMaximumProba 1 1 2 (by norm_num) (by norm_num) :
    Measure ℝ) t = if t * (1 * ((1 + 1 : ℕ) : ℝ) ^ (1 / 2 : ℝ)) < 1 then 0 else
      paretoSampleMaxCDF 2 1 2 (t * (1 * ((1 + 1 : ℕ) : ℝ) ^ (1 / 2 : ℝ))) :=
  paretoNormalizedMaximumProba_cdf _ (by norm_num) (by norm_num) _

example : (1 / (1 * (1 * (2 : ℝ) ^ (1 / 2 : ℝ)))) ^ (2 : ℝ) = 1 ^ (-2 : ℝ) / 2 :=
  pareto_normalized_survival_power (by norm_num) (by norm_num) (by norm_num) (by norm_num)

example : cdf (paretoNormalizedMaximumProba 1 1 2 (by norm_num) (by norm_num) : Measure ℝ)
    (-1) = 0 :=
  paretoNormalizedMaximumProba_cdf_nonpos _ (by norm_num) (by norm_num) (by norm_num)

example : Tendsto (fun n : ℕ => cdf
    (paretoNormalizedMaximumProba n 1 2 (by norm_num) (by norm_num) : Measure ℝ) 1)
      atTop (𝓝 (Real.exp (-((1 : ℝ) ^ (-2 : ℝ))))) :=
  paretoNormalizedMaximumProba_cdf_tendsto_pos (by norm_num) (by norm_num) (by norm_num)

example : Tendsto (fun n : ℕ => cdf
    (paretoNormalizedMaximumProba n 1 2 (by norm_num) (by norm_num) : Measure ℝ) 1)
      atTop (𝓝 (cdf (frechetMeasure 2) 1)) :=
  paretoNormalizedMaximumProba_cdf_tendsto (by norm_num) (by norm_num) _

example : Tendsto (fun n => paretoNormalizedMaximumProba n 1 2 (by norm_num) (by norm_num))
    atTop (𝓝 (frechetProba 2)) :=
  paretoNormalizedMaximumProba_tendsto (by norm_num) (by norm_num)

example : (iidSampleLaw 2 (paretoMeasure 1 2)).real {x | sampleMaximum x ≤ 1} ≠
    Real.exp (-((2 : ℝ) * (1 / 1) ^ (2 : ℝ))) :=
  paretoSampleMaximum_not_exact_frechet (by norm_num) (by norm_num)

example : (iidSampleLaw 2 (paretoMeasure 1 2)).real {x | sampleMaximum x ≤ 2} <
    Real.exp (-((2 : ℝ) * (1 / 2) ^ (2 : ℝ))) :=
  paretoSampleMaximum_cdf_lt_frechet (by norm_num) (by norm_num) (by norm_num)

#print axioms paretoNormalizedMaximumProba_cdf
#print axioms pareto_normalized_survival_power
#print axioms paretoNormalizedMaximumProba_cdf_nonpos
#print axioms paretoNormalizedMaximumProba_cdf_tendsto_pos
#print axioms paretoNormalizedMaximumProba_cdf_tendsto
#print axioms paretoNormalizedMaximumProba_tendsto
#print axioms paretoSampleMaximum_not_exact_frechet
#print axioms paretoSampleMaximum_cdf_lt_frechet

end TailOptionPricing
