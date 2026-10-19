module

/-
  Actual standard Frechet probability law used by the corrected
  maximum limit in arXiv:2004.05894v1, Proposition 1. It is built
  independently as the negative-power pushforward of an Exp(1)
  population. For a positive index a its CDF is exp(-t^(-a))
  at positive t and zero otherwise. It is not identified with any
  finite Pareto maximum by definition.
-/
public import Stats.Probability.Exponential
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory Filter Topology

namespace TailOptionPricing

/-- An actual Exp(1) draw is strictly positive almost surely.
The boundary zero has probability zero by its actual CDF. -/
theorem unitExponential_ae_pos : ∀ᵐ u ∂expMeasure 1, 0 < u := by
  let := isProbabilityMeasure_expMeasure (show (0 : ℝ) < 1 by norm_num)
  have hz : (expMeasure 1).real (Iic (0 : ℝ)) = 0 := by
    rw [← cdf_eq_real, cdf_expMeasure_eq (by norm_num)]
    norm_num
  apply ae_iff.mpr
  rw [← measureReal_eq_zero_iff]
  have he : {u : ℝ | ¬0 < u} = Iic (0 : ℝ) := by
    ext u
    exact not_lt
  rw [he]
  exact hz

/-- A normalized law constructed from an actual exponential draw.
For positive a this is the standard Frechet law with index a;
the constructor does not supply its proposed CDF as a property. -/
noncomputable def frechetMeasure (a : ℝ) : Measure ℝ :=
  (expMeasure 1).map (fun u : ℝ => u ^ (-1 / a))

instance frechetMeasure_probability (a : ℝ) : IsProbabilityMeasure (frechetMeasure a) := by
  let := isProbabilityMeasure_expMeasure (show (0 : ℝ) < 1 by norm_num)
  unfold frechetMeasure
  exact (Measure.isProbabilityMeasure_map_iff (by fun_prop)).mpr inferInstance

/-- The actual Frechet construction is supported on strictly positive
values. This support fact is independent of the displayed CDF. -/
theorem frechetMeasure_ae_pos (a : ℝ) : ∀ᵐ x ∂frechetMeasure a, 0 < x := by
  unfold frechetMeasure
  apply (ae_map_iff (by fun_prop) measurableSet_Ioi).mpr
  exact unitExponential_ae_pos.mono (fun u hu => Real.rpow_pos_of_pos hu _)

/-- The decreasing inverse-power transform gives the full Jacobian-free
CDF event relation on positive exponential observations. Used before
computing the Frechet law in Proposition 1's asymptotic interpretation. -/
theorem frechet_inverse_power_le_iff {a u t : ℝ} (ha : 0 < a) (hu : 0 < u) (ht : 0 < t) :
    u ^ (-1 / a) ≤ t ↔ t ^ (-a) ≤ u := by
  have he : (u ^ (-1 / a)) ^ (-a) = u := by
    rw [← Real.rpow_mul hu.le]
    have hp : (-1 / a) * (-a) = 1 := by field_simp
    rw [hp, Real.rpow_one]
  have h := Real.rpow_le_rpow_iff_of_neg ht (Real.rpow_pos_of_pos hu (-1 / a))
    (neg_neg_of_pos ha)
  rw [he] at h
  exact h.symm

/-- CDF of the actual normalized Frechet probability law, with its
entire support. This justifies the limiting CDF used for the normalized
Pareto maximum, rather than substituting an asymptotic density into a
finite-sample identity (arXiv:2004.05894v1, Proposition 1). -/
theorem frechetMeasure_cdf {a : ℝ} (ha : 0 < a) (t : ℝ) :
    cdf (frechetMeasure a) t = if 0 < t then Real.exp (-(t ^ (-a))) else 0 := by
  let := isProbabilityMeasure_expMeasure (show (0 : ℝ) < 1 by norm_num)
  let : NullSingletonClass (expMeasure 1) := by
    unfold expMeasure gammaMeasure
    infer_instance
  have hm : Measurable (fun u : ℝ => u ^ (-1 / a)) := by fun_prop
  rw [cdf_eq_real, frechetMeasure, measureReal_def, Measure.map_apply hm measurableSet_Iic]
  change (expMeasure 1).real {u : ℝ | u ^ (-1 / a) ≤ t} = _
  split_ifs with ht
  · have he : {u : ℝ | u ^ (-1 / a) ≤ t} =ᵐ[expMeasure 1] Ici (t ^ (-a)) := by
      filter_upwards [unitExponential_ae_pos] with u hu
      exact propext (frechet_inverse_power_le_iff ha hu ht)
    rw [measureReal_congr he,
      ← measureReal_congr (Ioi_ae_eq_Ici (μ := expMeasure 1)),
      expMeasure_real_Ioi (by norm_num),
      ite_eq_left (Real.rpow_nonneg ht.le _), one_mul]
  · have he : {u : ℝ | u ^ (-1 / a) ≤ t} =ᵐ[expMeasure 1] (∅ : Set ℝ) := by
      filter_upwards [unitExponential_ae_pos] with u hu
      apply propext
      change (u ^ (-1 / a) ≤ t) ↔ False
      exact iff_false_intro
        (not_le_of_gt ((le_of_not_gt ht).trans_lt (Real.rpow_pos_of_pos hu _)))
    rw [measureReal_congr he, measureReal_empty]

/-- A probability-measure value for the independently constructed
Frechet population, so weak limits use the actual measure topology. -/
noncomputable def frechetProba (a : ℝ) : ProbabilityMeasure ℝ :=
  ⟨frechetMeasure a, inferInstance⟩

/-- The actual Frechet upper tail at every real threshold, including
the region below support (Proposition 1's limiting population). -/
theorem frechetMeasure_real_Ioi {a : ℝ} (ha : 0 < a) (t : ℝ) :
    (frechetMeasure a).real (Ioi t) =
      if 0 < t then 1 - Real.exp (-(t ^ (-a))) else 1 := by
  rw [← compl_Iic, measureReal_compl measurableSet_Iic, probReal_univ,
    ← cdf_eq_real, frechetMeasure_cdf ha]
  split_ifs <;> ring

/-- Every positive threshold has positive actual Frechet CDF. -/
theorem frechetMeasure_cdf_pos {a t : ℝ} (ha : 0 < a) (ht : 0 < t) :
    0 < cdf (frechetMeasure a) t := by
  rw [frechetMeasure_cdf ha, ite_eq_left ht]
  exact Real.exp_pos _

/-- The actual Frechet CDF remains strictly below one at each finite
positive threshold, as required of its unbounded positive population. -/
theorem frechetMeasure_cdf_lt_one {a t : ℝ} (ha : 0 < a) (ht : 0 < t) :
    cdf (frechetMeasure a) t < 1 := by
  rw [frechetMeasure_cdf ha, ite_eq_left ht, Real.exp_lt_one_iff]
  exact neg_neg_of_pos (Real.rpow_pos_of_pos ht _)

/-- Actual Frechet survival is positive at every finite real threshold. -/
theorem frechetMeasure_survival_pos {a : ℝ} (ha : 0 < a) (t : ℝ) :
    0 < (frechetMeasure a).real (Ioi t) := by
  rw [frechetMeasure_real_Ioi ha]
  split_ifs with ht
  · exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos (Real.rpow_pos_of_pos ht _)))
  · exact zero_lt_one

example : (4 : ℝ) ^ (-1 / 2 : ℝ) ≤ 2 ↔ (2 : ℝ) ^ (-2 : ℝ) ≤ 4 :=
  frechet_inverse_power_le_iff (by norm_num) (by norm_num) (by norm_num)

example : cdf (frechetMeasure 2) 1 = Real.exp (-1) := by
  rw [frechetMeasure_cdf (by norm_num)]
  norm_num

example : (frechetMeasure 2).real (Ioi 1) = 1 - Real.exp (-1) := by
  rw [frechetMeasure_real_Ioi (by norm_num)]
  norm_num

example : 0 < cdf (frechetMeasure 2) 1 := frechetMeasure_cdf_pos (by norm_num) (by norm_num)

example : cdf (frechetMeasure 2) 1 < 1 := frechetMeasure_cdf_lt_one (by norm_num) (by norm_num)

example : 0 < (frechetMeasure 2).real (Ioi 1) := frechetMeasure_survival_pos (by norm_num) _

#print axioms unitExponential_ae_pos
#print axioms frechetMeasure_ae_pos
#print axioms frechet_inverse_power_le_iff
#print axioms frechetMeasure_cdf
#print axioms frechetMeasure_real_Ioi
#print axioms frechetMeasure_cdf_pos
#print axioms frechetMeasure_cdf_lt_one
#print axioms frechetMeasure_survival_pos

end TailOptionPricing
