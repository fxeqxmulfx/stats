module

/-
  Actual density change of variables for positive scaled powers.
  Used for arXiv:2004.05894v1, Proposition 1. The inverse Jacobian
  is computed independently, and the measure identity follows from
  the one-dimensional monotone change-of-variables theorem. No
  integrability at the zero endpoint or bounded derivative is needed.
-/
public import Stats.Probability.PositivePower
public import Mathlib.MeasureTheory.Function.JacobianOneDim

@[expose] public section

open Real Set MeasureTheory Filter

namespace TailOptionPricing

theorem measurable_positivePower (C r : ℝ) : Measurable (positivePower C r) := by
  unfold positivePower
  fun_prop

theorem measurable_positivePowerInverse (C r : ℝ) : Measurable (positivePowerInverse C r) := by
  unfold positivePowerInverse
  fun_prop

theorem measurable_positivePowerJacobian (C r : ℝ) : Measurable (positivePowerJacobian C r) := by
  unfold positivePowerJacobian
  fun_prop

/-- A nonnegative density supported on positive values transforms by
the proved inverse Jacobian. The actual equality is of whole measures;
the target density is not supplied as an assumption (Proposition 1).
The input need not be normalized, and no endpoint L1 assumption is used. -/
theorem map_positivePower_withDensity {C r : ℝ} (hC : 0 < C) (hr : 0 < r)
    (g : ℝ → ENNReal) (hg : ∀ y : ℝ, y ≤ 0 → g y = 0) :
    (volume.withDensity g).map (positivePower C r) =
      volume.withDensity ((Ioi (0 : ℝ)).indicator (fun z =>
        ENNReal.ofReal (positivePowerJacobian C r z) * g (positivePowerInverse C r z))) := by
  ext s hs
  have hm := measurable_positivePower C r
  rw [Measure.map_apply hm hs, withDensity_apply g (hm hs), withDensity_apply _ hs]
  calc
    _ = ∫⁻ y in positivePower C r ⁻¹' s, (Ioi (0 : ℝ)).indicator g y := by
      apply lintegral_congr_ae
      exact Eventually.of_forall (fun y => by
        by_cases hy : 0 < y
        · rw [indicator_of_mem (s := Ioi (0 : ℝ)) hy]
        · rw [indicator_of_notMem (s := Ioi (0 : ℝ)) hy, hg y (le_of_not_gt hy)])
    _ = ∫⁻ y in Ioi (0 : ℝ) ∩ positivePower C r ⁻¹' s, g y := by
      rw [lintegral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi]
    _ = ∫⁻ z in Ioi (0 : ℝ) ∩ s,
        ENNReal.ofReal (positivePowerJacobian C r z) * g (positivePowerInverse C r z) := by
      rw [← positivePowerInverse_image hC hr s]
      exact lintegral_image_eq_lintegral_deriv_mul_of_monotoneOn
        (measurableSet_Ioi.inter hs)
        (fun z hz => (positivePowerInverse_hasDerivAt hC hz.1).hasDerivWithinAt)
        ((positivePowerInverse_monotoneOn hC hr).mono inter_subset_left) g
    _ = _ := by
      rw [lintegral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi]

/-- The real-valued positive-axis density formula from the actual
inverse Jacobian (Proposition 1's change of variables). -/
noncomputable def positivePowerDensity (C r : ℝ) (g : ℝ → ℝ) (z : ℝ) : ℝ :=
  (Ioi (0 : ℝ)).indicator
    (fun z => positivePowerJacobian C r z * g (positivePowerInverse C r z)) z

theorem measurable_positivePowerDensity (C r : ℝ) {g : ℝ → ℝ} (hg : Measurable g) :
    Measurable (positivePowerDensity C r g) := by
  unfold positivePowerDensity
  exact ((measurable_positivePowerJacobian C r).mul
    (hg.comp (measurable_positivePowerInverse C r))).indicator measurableSet_Ioi

/-- Nonnegative real input densities give nonnegative transformed
densities, with zero density off the positive axis (Proposition 1). -/
theorem positivePowerDensity_nonneg {C r : ℝ} (hC : 0 < C) (hr : 0 < r)
    {g : ℝ → ℝ} (hg : ∀ y, 0 ≤ g y) (z : ℝ) :
    0 ≤ positivePowerDensity C r g z := by
  unfold positivePowerDensity
  by_cases hz : 0 < z
  · rw [indicator_of_mem (s := Ioi (0 : ℝ)) hz]
    exact mul_nonneg (positivePowerJacobian_pos hC hr hz).le (hg _)
  · rw [indicator_of_notMem (s := Ioi (0 : ℝ)) hz]

/-- Whole-law real-density change of variables for the positive
scaled power. The formula holds without any bounded-Jacobian or
endpoint integrability restriction (Proposition 1). -/
theorem map_positivePower_realDensity {C r : ℝ} (hC : 0 < C) (hr : 0 < r)
    (g : ℝ → ℝ) (hg : ∀ y : ℝ, y ≤ 0 → g y = 0) :
    (volume.withDensity (fun y => ENNReal.ofReal (g y))).map (positivePower C r) =
      volume.withDensity (fun z => ENNReal.ofReal (positivePowerDensity C r g z)) := by
  rw [map_positivePower_withDensity hC hr (fun y => ENNReal.ofReal (g y))
    (fun y hy => by rw [hg y hy, ENNReal.ofReal_zero])]
  apply withDensity_congr_ae
  exact Eventually.of_forall (fun z => by
    change (Ioi (0 : ℝ)).indicator (fun z => ENNReal.ofReal (positivePowerJacobian C r z) *
      ENNReal.ofReal (g (positivePowerInverse C r z))) z =
        ENNReal.ofReal (positivePowerDensity C r g z)
    unfold positivePowerDensity
    by_cases hz : 0 < z
    · rw [indicator_of_mem (s := Ioi (0 : ℝ)) hz,
        indicator_of_mem (s := Ioi (0 : ℝ)) hz,
        ENNReal.ofReal_mul (positivePowerJacobian_pos hC hr hz).le]
    · rw [indicator_of_notMem (s := Ioi (0 : ℝ)) hz,
        indicator_of_notMem (s := Ioi (0 : ℝ)) hz, ENNReal.ofReal_zero])

/-- The Jacobian formula preserves probability normalization in both
directions. This follows from whole-measure equality and measurable
generation, independently of any proposed density integral value. -/
theorem positivePowerDensity_probability_iff {C r : ℝ} (hC : 0 < C) (hr : 0 < r)
    (g : ℝ → ℝ) (hg : ∀ y : ℝ, y ≤ 0 → g y = 0) :
    IsProbabilityMeasure (volume.withDensity (fun z =>
      ENNReal.ofReal (positivePowerDensity C r g z))) ↔
        IsProbabilityMeasure (volume.withDensity (fun y => ENNReal.ofReal (g y))) := by
  rw [← map_positivePower_realDensity hC hr g hg]
  exact Measure.isProbabilityMeasure_map_iff (measurable_positivePower C r).aemeasurable

example : (volume.withDensity ((Ioo (0 : ℝ) 1).indicator (fun _ => (1 : ENNReal)))).map
    (positivePower 2 3) = volume.withDensity ((Ioi (0 : ℝ)).indicator (fun z =>
      ENNReal.ofReal (positivePowerJacobian 2 3 z) *
        (Ioo (0 : ℝ) 1).indicator (fun _ => (1 : ENNReal)) (positivePowerInverse 2 3 z))) := by
  apply map_positivePower_withDensity (by norm_num) (by norm_num)
  intro y hy
  exact indicator_of_notMem (by intro h; exact (not_lt_of_ge hy) h.1) _

example : Measurable (positivePowerDensity 2 3
    ((Ioo (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)))) :=
  measurable_positivePowerDensity _ _ (measurable_const.indicator measurableSet_Ioo)

example (z : ℝ) : 0 ≤ positivePowerDensity 2 3
    ((Ioo (0 : ℝ) 1).indicator (fun _ => (1 : ℝ))) z := by
  apply positivePowerDensity_nonneg (by norm_num) (by norm_num)
  exact fun y => indicator_nonneg (fun _ _ => zero_le_one) y

example : (volume.withDensity (fun y => ENNReal.ofReal
    ((Ioo (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) y))).map (positivePower 2 3) =
      volume.withDensity (fun z => ENNReal.ofReal (positivePowerDensity 2 3
        ((Ioo (0 : ℝ) 1).indicator (fun _ => (1 : ℝ))) z)) := by
  apply map_positivePower_realDensity (by norm_num) (by norm_num)
  intro y hy
  exact indicator_of_notMem (by intro h; exact (not_lt_of_ge hy) h.1) _

#print axioms map_positivePower_withDensity
#print axioms positivePowerDensity_nonneg
#print axioms map_positivePower_realDensity

example : IsProbabilityMeasure (volume.withDensity (fun z => ENNReal.ofReal
    (positivePowerDensity 2 3 ((Ioo (0 : ℝ) 1).indicator (fun _ => (1 : ℝ))) z))) ↔
      IsProbabilityMeasure (volume.withDensity (fun y => ENNReal.ofReal
        ((Ioo (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) y))) := by
  apply positivePowerDensity_probability_iff (by norm_num) (by norm_num)
  intro y hy
  exact indicator_of_notMem (by intro h; exact (not_lt_of_ge hy) h.1) _

#print axioms positivePowerDensity_probability_iff

end TailOptionPricing
