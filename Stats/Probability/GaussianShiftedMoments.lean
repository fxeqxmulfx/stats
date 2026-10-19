module

/-
  Actual Gaussian moments about an arbitrary center, needed by the
  switching-mean model of arXiv:1802.05495v3, Eq. 17. The law is shifted
  by an actual Gaussian pushforward; polynomial integration uses proved L1.
-/
public import Stats.Probability.GaussianMoments

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory

namespace TailOptionPricing

/-- L1 of every power about any finite center for the actual Gaussian
components in arXiv:1802.05495v3, Eq. 17. -/
theorem gaussianReal_integrable_sub_pow (μ c : ℝ) (v : NNReal) (n : ℕ) :
    Integrable (fun x : ℝ => (x - c) ^ n) (gaussianReal μ v) := by
  have hm : AEStronglyMeasurable (fun x : ℝ => x ^ n)
      ((gaussianReal μ v).map (fun x : ℝ => x - c)) :=
    (measurable_id.pow_const n).aestronglyMeasurable
  have hi : Integrable (fun x : ℝ => x ^ n)
      ((gaussianReal μ v).map (fun x : ℝ => x - c)) := by
    rw [gaussianReal_map_sub_const]
    exact gaussianReal_integrable_pow _ _ _
  exact (integrable_map_measure hm (measurable_id.sub_const c).aemeasurable).mp hi

/-- The actual centered third Gaussian moment vanishes by reflection
symmetry, before expanding the switching-mean fourth moment (Eq. 17). -/
theorem gaussianReal_zero_moment_three (v : NNReal) :
    (∫ x : ℝ, x ^ 3 ∂gaussianReal 0 v) = 0 := by
  have hm : AEStronglyMeasurable (fun x : ℝ => x ^ 3)
      ((gaussianReal 0 v).map (fun x : ℝ => -x)) :=
    (measurable_id.pow_const 3).aestronglyMeasurable
  have he := integral_map measurable_neg.aemeasurable hm
  rw [gaussianReal_map_neg, neg_zero] at he
  have hn : (fun x : ℝ => (-x) ^ 3) = fun x : ℝ => -(x ^ 3) := by
    funext x
    ring
  rw [hn, integral_neg] at he
  linarith

/-- Actual second Gaussian moment about an arbitrary center in
arXiv:1802.05495v3, Eq. 17's mixture variance calculation. -/
theorem gaussianReal_momentAbout_two (μ c : ℝ) (v : NNReal) :
    (∫ x : ℝ, (x - c) ^ 2 ∂gaussianReal μ v) = (v : ℝ) + (μ - c) ^ 2 := by
  have hmap : (gaussianReal 0 v).map (fun x : ℝ => μ + x) = gaussianReal μ v := by
    simpa only [zero_add] using gaussianReal_map_const_add (μ := 0) (v := v) μ
  have hm : AEStronglyMeasurable (fun x : ℝ => (x - c) ^ 2)
      ((gaussianReal 0 v).map (fun x : ℝ => μ + x)) :=
    ((measurable_id.sub_const c).pow_const 2).aestronglyMeasurable
  rw [← hmap, integral_map (measurable_const_add μ).aemeasurable hm]
  have he : (fun x : ℝ => (μ + x - c) ^ 2) =
      fun x : ℝ => x ^ 2 + 2 * (μ - c) * x + (μ - c) ^ 2 := by
    funext x
    ring
  have h1 : Integrable (fun x : ℝ => x) (gaussianReal 0 v) := by
    simpa only [pow_one] using gaussianReal_integrable_pow 0 v 1
  have h2 := gaussianReal_integrable_pow 0 v 2
  have hs : Integrable (fun x : ℝ => x ^ 2 + 2 * (μ - c) * x) (gaussianReal 0 v) :=
    h2.add (h1.const_mul (2 * (μ - c)))
  rw [he, integral_add hs (integrable_const _),
    integral_add h2 (h1.const_mul (2 * (μ - c))), integral_const_mul,
    gaussianReal_zero_moment_two, integral_id_gaussianReal]
  simp

/-- Actual fourth Gaussian moment about an arbitrary center for
arXiv:1802.05495v3, Eq. 17. In particular the noncentered term is
(mu-c)^4, not (mu-c)^2. Every integrated polynomial term is L1. -/
theorem gaussianReal_momentAbout_four (μ c : ℝ) (v : NNReal) :
    (∫ x : ℝ, (x - c) ^ 4 ∂gaussianReal μ v) =
      3 * (v : ℝ) ^ 2 + 6 * (v : ℝ) * (μ - c) ^ 2 + (μ - c) ^ 4 := by
  have hmap : (gaussianReal 0 v).map (fun x : ℝ => μ + x) = gaussianReal μ v := by
    simpa only [zero_add] using gaussianReal_map_const_add (μ := 0) (v := v) μ
  have hm : AEStronglyMeasurable (fun x : ℝ => (x - c) ^ 4)
      ((gaussianReal 0 v).map (fun x : ℝ => μ + x)) :=
    ((measurable_id.sub_const c).pow_const 4).aestronglyMeasurable
  rw [← hmap, integral_map (measurable_const_add μ).aemeasurable hm]
  have he : (fun x : ℝ => (μ + x - c) ^ 4) = fun x : ℝ =>
      x ^ 4 + 4 * (μ - c) * x ^ 3 + 6 * (μ - c) ^ 2 * x ^ 2 +
        4 * (μ - c) ^ 3 * x + (μ - c) ^ 4 := by
    funext x
    ring
  have hi : Integrable (fun x : ℝ => x) (gaussianReal 0 v) := by
    simpa only [pow_one] using gaussianReal_integrable_pow 0 v 1
  have h4 := gaussianReal_integrable_pow 0 v 4
  have h3 := (gaussianReal_integrable_pow 0 v 3).const_mul (4 * (μ - c))
  have h2 := (gaussianReal_integrable_pow 0 v 2).const_mul (6 * (μ - c) ^ 2)
  have h1 := hi.const_mul (4 * (μ - c) ^ 3)
  have h43 : Integrable (fun x : ℝ => x ^ 4 + 4 * (μ - c) * x ^ 3) (gaussianReal 0 v) :=
    h4.add h3
  have h432 : Integrable (fun x : ℝ => x ^ 4 + 4 * (μ - c) * x ^ 3 +
      6 * (μ - c) ^ 2 * x ^ 2) (gaussianReal 0 v) := h43.add h2
  have h4321 : Integrable (fun x : ℝ => x ^ 4 + 4 * (μ - c) * x ^ 3 +
      6 * (μ - c) ^ 2 * x ^ 2 + 4 * (μ - c) ^ 3 * x) (gaussianReal 0 v) := h432.add h1
  rw [he, integral_add h4321 (integrable_const _),
    integral_add h432 h1, integral_add h43 h2,
    integral_add h4 h3]
  rw [integral_const_mul, integral_const_mul, integral_const_mul,
    gaussianReal_zero_moment_four, gaussianReal_zero_moment_three,
    gaussianReal_zero_moment_two, integral_id_gaussianReal]
  simp
  ring

example : Integrable (fun x : ℝ => (x - 1) ^ 4) (gaussianReal 2 9) :=
  gaussianReal_integrable_sub_pow _ _ _ _

example : (∫ x : ℝ, x ^ 3 ∂gaussianReal 0 9) = 0 := gaussianReal_zero_moment_three _

example : (∫ x : ℝ, (x - 1) ^ 2 ∂gaussianReal 2 9) = 10 := by
  rw [gaussianReal_momentAbout_two]
  norm_num

example : (∫ x : ℝ, (x - 1) ^ 4 ∂gaussianReal 2 9) = 298 := by
  rw [gaussianReal_momentAbout_four]
  norm_num

#print axioms gaussianReal_integrable_sub_pow
#print axioms gaussianReal_zero_moment_three
#print axioms gaussianReal_momentAbout_four

end TailOptionPricing
