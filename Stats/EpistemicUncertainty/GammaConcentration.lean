module

/-
  Actual concentration of Section VI's matched Gamma precision,
  arXiv:1912.00277v2. Its mean tends to one and its variance tends
  to zero as the positive epistemic log variance tends to zero.
  The resulting squared-distance moment bounds actual probabilities,
  before any weak Gaussian limit is asserted for the compound law.
-/
public import Stats.EpistemicUncertainty.GammaMatch
public import Stats.Probability.GammaMomentDomain
public import Stats.Probability.Concentration

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory Filter Topology

namespace TailOptionPricing

open LognormalMeasure

/-- The matched actual precision's squared distance from one is L1
for every positive epistemic log variance (Section VI). -/
theorem epistemicGammaMatch_integrable_sub_one_sq {v : ℝ} (hv : 0 < v) :
    Integrable (fun x : ℝ => (x - 1) ^ 2)
      (gammaMeasure (epistemicGammaMatchShape v) (epistemicGammaMatchRate v)) := by
  let := epistemicGammaMatch_probability hv
  have h₁ : Integrable (fun x : ℝ => x)
      (gammaMeasure (epistemicGammaMatchShape v) (epistemicGammaMatchRate v)) := by
    simpa only [pow_one] using gammaMeasure_integrable_pow
      (epistemicGammaMatchShape_pos hv) (epistemicGammaMatchRate_pos hv) 1
  have h₂ := gammaMeasure_integrable_pow
    (epistemicGammaMatchShape_pos hv) (epistemicGammaMatchRate_pos hv) 2
  have he : (fun x : ℝ => (x - 1) ^ 2) = (fun x => x ^ 2 - 2 * x + 1) := by
    funext x
    ring
  rw [he]
  exact (h₂.sub' (h₁.const_mul 2)).fun_add (integrable_const 1)

/-- Actual mean-square deviation from one, using the independently
proved Gamma/lognormal mean and variance match (Section VI). Its
right boundary limit is zero although the Gamma parameters diverge. -/
theorem epistemicGammaMatch_moment_sub_one_sq {v : ℝ} (hv : 0 < v) :
    (∫ x : ℝ, (x - 1) ^ 2
      ∂gammaMeasure (epistemicGammaMatchShape v) (epistemicGammaMatchRate v)) =
        (Real.exp v - 1) * Real.exp v + (Real.exp (v / 2) - 1) ^ 2 := by
  let := epistemicGammaMatch_probability hv
  have h₁ : Integrable (fun x : ℝ => x)
      (gammaMeasure (epistemicGammaMatchShape v) (epistemicGammaMatchRate v)) := by
    simpa only [pow_one] using gammaMeasure_integrable_pow
      (epistemicGammaMatchShape_pos hv) (epistemicGammaMatchRate_pos hv) 1
  have h₂ := gammaMeasure_integrable_pow
    (epistemicGammaMatchShape_pos hv) (epistemicGammaMatchRate_pos hv) 2
  have hm := epistemicGammaMatch_mean (v := NNReal.mk v hv.le) hv
  rw [lognormalReal_mean] at hm
  change (∫ x : ℝ, x
    ∂gammaMeasure (epistemicGammaMatchShape v) (epistemicGammaMatchRate v)) =
      Real.exp (0 + v / 2) at hm
  rw [zero_add] at hm
  have hv' := epistemicGammaMatch_variance (v := NNReal.mk v hv.le) hv
  rw [lognormalReal_variance] at hv'
  change variance (fun x : ℝ => x)
    (gammaMeasure (epistemicGammaMatchShape v) (epistemicGammaMatchRate v)) =
      (Real.exp v - 1) * Real.exp (2 * 0 + v) at hv'
  have hl₂ : MemLp (fun x : ℝ => x) 2
      (gammaMeasure (epistemicGammaMatchShape v) (epistemicGammaMatchRate v)) :=
    (memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).mpr h₂
  rw [variance_eq_sub hl₂] at hv'
  change (∫ x : ℝ, x ^ 2
    ∂gammaMeasure (epistemicGammaMatchShape v) (epistemicGammaMatchRate v)) -
      (∫ x : ℝ, x
        ∂gammaMeasure (epistemicGammaMatchShape v) (epistemicGammaMatchRate v)) ^ 2 =
          (Real.exp v - 1) * Real.exp (2 * 0 + v) at hv'
  rw [hm] at hv'
  have he : (fun x : ℝ => (x - 1) ^ 2) = (fun x => x ^ 2 - 2 * x + 1) := by
    funext x
    ring
  rw [he, integral_add (h₂.sub' (h₁.const_mul 2)) (integrable_const 1),
    integral_sub h₂ (h₁.const_mul 2), integral_const_mul, integral_const, hm]
  simp only [probReal_univ, smul_eq_mul, one_mul, mul_zero, zero_add] at *
  nlinarith only [hv']

/-- Along every positive-variance family tending to zero, the actual
Gamma precision's mean-square distance from one tends to zero.
This is a law moment, not just a limit of the scalar shape parameter. -/
theorem epistemicGammaMatch_moment_sub_one_sq_tendsto_zero {ι : Type*} {l : Filter ι}
    {v : ι → ℝ} (hv : ∀ i, 0 < v i) (hv₀ : Tendsto v l (𝓝 0)) :
    Tendsto (fun i => ∫ x : ℝ, (x - 1) ^ 2
      ∂gammaMeasure (epistemicGammaMatchShape (v i)) (epistemicGammaMatchRate (v i)))
        l (𝓝 0) := by
  have he : Tendsto (fun i => Real.exp (v i)) l (𝓝 1) := by
    simpa only [Real.exp_zero, Function.comp_def] using Real.continuous_exp.continuousAt.tendsto.comp hv₀
  have hh : Tendsto (fun i => Real.exp (v i / 2)) l (𝓝 1) := by
    have ht : Tendsto (fun i => v i / 2) l (𝓝 0) := by
      simpa only [zero_div] using hv₀.div_const 2
    simpa only [Real.exp_zero, Function.comp_def] using Real.continuous_exp.continuousAt.tendsto.comp ht
  have ht := ((he.sub_const 1).mul he).add ((hh.sub_const 1).pow 2)
  simpa only [epistemicGammaMatch_moment_sub_one_sq (hv _), sub_self, zero_mul,
    zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add] using ht

/-- Every fixed positive-distance event for the actual matched Gamma
precision is bounded by its evaluated mean-square deviation divided by
the squared radius (Section VI). This is a quantitative probability bound. -/
theorem epistemicGammaMatch_tail_le {v δ : ℝ} (hv : 0 < v) (hδ : 0 < δ) :
    (gammaMeasure (epistemicGammaMatchShape v) (epistemicGammaMatchRate v)).real
      {x | δ ≤ |x - 1|} ≤
        ((Real.exp v - 1) * Real.exp v + (Real.exp (v / 2) - 1) ^ 2) / δ ^ 2 := by
  have ht := measureReal_abs_sub_ge_le_integral_sq hδ
    (epistemicGammaMatch_integrable_sub_one_sq hv)
  rwa [epistemicGammaMatch_moment_sub_one_sq hv] at ht

/-- Every fixed positive-distance event for the actual matched Gamma
precision has probability tending to zero. Markov is applied to its
L1 squared distance from one (Section VI's zero-error boundary). -/
theorem epistemicGammaMatch_tail_tendsto_zero {ι : Type*} {l : Filter ι} {v : ι → ℝ}
    (hv : ∀ i, 0 < v i) (hv₀ : Tendsto v l (𝓝 0)) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun i => (gammaMeasure (epistemicGammaMatchShape (v i))
      (epistemicGammaMatchRate (v i))).real {x | δ ≤ |x - 1|}) l (𝓝 0) := by
  exact measureReal_abs_sub_ge_tendsto_zero_of_integral_sq
    (fun i => epistemicGammaMatch_integrable_sub_one_sq (hv i))
    (epistemicGammaMatch_moment_sub_one_sq_tendsto_zero hv hv₀) hδ

example : Integrable (fun x : ℝ => (x - 1) ^ 2)
    (gammaMeasure (epistemicGammaMatchShape 1) (epistemicGammaMatchRate 1)) :=
  epistemicGammaMatch_integrable_sub_one_sq (by norm_num)

example : (∫ x : ℝ, (x - 1) ^ 2
    ∂gammaMeasure (epistemicGammaMatchShape 1) (epistemicGammaMatchRate 1)) =
      (Real.exp 1 - 1) * Real.exp 1 + (Real.exp (1 / 2) - 1) ^ 2 :=
  epistemicGammaMatch_moment_sub_one_sq (by norm_num)

example : Tendsto (fun n : ℕ => ∫ x : ℝ, (x - 1) ^ 2
    ∂gammaMeasure (epistemicGammaMatchShape (Real.exp (-(n : ℝ))))
      (epistemicGammaMatchRate (Real.exp (-(n : ℝ))))) atTop (𝓝 0) :=
  epistemicGammaMatch_moment_sub_one_sq_tendsto_zero (fun _ => Real.exp_pos _)
    (Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop)

example : Tendsto (fun n : ℕ =>
    (gammaMeasure (epistemicGammaMatchShape (Real.exp (-(n : ℝ))))
      (epistemicGammaMatchRate (Real.exp (-(n : ℝ))))).real {x | 1 ≤ |x - 1|})
        atTop (𝓝 0) :=
  epistemicGammaMatch_tail_tendsto_zero (fun _ => Real.exp_pos _)
    (Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop) (by norm_num)

example : (gammaMeasure (epistemicGammaMatchShape 1) (epistemicGammaMatchRate 1)).real
    {x | 2 ≤ |x - 1|} ≤
      ((Real.exp 1 - 1) * Real.exp 1 + (Real.exp (1 / 2) - 1) ^ 2) / 2 ^ 2 :=
  epistemicGammaMatch_tail_le (by norm_num) (by norm_num)

#print axioms epistemicGammaMatch_integrable_sub_one_sq
#print axioms epistemicGammaMatch_moment_sub_one_sq
#print axioms epistemicGammaMatch_moment_sub_one_sq_tendsto_zero
#print axioms epistemicGammaMatch_tail_tendsto_zero
#print axioms epistemicGammaMatch_tail_le

end TailOptionPricing
