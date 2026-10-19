module

/-
  Actual binomial collapse of the finite constant-error dispersion law,
  arXiv:1912.00277v2, Section III. Pascal's identity is applied to the
  actual recursive expectation, for arbitrary real-valued test functions.
-/
public import Stats.EpistemicUncertainty.ScaleLaw
public import Mathlib.Probability.Distributions.Binomial
public import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory Finset

namespace TailOptionPricing

private theorem binomial_sum_pascal (n : ℕ) (f : ℕ → ℝ) :
    ∑ j ∈ range (n + 2), ((n + 1).choose j : ℝ) * f j =
      ∑ j ∈ range (n + 1), (n.choose j : ℝ) * (f j + f (j + 1)) := by
  have hz : ∑ j ∈ range (n + 2), (n.choose j : ℝ) * f j =
      ∑ j ∈ range (n + 1), (n.choose j : ℝ) * f j := by
    rw [sum_range_succ]
    simp
  have hu := sum_range_succ' (fun j => (n.choose j : ℝ) * f j) (n + 1)
  rw [hz] at hu
  simp only [Nat.choose_zero_right, Nat.cast_one, one_mul] at hu
  rw [sum_range_succ']
  simp only [Nat.choose_succ_succ, Nat.cast_add, add_mul, Nat.choose_zero_right,
    Nat.cast_one, one_mul]
  rw [sum_add_distrib]
  simp only [mul_add, sum_add_distrib, Nat.succ_eq_add_one]
  linarith

private theorem binomial_half_weight (n j : ℕ) (hj : j ≤ n) :
    (n.choose j : ℝ) * (1 / 2 : ℝ) ^ j * (1 - 1 / 2 : ℝ) ^ (n - j) =
      (1 / 2 : ℝ) ^ n * (n.choose j : ℝ) := by
  have hp : (1 / 2 : ℝ) ^ j * (1 / 2 : ℝ) ^ (n - j) = (1 / 2 : ℝ) ^ n := by
    rw [← pow_add, show j + (n - j) = n by omega]
  rw [show (1 - 1 / 2 : ℝ) = 1 / 2 by norm_num, ← hp]
  ring

private theorem binomial_sum_prod (s : Finset ℕ) (ν : ℕ → Measure ℝ) (ρ : Measure ℝ)
    [∀ j, IsFiniteMeasure (ν j)] [SFinite ρ] :
    (∑ j ∈ s, ν j).prod ρ = ∑ j ∈ s, (ν j).prod ρ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hj ih => rw [sum_insert hj, Measure.add_prod, ih, sum_insert hj]

/-- Actual dispersion expectation as the binomial-weighted sum printed
in Section III. L1 of every test function follows independently from
the finite recursive atomic law. No moment-determinacy assumption is used. -/
theorem epistemicScaleLaw_integral_binomial (n : ℕ) (σ ε : ℝ) (f : ℝ → ℝ) :
    (∫ s : ℝ, f s ∂epistemicScaleLaw n σ ε) =
      (1 / 2 : ℝ) ^ n * ∑ j ∈ range (n + 1), (n.choose j : ℝ) *
        f (σ * (1 + ε) ^ j * (1 - ε) ^ (n - j)) := by
  induction n generalizing σ with
  | zero => simp [epistemicScaleLaw]
  | succ n ih =>
    rw [epistemicScaleLaw, equalMixture_integral (epistemicScaleLaw_integrable n _ ε f)
      (epistemicScaleLaw_integrable n _ ε f), ih, ih, binomial_sum_pascal]
    have he : (∑ j ∈ range (n + 1), (n.choose j : ℝ) *
        (f (σ * (1 + ε) ^ j * (1 - ε) ^ (n + 1 - j)) +
          f (σ * (1 + ε) ^ (j + 1) * (1 - ε) ^ (n + 1 - (j + 1))))) =
        (∑ j ∈ range (n + 1), (n.choose j : ℝ) *
          f (σ * (1 - ε) * (1 + ε) ^ j * (1 - ε) ^ (n - j))) +
        (∑ j ∈ range (n + 1), (n.choose j : ℝ) *
          f (σ * (1 + ε) * (1 + ε) ^ j * (1 - ε) ^ (n - j))) := by
      rw [← sum_add_distrib]
      apply sum_congr rfl
      intro j hj
      have hjn : j ≤ n := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj
      have hm : σ * (1 + ε) ^ j * (1 - ε) ^ (n + 1 - j) =
          σ * (1 - ε) * (1 + ε) ^ j * (1 - ε) ^ (n - j) := by
        rw [show n + 1 - j = n - j + 1 by omega, pow_succ]
        ring
      have hp : σ * (1 + ε) ^ (j + 1) * (1 - ε) ^ (n + 1 - (j + 1)) =
          σ * (1 + ε) * (1 + ε) ^ j * (1 - ε) ^ (n - j) := by
        rw [show n + 1 - (j + 1) = n - j by omega, pow_succ]
        ring
      rw [hm, hp, mul_add]
    rw [he, pow_succ (1 / 2 : ℝ) n]
    ring

/-- Whole-law binomial collapse for Section III's actual recursively
generated dispersion. A genuine Binomial(n,1/2) count is pushed through
the printed scale function. Equality is proved using all bounded
continuous test functions, rather than inferred from a few moments. -/
theorem epistemicScaleLaw_eq_binomial (n : ℕ) (σ ε : ℝ) :
    epistemicScaleLaw n σ ε =
      (binomial n ⟨1 / 2, by constructor <;> norm_num⟩).map
        (fun j : ℕ => σ * (1 + ε) ^ j * (1 - ε) ^ (n - j)) := by
  let p : unitInterval := ⟨1 / 2, by constructor <;> norm_num⟩
  change epistemicScaleLaw n σ ε = (binomial n p).map _
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  have hc : Measurable (fun j : ℕ => σ * (1 + ε) ^ j * (1 - ε) ^ (n - j)) :=
    measurable_of_countable _
  have hf : AEStronglyMeasurable (fun s : ℝ => f s) ((binomial n p).map
      (fun j : ℕ => σ * (1 + ε) ^ j * (1 - ε) ^ (n - j))) :=
    f.continuous.measurable.aestronglyMeasurable
  rw [epistemicScaleLaw_integral_binomial, integral_map hc.aemeasurable hf, integral_binomial]
  have hIic : Finset.Iic n = range (n + 1) := by
    ext j
    simp only [Finset.mem_Iic, Finset.mem_range]
    omega
  rw [hIic, Finset.mul_sum]
  simp only [smul_eq_mul]
  apply sum_congr rfl
  intro j hj
  have hjn : j ≤ n := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj
  change (1 / 2 : ℝ) ^ n * ((n.choose j : ℝ) *
    f (σ * (1 + ε) ^ j * (1 - ε) ^ (n - j))) =
    ((n.choose j : ℝ) * (1 / 2 : ℝ) ^ j * (1 - 1 / 2 : ℝ) ^ (n - j)) *
      f (σ * (1 + ε) ^ j * (1 - ε) ^ (n - j))
  rw [binomial_half_weight n j hjn]
  ring

/-- Actual Gaussian population as Section III's normalized binomial
mixture of genuine Gaussian measures. The scales and coefficients are
derived from the recursive law and the independent-innovation model. -/
theorem epistemicBranchLaw_eq_binomial_mixture (n : ℕ) (μ σ ε : ℝ) :
    epistemicBranchLaw n μ σ ε = ∑ j ∈ range (n + 1),
      ENNReal.ofReal ((1 / 2 : ℝ) ^ n * (n.choose j : ℝ)) • gaussianReal μ
        (NNReal.mk ((σ * (1 + ε) ^ j * (1 - ε) ^ (n - j)) ^ 2) (sq_nonneg _)) := by
  let p : unitInterval := ⟨1 / 2, by constructor <;> norm_num⟩
  let instFinite (j : ℕ) : IsFiniteMeasure
      (ENNReal.ofReal ((n.choose j : ℝ) * (p : ℝ) ^ j * (1 - p : ℝ) ^ (n - j)) •
        Measure.dirac (σ * (1 + ε) ^ j * (1 - ε) ^ (n - j))) :=
    Measure.smul_finite _ ENNReal.ofReal_ne_top
  have hc : Measurable (fun j : ℕ => σ * (1 + ε) ^ j * (1 - ε) ^ (n - j)) :=
    measurable_of_countable _
  have hm : Measurable (fun z : ℝ × ℝ => μ + z.1 * z.2) :=
    (measurable_fst.mul measurable_snd).const_add μ
  rw [← epistemicScaleLaw_outcome_model, epistemicScaleLaw_eq_binomial,
    binomial_eq_sum_dirac, Measure.map_finset_sum hc.aemeasurable]
  simp_rw [Measure.map_smul _ hc.aemeasurable, Measure.map_dirac]
  rw [binomial_sum_prod, Measure.map_finset_sum hm.aemeasurable]
  simp_rw [Measure.prod_smul_left, Measure.map_smul _ hm.aemeasurable,
    Measure.dirac_prod, Measure.map_map hm measurable_prodMk_left]
  simp only [Function.comp_def, gaussianReal_map_affine_scale]
  have hIic : Finset.Iic n = range (n + 1) := by
    ext j
    simp only [Finset.mem_Iic, Finset.mem_range]
    omega
  rw [hIic]
  apply sum_congr rfl
  intro j hj
  have hjn : j ≤ n := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj
  rw [binomial_half_weight n j hjn]

example : (∫ s : ℝ, s ^ 4 ∂epistemicScaleLaw 2 2 (1 / 2)) =
    (1 / 2 : ℝ) ^ 2 * ∑ j ∈ range 3, (Nat.choose 2 j : ℝ) *
      (2 * (1 + (1 / 2 : ℝ)) ^ j * (1 - (1 / 2 : ℝ)) ^ (2 - j)) ^ 4 :=
  epistemicScaleLaw_integral_binomial _ _ _ _

example : epistemicScaleLaw 2 2 (1 / 2) =
    (binomial 2 ⟨1 / 2, by constructor <;> norm_num⟩).map
      (fun j : ℕ => 2 * (1 + (1 / 2 : ℝ)) ^ j * (1 - (1 / 2 : ℝ)) ^ (2 - j)) :=
  epistemicScaleLaw_eq_binomial _ _ _

example : (epistemicScaleLaw 2 2 (1 / 2)).real {(3 / 2 : ℝ)} = 1 / 2 := by
  have h := epistemicScaleLaw_integral_binomial 2 2 (1 / 2)
    (({(3 / 2 : ℝ)} : Set ℝ).indicator (fun _ : ℝ => (1 : ℝ)))
  rw [integral_indicator (measurableSet_singleton (3 / 2 : ℝ))] at h
  simp only [setIntegral_const, smul_eq_mul, mul_one] at h
  norm_num [Finset.sum_range_succ, Set.indicator] at h
  exact h

example : epistemicBranchLaw 2 1 2 (1 / 2) = ∑ j ∈ range 3,
    ENNReal.ofReal ((1 / 2 : ℝ) ^ 2 * (Nat.choose 2 j : ℝ)) • gaussianReal 1
      (NNReal.mk ((2 * (1 + (1 / 2 : ℝ)) ^ j * (1 - (1 / 2 : ℝ)) ^ (2 - j)) ^ 2)
        (sq_nonneg _)) := epistemicBranchLaw_eq_binomial_mixture _ _ _ _

#print axioms epistemicScaleLaw_integral_binomial
#print axioms epistemicScaleLaw_eq_binomial
#print axioms epistemicBranchLaw_eq_binomial_mixture

end TailOptionPricing
