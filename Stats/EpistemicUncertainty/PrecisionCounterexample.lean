module

/-
  Counterexample to the uncentered lognormal approximation in
  arXiv:1912.00277v2, Section V, following Eq. lerrornapprox. Actual
  iid errors with values epsilon and -epsilon satisfy independence, zero mean,
  boundedness and positive finite-variance assumptions. For every fixed
  epsilon in (0,1), the actual and proposed Gaussian log laws have a
  tail-probability discrepancy tending to one half, even if epsilon
  is arbitrarily small. A correctly centered log-factor CLT is separate.
-/
public import Stats.EpistemicUncertainty.PrecisionLaw
public import Stats.EpistemicUncertainty.BinomialSurvival

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory Filter Topology

namespace TailOptionPricing

/-- Section V's proposed zero-centered Gaussian law for log precision.
The variance sums all n actual error variances: the source's printed
upper summation index 2 is corrected to n. Initial precision is one. -/
noncomputable def epistemicPrecisionGaussianApproximation (n : ℕ) (ε : ℝ) : Measure ℝ :=
  gaussianReal 0 (NNReal.mk ((n : ℝ) * ε ^ 2) (mul_nonneg (Nat.cast_nonneg n) (sq_nonneg ε)))

instance epistemicPrecisionGaussianApproximation_probability (n : ℕ) (ε : ℝ) :
    IsProbabilityMeasure (epistemicPrecisionGaussianApproximation n ε) := by
  unfold epistemicPrecisionGaussianApproximation
  infer_instance

/-- Every nondegenerate Gaussian proposed in Section V assigns
probability one half to nonnegative log precision, at every depth. -/
theorem epistemicPrecisionGaussianApproximation_real_Ici_zero (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    (epistemicPrecisionGaussianApproximation (n + 1) ε).real (Ici 0) = 1 / 2 := by
  have hn : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
  have hw : 0 < ε * √((n + 1 : ℕ) : ℝ) := mul_pos hε (Real.sqrt_pos.mpr hn)
  have hv : NNReal.mk (((n + 1 : ℕ) : ℝ) * ε ^ 2)
      (mul_nonneg (Nat.cast_nonneg (n + 1)) (sq_nonneg ε)) =
      NNReal.mk ((ε * √((n + 1 : ℕ) : ℝ)) ^ 2) (sq_nonneg _) := by
    apply NNReal.eq
    simp only [NNReal.coe_mk, mul_pow, Real.sq_sqrt hn.le]
    ring
  rw [epistemicPrecisionGaussianApproximation, hv, gaussianReal_real_Ici_affine_scale 0 hw]
  norm_num [stdNormalCdf_zero]

/-- Actual upper-tail discrepancy at the fixed threshold zero between
the log of the iid precision product and Section V's proposed normal. -/
noncomputable def epistemicPrecisionGaussianTailGap (n : ℕ) (ε : ℝ) : ℝ :=
  |(epistemicLogPrecisionLaw n 1 ε).real (Ici 0) -
    (epistemicPrecisionGaussianApproximation n ε).real (Ici 0)|

/-- Formal counterexample to Section V's uncentered normal/lognormal
approximation as depth tends to infinity. Even genuinely iid bounded
mean-zero errors of arbitrarily small fixed magnitude produce a tail
gap tending to one half, rather than zero. This does not concern a
CLT with the actual log-factor mean and variance. -/
theorem epistemicPrecisionGaussianTailGap_tendsto_half {ε : ℝ} (hε₀ : 0 < ε) (hε₁ : ε < 1) :
    Tendsto (fun n => epistemicPrecisionGaussianTailGap (n + 1) ε) atTop (𝓝 (1 / 2)) := by
  have ht := (epistemicLogPrecisionLaw_tail_tendsto_zero hε₀ hε₁).comp
    (Filter.tendsto_add_atTop_nat 1)
  have h := (ht.sub_const (1 / 2 : ℝ)).abs
  simp only [epistemicPrecisionGaussianTailGap,
    epistemicPrecisionGaussianApproximation_real_Ici_zero _ hε₀]
  simpa using h

/-- The source's proposed uncentered Gaussian is not an asymptotically
accurate tail approximation for the actual iid precision product. -/
theorem epistemicPrecisionGaussianTailGap_not_tendsto_zero {ε : ℝ}
    (hε₀ : 0 < ε) (hε₁ : ε < 1) :
    ¬Tendsto (fun n => epistemicPrecisionGaussianTailGap (n + 1) ε) atTop (𝓝 0) := by
  intro h
  have he := tendsto_nhds_unique (epistemicPrecisionGaussianTailGap_tendsto_half hε₀ hε₁) h
  norm_num at he

example : (epistemicPrecisionGaussianApproximation 10 (1 / 100)).real (Ici 0) = 1 / 2 :=
  epistemicPrecisionGaussianApproximation_real_Ici_zero 9 (by norm_num)

example : Tendsto (fun n => epistemicPrecisionGaussianTailGap (n + 1) (1 / 100))
    atTop (𝓝 (1 / 2)) :=
  epistemicPrecisionGaussianTailGap_tendsto_half (by norm_num) (by norm_num)

example : ¬Tendsto (fun n => epistemicPrecisionGaussianTailGap (n + 1) (1 / 100))
    atTop (𝓝 0) :=
  epistemicPrecisionGaussianTailGap_not_tendsto_zero (by norm_num) (by norm_num)

example (i : ℕ) : (0 : ℝ) <
    variance (epistemicErrorVariable (1 / 100) i) epistemicInfiniteSignLaw := by
  rw [epistemicErrorVariable_variance]
  norm_num

example (i : ℕ) (ω : ℕ → Bool) : |epistemicErrorVariable (1 / 100) i ω| = 1 / 100 := by
  rw [epistemicErrorVariable_abs]
  norm_num

#print axioms epistemicPrecisionGaussianApproximation_real_Ici_zero
#print axioms epistemicPrecisionGaussianTailGap_tendsto_half
#print axioms epistemicPrecisionGaussianTailGap_not_tendsto_zero

end TailOptionPricing
