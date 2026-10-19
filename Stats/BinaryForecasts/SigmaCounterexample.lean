module

/-
  arXiv:1907.11162v3, Eq. 8 and the following universal positivity claim
  (source lines 471–475). Positive K=3 and sigma=5 give a negative
  sensitivity. The printed A-B quantity differs from Definition 5's A-K*B.
-/
public import Stats.BinaryForecasts.SigmaSensitivity

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory Filter Topology

namespace TailOptionPricing

/-- Counterexample to the universal positivity asserted immediately
after Eq. 8 in arXiv:1907.11162v3: K=3 and sigma=5 give numerator -21. -/
theorem gaussianEq8_negative_at_three_five :
    Real.exp (-(3 : ℝ) ^ 2 / (2 * 5 ^ 2)) *
      ((3 - 1) * 3 ^ 3 - (3 - 2) * 3 * 5 ^ 2) /
      (Real.sqrt (2 * Real.pi) * 5 ^ 5) < 0 := by
  apply div_neg_of_neg_of_pos
  · exact mul_neg_of_pos_of_neg (Real.exp_pos _) (by norm_num)
  · positivity

/-- The printed Eq. 8 derivative, not the missing K-weighted true gap,
has a strictly negative value at positive parameters K=3 and sigma=5. -/
theorem gaussianEq8_exists_negative_derivative :
    ∃ d : ℝ, d < 0 ∧ HasDerivAt
      (fun s : ℝ => gaussianPDFReal 0 1 (3 / s) * (1 + 3 ^ 2 / s ^ 2) -
        3 / s ^ 2 * gaussianPDFReal 0 1 (3 / s)) d 5 := by
  refine ⟨_, gaussianEq8_negative_at_three_five, ?_⟩
  exact gaussianEq8_sigmaSensitivity_eq (K := 3) (σ := 5) (by norm_num)

/-- Formal refutation of Eq. 8's claimed positivity for all positive
thresholds and scales; the sigma=1 polynomial does not prove this claim. -/
theorem gaussianEq8_not_always_positive :
    ¬ ∀ K σ : ℝ, 0 < K → 0 < σ →
      0 < Real.exp (-K ^ 2 / (2 * σ ^ 2)) *
        ((K - 1) * K ^ 3 - (K - 2) * K * σ ^ 2) /
        (Real.sqrt (2 * Real.pi) * σ ^ 5) := by
  intro h
  have hp := h 3 5 (by norm_num) (by norm_num)
  exact (not_lt_of_ge gaussianEq8_negative_at_three_five.le) hp

#print axioms gaussianEq8_negative_at_three_five
#print axioms gaussianEq8_exists_negative_derivative
#print axioms gaussianEq8_not_always_positive

end TailOptionPricing
