module

/-
  Euler's real Gamma approximants as scaled Beta values, used for the
  expectation asymptotic following Proposition 1 of arXiv:2004.05894v1.
-/
public import Mathlib.Probability.Distributions.Beta

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory Filter Topology

namespace TailOptionPricing

/-- Euler's Gamma approximant equals a scaled real Beta normalizing
constant, for every positive real shape. -/
theorem realGammaSeq_eq_beta {r : ℝ} (hr : 0 < r) (n : ℕ) :
    Real.GammaSeq r n = (n : ℝ) ^ r * ProbabilityTheory.beta r ((n : ℝ) + 1) := by
  have hc : ((Real.GammaSeq r n : ℝ) : ℂ) = Complex.GammaSeq r n := by
    dsimp only [Real.GammaSeq, Complex.GammaSeq]
    push_cast
    rw [Complex.ofReal_cpow (Nat.cast_nonneg n), Complex.ofReal_natCast]
  have hb : ((ProbabilityTheory.beta r ((n : ℝ) + 1) : ℝ) : ℂ) =
      Complex.betaIntegral r ((n : ℂ) + 1) := by
    rw [Complex.betaIntegral_eq_Gamma_mul_div _ _ (by simpa using hr) (by
      simp only [Complex.add_re, Complex.natCast_re, Complex.one_re]
      positivity)]
    unfold ProbabilityTheory.beta
    rw [Complex.ofReal_div, Complex.ofReal_mul, ← Complex.Gamma_ofReal,
      ← Complex.Gamma_ofReal, ← Complex.Gamma_ofReal]
    norm_cast
  apply Complex.ofReal_injective
  rw [hc, Complex.GammaSeq_eq_betaIntegral_of_re_pos (by simpa using hr),
    Complex.ofReal_mul, Complex.ofReal_cpow (Nat.cast_nonneg n), hb, Complex.ofReal_natCast]

end TailOptionPricing
