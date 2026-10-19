module

/-
# The returns-tail bound with an actual volatility smile

Taleb et al., arXiv:1908.02347v3, "Arbitrage Boundaries", display
`arbitrage` and the final unnumbered display. The printed derivative
inequality has the wrong direction; a nonnegative right-hand mixed
butterfly gives `BSC' ≤ C'`. Here annual volatility is multiplied by
`sqrt t`, including in its strike derivative, and the Pareto denominator
is `log (l * S₀ / (K - S₀))`.
-/
public import Stats.BlackScholes.Smile
public import Stats.Pareto.Returns

@[expose] public section

open Real Set Filter Topology ProbabilityTheory

namespace TailOptionPricing

/-- Strike derivative of the integral-defined returns call, from Result 2
of arXiv:1908.02347v3. The strike lies strictly inside the Pareto tail. -/
theorem callPriceReturns_hasDerivAt {l α S₀ K : ℝ}
    (hα : 1 < α) (hl : 0 < l) (hS₀ : 0 < S₀)
    (hK : S₀ * (1 + l) < K) :
    HasDerivAt (callPriceReturns l α S₀) (-((l * S₀ / (K - S₀)) ^ α)) K := by
  have hshift : l * S₀ < K - S₀ := by nlinarith
  have h := (callPrice_hasDerivAt hα (mul_pos hl hS₀) hshift).comp K
    ((hasDerivAt_id K).sub_const S₀)
  have heq : callPriceReturns l α S₀ =ᶠ[𝓝 K]
      (fun x => callPrice (l * S₀) α (x - S₀)) := by
    filter_upwards [eventually_gt_nhds hK] with x hx
    rw [callPriceReturns_eq hα hl hS₀ hx.le,
      callPrice_eq hα (mul_pos hl hS₀) (by nlinarith)]
  simpa only [Function.comp_def, mul_one] using h.congr_of_eventuallyEq heq

example : HasDerivAt (callPriceReturns 1 2 1) (-(1 / 4 : ℝ)) 3 := by
  have h := callPriceReturns_hasDerivAt (l := 1) (α := 2) (S₀ := 1) (K := 3)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num at h
  exact h

/-- Negative strike derivative of the Black--Scholes surface with annual
volatility `σ`. This is a derivative expression; no probability law for an
arbitrary smile is asserted. Source: arXiv:1908.02347v3, final display. -/
noncomputable def bsSmileDigital (S₀ t : ℝ) (σ : ℝ → ℝ) (σ' K : ℝ) : ℝ :=
  stdNormalCdf ((Real.log (S₀ / K) - (σ K * Real.sqrt t) ^ 2 / 2) /
      (σ K * Real.sqrt t)) -
    S₀ * gaussianPDFReal 0 1
      ((Real.log (S₀ / K) + (σ K * Real.sqrt t) ^ 2 / 2) /
        (σ K * Real.sqrt t)) * (σ' * Real.sqrt t)

/-- The `erfc` form of the final display in arXiv:1908.02347v3, retaining
the Gaussian PDF instead of expanding it into powers and exponentials. -/
theorem bsSmileDigital_eq_erfc {S₀ K t σ' : ℝ} {σ : ℝ → ℝ} (ht : 0 ≤ t) :
    bsSmileDigital S₀ t σ σ' K =
      (1 / 2) * erfc ((Real.log (K / S₀) + t * (σ K) ^ 2 / 2) /
        (σ K * Real.sqrt t * Real.sqrt 2)) -
      S₀ * gaussianPDFReal 0 1
        ((Real.log (S₀ / K) + (σ K * Real.sqrt t) ^ 2 / 2) /
          (σ K * Real.sqrt t)) * (σ' * Real.sqrt t) := by
  let d := (Real.log (S₀ / K) - (σ K * Real.sqrt t) ^ 2 / 2) /
    (σ K * Real.sqrt t)
  have hlog : Real.log (S₀ / K) = -Real.log (K / S₀) := by
    rw [← Real.log_inv, inv_div]
  have harg : -d / Real.sqrt 2 =
      (Real.log (K / S₀) + t * (σ K) ^ 2 / 2) /
        (σ K * Real.sqrt t * Real.sqrt 2) := by
    dsimp [d]
    rw [neg_div, div_div, mul_pow, Real.sq_sqrt ht, hlog]
    ring
  have hCDF : stdNormalCdf d = (1 / 2) * erfc
      ((Real.log (K / S₀) + t * (σ K) ^ 2 / 2) /
        (σ K * Real.sqrt t * Real.sqrt 2)) := by
    calc
      stdNormalCdf d = 1 - stdNormalCdf (-d) := by rw [stdNormalCdf_neg]; ring
      _ = _ := by rw [one_sub_stdNormalCdf_eq_half_erfc, harg]
  unfold bsSmileDigital
  rw [hCDF]

example : bsSmileDigital 1 1 (fun _ => 1) 0 2 =
    (1 / 2) * erfc ((Real.log 2 + 1 / 2) / Real.sqrt 2) := by
  simpa using (bsSmileDigital_eq_erfc (S₀ := 1) (K := 2)
    (σ := fun _ => 1) (σ' := 0) (by norm_num : 0 ≤ (1 : ℝ)))

/-- The matched butterfly forces domination of the returns survival by the
negative smile derivative. Source: arXiv:1908.02347v3, `arbitrage`.
The conclusion is derived from the actual smile derivative, not assumed. -/
theorem returns_survival_le_bsSmileDigital {l α S₀ K t σ' : ℝ} {σ : ℝ → ℝ}
    (hα : 1 < α) (hl : 0 < l) (hS₀ : 0 < S₀)
    (hK : S₀ * (1 + l) < K) (ht : 0 < t)
    (hσ : 0 < σ K) (hσ' : HasDerivAt σ σ' K)
    (hmatch : callPriceBS_σ S₀ (σ K * Real.sqrt t) K = callPriceReturns l α S₀ K)
    (hbutterfly : ∀ᶠ d in 𝓝[>] (0 : ℝ),
      callPriceReturns l α S₀ (K + d) +
        callPriceBS_σ S₀ (σ (K - d) * Real.sqrt t) (K - d) ≥
      2 * callPriceReturns l α S₀ K) :
    (l * S₀ / (K - S₀)) ^ α ≤ bsSmileDigital S₀ t σ σ' K := by
  have hKpos : 0 < K := by nlinarith
  have hB := callPriceBS_σ_smile_hasDerivAt
    (σ := fun x => σ x * Real.sqrt t) (σ' := σ' * Real.sqrt t) hS₀ hKpos
    (mul_pos hσ (Real.sqrt_pos.mpr ht)) (hσ'.mul_const (Real.sqrt t))
  have h := deriv_le_of_matched_butterfly
    (callPriceReturns_hasDerivAt hα hl hS₀ hK) hB hmatch.symm hbutterfly
  unfold bsSmileDigital
  linarith

/-- Corrected final bound of arXiv:1908.02347v3, "Arbitrage Boundaries".
It uses returns, a differentiable annual-volatility smile, explicit time,
and the paper's matched-butterfly hypothesis. -/
theorem alpha_lower_bound_returns_smile {l α S₀ K t σ' : ℝ} {σ : ℝ → ℝ}
    (hα : 1 < α) (hl : 0 < l) (hS₀ : 0 < S₀)
    (hK : S₀ * (1 + l) < K) (ht : 0 < t)
    (hσ : 0 < σ K) (hσ' : HasDerivAt σ σ' K)
    (hmatch : callPriceBS_σ S₀ (σ K * Real.sqrt t) K = callPriceReturns l α S₀ K)
    (hbutterfly : ∀ᶠ d in 𝓝[>] (0 : ℝ),
      callPriceReturns l α S₀ (K + d) +
        callPriceBS_σ S₀ (σ (K - d) * Real.sqrt t) (K - d) ≥
      2 * callPriceReturns l α S₀ K) :
    Real.log (bsSmileDigital S₀ t σ σ' K) / Real.log (l * S₀ / (K - S₀)) ≤ α :=
  alpha_lower_bound (mul_pos hl hS₀) (by nlinarith)
    (returns_survival_le_bsSmileDigital hα hl hS₀ hK ht hσ hσ' hmatch hbutterfly)

/-- The corrected final returns-tail bound in `erfc` form. Source:
arXiv:1908.02347v3, final display of "Arbitrage Boundaries". The Gaussian
PDF is left normalized rather than expanded into powers of spot/strike. -/
theorem alpha_lower_bound_returns_smile_erfc {l α S₀ K t σ' : ℝ} {σ : ℝ → ℝ}
    (hα : 1 < α) (hl : 0 < l) (hS₀ : 0 < S₀)
    (hK : S₀ * (1 + l) < K) (ht : 0 < t)
    (hσ : 0 < σ K) (hσ' : HasDerivAt σ σ' K)
    (hmatch : callPriceBS_σ S₀ (σ K * Real.sqrt t) K = callPriceReturns l α S₀ K)
    (hbutterfly : ∀ᶠ d in 𝓝[>] (0 : ℝ),
      callPriceReturns l α S₀ (K + d) +
        callPriceBS_σ S₀ (σ (K - d) * Real.sqrt t) (K - d) ≥
      2 * callPriceReturns l α S₀ K) :
    Real.log ((1 / 2) * erfc ((Real.log (K / S₀) + t * (σ K) ^ 2 / 2) /
        (σ K * Real.sqrt t * Real.sqrt 2)) -
      S₀ * gaussianPDFReal 0 1
        ((Real.log (S₀ / K) + (σ K * Real.sqrt t) ^ 2 / 2) /
          (σ K * Real.sqrt t)) * (σ' * Real.sqrt t)) /
      Real.log (l * S₀ / (K - S₀)) ≤ α := by
  have h := alpha_lower_bound_returns_smile hα hl hS₀ hK ht hσ hσ' hmatch hbutterfly
  rwa [bsSmileDigital_eq_erfc ht.le] at h

end TailOptionPricing
