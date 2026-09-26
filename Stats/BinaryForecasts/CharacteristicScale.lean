/-
  Statistical differences between binary forecasts and real-world payoffs.
    Taleb, arXiv:1907.11162v3 (Dec 2019).

  ## Stats.BinaryForecasts.CharacteristicScale — paper Definition 4.

  Characteristic scale of a distribution, defining the borderline
  between the L¹/L² regime and the heavy-tailed regime.

  See `Stats/BinaryForecasts.lean` for the umbrella module.
-/
import Stats.Pareto
import Stats.BlackScholes

open Real Set MeasureTheory Filter Topology
open scoped NNReal

namespace TailOptionPricing

open ProbabilityTheory

/-! ## Characteristic scale (paper Definition 4).

    The characteristic scale `λ` of a positive random variable `X` is
        λ := lim_{K → ∞} (1/K) · E[X | X > K]
           = lim_{K → ∞} (∫_K^∞ x · f(x) dx) / (K · ∫_K^∞ f(x) dx).
    Pareto: `λ = α / (α − 1) > 1` (fat-tailed class `D_2`, no
    characteristic scale).  Gaussian: `λ = 1` (thin-tailed class `D_1`,
    finite characteristic scale).

    We work *pointwise* in `K`: for Pareto the ratio is the constant
    `α / (α − 1)` for every `K ≥ l`, so the limit is trivial. -/

/-- **Pointwise tail-ratio under strong Pareto (paper Eq. 7).**  For the
    strong Pareto law on `[l, ∞)` with tail index `α > 1`, the
    conditional-mean ratio is identically the constant `α / (α − 1)`:
        (∫_K^∞ x · f(x) dx) / (K · ∫_K^∞ f(x) dx) = α / (α − 1)
    for every `K ≥ l`.  The limit `K → ∞` is then trivial.

    Direct corollary of `paretoTailExpectation_div_survival`. -/
theorem characteristicScale_pareto {l α K : ℝ}
    (hα : 1 < α) (hl : 0 < l) (hK : l ≤ K) :
    paretoTailExpectation l α K / (K * survival l α K) = α / (α - 1) := by
  have hK_pos : 0 < K := hl.trans_le hK
  have hK_ne : K ≠ 0 := hK_pos.ne'
  have h := paretoTailExpectation_div_survival hα hl hK
  -- paretoTailExpectation/survival = α·K/(α-1)
  have h_surv_pos : 0 < survival l α K := by
    unfold survival; positivity
  have h_surv_ne : survival l α K ≠ 0 := h_surv_pos.ne'
  -- LHS = (paretoTailExpectation/survival) / K = (α·K/(α-1)) / K = α/(α-1).
  rw [show paretoTailExpectation l α K / (K * survival l α K)
        = (paretoTailExpectation l α K / survival l α K) / K from by
      field_simp]
  rw [h]
  field_simp

/-- **Fat-tail signature: Pareto characteristic scale exceeds 1.**  For
    `α > 1`, the Pareto tail-ratio satisfies `α / (α − 1) > 1`, placing
    Pareto in class `D_2` (no characteristic scale). -/
theorem characteristicScale_pareto_gt_one {α : ℝ} (hα : 1 < α) :
    1 < α / (α - 1) := by
  have hα1_pos : 0 < α - 1 := by linarith
  rw [lt_div_iff₀ hα1_pos, one_mul]
  linarith


end TailOptionPricing
