module

/-
  Risk measures & portfolio theory under Pareto.

  ## Stats.RiskMeasures.Kelly — Kelly criterion (Item 6).

  Definitions of density-weighted log payoffs and their pointwise
  derivatives and curvature. No derivative-under-the-integral theorem,
  constrained portfolio problem or optimal stake is proved here.

  See `Stats/RiskMeasures.lean` for the umbrella module.
-/
public import Stats.Pareto

@[expose] public section

open Real Set MeasureTheory Filter Topology intervalIntegral

namespace TailOptionPricing

/-! ## Item 6 — Kelly criterion under Pareto.

    The Kelly criterion seeks the bet fraction `f` that maximises the
    expected log-growth `g(f) := E[log(1 + f·X)]`.  For `X ~ Pareto(l,
    α)` the integrand `log(1 + f·s)` admits no elementary
    antiderivative against the Pareto density — closed forms involve
    Lerch / hypergeometric special functions.  The maximisation is
    a separate problem: admissible stakes, integrability and an actual
    objective derivative must be established before asserting an optimum.

    We formalise the algebraic / analytic ingredients:

    * Pointwise derivative `d/df log(1 + f·s) = s / (1 + f·s)`,
    * Pointwise second derivative
        `d²/df² log(1 + f·s) = −s² / (1 + f·s)²`,
    * Nonpositivity of the pointwise curvature when `1 + f*s > 0`.

    Lifting these facts to an objective requires integrability and
    differentiation or strict-concavity arguments for the integral.
    The pointwise statements below do not supply those steps or prove
    existence of a critical point for an unconstrained positive payoff.

    Time-vs-ensemble subtleties (Tier 8) are out of scope here. -/

/-- **Kelly integrand:** `log(1 + f·s) · paretoDensity l α s`. -/
noncomputable def kellyIntegrand (f l α s : ℝ) : ℝ :=
  Real.log (1 + f * s) * paretoDensity l α s

/-- The density integral `∫_l^∞ log(1+f*s) paretoDensity(s) ds`.
An expected-log-growth interpretation requires a valid Pareto law,
admissible stakes and integrability. -/
noncomputable def kellyObjective (f l α : ℝ) : ℝ :=
  ∫ s in Ioi l, kellyIntegrand f l α s

/-- The pointwise marginal expression weighted by the Pareto density.
No differentiation under the objective's integral is asserted here. -/
noncomputable def kellyMarginalIntegrand (f l α s : ℝ) : ℝ :=
  s / (1 + f * s) * paretoDensity l α s

/-- **Pointwise first-order Kelly derivative** (in `f`).  Captures
    `d/df log(1 + f·s) = s / (1 + f·s)` whenever `1 + f·s > 0`. -/
theorem kelly_log_hasDerivAt {f s : ℝ} (h : 0 < 1 + f * s) :
    HasDerivAt (fun f => Real.log (1 + f * s)) (s / (1 + f * s)) f := by
  have h_ne : (1 + f * s) ≠ 0 := h.ne'
  have h_inner : HasDerivAt (fun f : ℝ => 1 + f * s) s f := by
    have h1 := ((hasDerivAt_id f).mul_const s).const_add (1:ℝ)
    convert h1 using 1 <;> simp [mul_comm]
  have h_log := (Real.hasDerivAt_log h_ne).comp f h_inner
  -- h_log : HasDerivAt (log ∘ fun f => 1 + f * s) ((1 + f * s)⁻¹ * s) f
  have h_eq_val : ((1 + f * s)⁻¹ * s) = s / (1 + f * s) := by
    rw [div_eq_mul_inv, mul_comm]
  rw [← h_eq_val]
  exact h_log

/-- **Pointwise second-order Kelly derivative.**  `d²/df² log(1 + f·s)
    = −s² / (1 + f·s)²`.  Sign is non-positive — log is concave in `f`
    pointwise.  This gives strict concavity whenever `s ≠ 0`. -/
theorem kelly_log_hasDerivAt_second {f s : ℝ} (h : 0 < 1 + f * s) :
    HasDerivAt (fun f => s / (1 + f * s)) (-(s ^ 2) / (1 + f * s) ^ 2) f := by
  have h_ne : (1 + f * s) ≠ 0 := h.ne'
  have h_inner : HasDerivAt (fun f : ℝ => 1 + f * s) s f := by
    have h1 := ((hasDerivAt_id f).mul_const s).const_add (1:ℝ)
    convert h1 using 1 <;> simp [mul_comm]
  -- d/df [s / (1 + f*s)] = -s · (d/df (1 + f*s)) / (1 + f*s)^2 = -s^2 / (1+f*s)^2
  have h_div : HasDerivAt (fun f : ℝ => s / (1 + f * s))
      ((0 * (1 + f * s) - s * s) / (1 + f * s) ^ 2) f := by
    exact (hasDerivAt_const f s).div h_inner h_ne
  convert h_div using 1
  rw [show (0 * (1 + f * s) - s * s : ℝ) = -(s ^ 2) from by ring]

/-- **Pointwise second derivative is non-positive** ⇒ log is concave
    in `f`: the marginal `s / (1 + f·s)` is non-increasing along the
    Kelly objective's domain. -/
theorem kelly_log_second_deriv_nonpos {f s : ℝ} (h : 0 < 1 + f * s) :
    -(s ^ 2) / (1 + f * s) ^ 2 ≤ 0 := by
  have h_sq_pos : 0 < (1 + f * s) ^ 2 := by positivity
  apply div_nonpos_of_nonpos_of_nonneg
  · exact neg_nonpos_of_nonneg (sq_nonneg s)
  · exact h_sq_pos.le

/-- At zero stake the pointwise marginal payoff equals the realized
payoff `s`. This scalar identity has no positivity requirement and does
not assert that an expected marginal vanishes or identify an optimum. -/
theorem kelly_marginal_at_zero {s : ℝ} :
    s / (1 + 0 * s) = s := by
  rw [zero_mul, add_zero, div_one]


end TailOptionPricing
