module

/-
  Scalar density identities, elementary variance bounds and the strong-
  Pareto moment threshold in Taleb, Bar-Yam and Cirillo,
  arXiv:2007.16096v1. Actual sample-variance and estimation-error results
  are in EmpiricalSurvival and FairCoin, rather than these scalar formulas.
-/
public import Stats.Pareto.Mispricing
public import Stats.RiskMeasures.Moments

@[expose] public section

open Real Set Filter Topology MeasureTheory

namespace TailOptionPricing

/-! ## Exponential growth → Pareto density (paper "Uncertainty goes
    one way").

    If `r ~ Exponential(λ)` with density `f_r(r) = λ·exp(−λr)` on
    `[0, ∞)`, then `X := X₀·exp(r·t)` has density
        `f_X(x) = (λ/(t·x)) · (X₀/x)^(λ/t)`
    for `x ≥ X₀`, which is exactly `paretoDensity X₀ (λ/t) x` — strong
    Pareto with scale `X₀` and tail index `λ/t`. -/

/-- **Density-after-exponential-growth identity.**  Pointwise
    identity `λ/(t·x) · (X₀/x)^(λ/t) = paretoDensity X₀ (λ/t) x`,
    matching the candidate change-of-variables expression for
    `X = X₀·exp(r·t)` with `r ~ Exp(λ)`. No law is asserted here. -/
theorem exp_growth_density_eq_pareto {X₀ t lam x : ℝ}
    (hX₀ : 0 < X₀) (ht : 0 < t) (hlam : 0 < lam) (hx : 0 < x) :
    lam / (t * x) * (X₀ / x) ^ (lam / t)
      = paretoDensity X₀ (lam / t) x := by
  unfold paretoDensity
  have ht_ne : t ≠ 0 := ht.ne'
  have hx_ne : x ≠ 0 := hx.ne'
  have h_X₀_pow_pos : 0 < X₀ ^ (lam / t) := Real.rpow_pos_of_pos hX₀ _
  have h_x_pow_pos : 0 < x ^ (lam / t) := Real.rpow_pos_of_pos hx _
  have hx_pow_α1_pos : 0 < x ^ (lam / t + 1) := Real.rpow_pos_of_pos hx _
  have hx_pow_α1_ne : x ^ (lam / t + 1) ≠ 0 := hx_pow_α1_pos.ne'
  have h_x_pow_split : x ^ (lam / t + 1) = x * x ^ (lam / t) := by
    rw [show (lam/t + 1 : ℝ) = 1 + lam/t from by ring,
        Real.rpow_add hx, Real.rpow_one]
  rw [Real.div_rpow hX₀.le hx.le, h_x_pow_split]
  field_simp

/-- **Tail-index/variance relation (paper claim "α direct function
    of variance of r").**  For `r ~ Exp(λ)` (variance `1/λ²`), the
    Pareto tail index `α = λ/t` satisfies
        `α · t · √Var(r) = 1`,
    i.e., `α = 1 / (t · √Var(r))`.  Higher Var(r) ⇒ smaller α ⇒
    fatter tail of X. -/
theorem exp_growth_tail_index_variance_relation {t lam : ℝ}
    (ht : 0 < t) (hlam : 0 < lam) :
    (lam / t) * t * Real.sqrt (1 / lam ^ 2) = 1 := by
  have hlam_ne : lam ≠ 0 := hlam.ne'
  have ht_ne : t ≠ 0 := ht.ne'
  have h_sqrt : Real.sqrt (1 / lam ^ 2) = 1 / lam := by
    rw [one_div, Real.sqrt_inv, Real.sqrt_sq hlam.le, ← one_div]
  rw [h_sqrt]
  field_simp

/-! ## Scalar inequalities used for the empirical-survival variance.

    The source actually prints `o(1/n)` (line 235), which the actual
    fair-coin estimator refutes in both MSE and RMSE. The probability-law
    bridge and corrected rates are in EmpiricalSurvival and FairCoin. -/

/-- The scalar polynomial bound holds for every real `p`. For event
probabilities it bounds the actual Bernoulli variance; that law bridge is
proved separately rather than supplied by this inequality. -/
theorem bernoulli_variance_bound {p : ℝ} :
    p * (1 - p) ≤ 1 / 4 := by
  nlinarith [sq_nonneg (p - 1/2)]

/-- Scalar upper bound `p(1-p)/n ≤ 1/(4n)`, for any real `p` and
positive sample size. The actual estimator variance is handled in
`empiricalSurvival_variance_bound`; this lemma alone is algebraic. -/
theorem empirical_survival_variance_bound {p : ℝ} {n : ℕ}
    (hn_pos : 0 < n) :
    p * (1 - p) / n ≤ 1 / (4 * n) := by
  have hn_real_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn_pos
  have h_bound := bernoulli_variance_bound (p := p)
  have h_four_n_pos : (0 : ℝ) < 4 * n := by positivity
  rw [div_le_iff₀ hn_real_pos, div_mul_eq_mul_div, le_div_iff₀ h_four_n_pos]
  nlinarith

/-- Scalar square-root bound for the variance expression. The actual
root-mean-square error is connected to it in EmpiricalSurvival. -/
theorem empirical_survival_std_bound {p : ℝ} {n : ℕ}
    (hn_pos : 0 < n) :
    Real.sqrt (p * (1 - p) / n) ≤ 1 / (2 * Real.sqrt n) := by
  have hn_real_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn_pos
  have h_sqrt_n_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn_real_pos
  have h_bound := empirical_survival_variance_bound (p := p) hn_pos
  -- √(p(1-p)/n) ≤ √(1/(4n)) = 1/(2√n).
  have h_sqrt_le : Real.sqrt (p * (1 - p) / n) ≤ Real.sqrt (1 / (4 * n)) :=
    Real.sqrt_le_sqrt h_bound
  -- √(1/(4n)) = 1/(2√n).
  have h_sqrt_simp : Real.sqrt (1 / (4 * (n : ℝ))) = 1 / (2 * Real.sqrt n) := by
    have h_pow : (4 * (n : ℝ)) = (2 * Real.sqrt n) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hn_real_pos.le]
      ring
    rw [h_pow]
    rw [show (1 : ℝ) / (2 * Real.sqrt n) ^ 2 = (1 / (2 * Real.sqrt n)) ^ 2 from by
          rw [div_pow, one_pow]]
    exact Real.sqrt_sq (by positivity)
  rw [h_sqrt_simp] at h_sqrt_le
  exact h_sqrt_le

/-! ## Pareto mean diverges at `α ≤ 1` (paper Remark 3).

    "Fat-tailed random variables with tail exponent α ≤ 1 are simply
    not forecastable.  They do not obey the LLN, as their theoretical
    mean is not defined."  Formal version: the Pareto first-moment
    integrand is not integrable on `(l, ∞)` whenever `α ≤ 1`. -/

/-- **Remark 3 (paper):** Pareto with tail index `α ≤ 1` has no
    finite first moment — the moment integrand
    `paretoMomentIntegrand l α 1` is *not* integrable on `(l, ∞)`.
    Direct corollary of `paretoMomentIntegrand_integrableOn_iff` at
    `k = 1`. An iid-sample/LLN statement needs a separate proof. -/
theorem paretoMean_not_integrable_when_alpha_le_one {l α : ℝ}
    (hα_pos : 0 < α) (hα_le : α ≤ 1) (hl : 0 < l) :
    ¬ IntegrableOn (paretoMomentIntegrand l α 1) (Ioi l) volume := by
  intro h_int
  have h := (paretoMomentIntegrand_integrableOn_iff hl hα_pos).mp h_int
  linarith

/-- **Strong-Pareto boundary case** at `α = 1`: the first-moment
    integrand is nonintegrable. This does not settle the boundary for
    a general regularly varying tail with a nonconstant slow factor. -/
theorem paretoMean_not_integrable_at_alpha_one {l : ℝ} (hl : 0 < l) :
    ¬ IntegrableOn (paretoMomentIntegrand l 1 1) (Ioi l) volume :=
  paretoMean_not_integrable_when_alpha_le_one (by norm_num) (le_refl _) hl

end TailOptionPricing
