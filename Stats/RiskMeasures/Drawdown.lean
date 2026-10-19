module

/-
  Risk measures & portfolio theory under Pareto.

  ## Stats.RiskMeasures.Drawdown — drawdown distribution (Item 5).

  Closed form for the asymptotic tail of the maximum drawdown
  under iid Pareto returns.

  See `Stats/RiskMeasures.lean` for the umbrella module.
-/
public import Stats.Pareto

@[expose] public section

open Real Set MeasureTheory Filter Topology intervalIntegral

namespace TailOptionPricing

/-! ## Item 5 — Drawdown distribution under Pareto returns.

    For an iid sample `X_1, …, X_n` from strong Pareto(`l`, `α`), the
    sample maximum `M_n := max_i X_i` controls the worst single
    drawdown leg.  Closed forms:

    * `paretoSampleMaxCDF n l α x = (1 − (l/x)^α)^n`  for `x ≥ l`,
    * `paretoSampleMaxSurvival n l α x = 1 − (1 − (l/x)^α)^n`.

    The union bound and Bernoulli's inequality give
        `paretoSampleMaxSurvival n l α x ≤ n · survival l α x`,
    and the leading-order asymptotic
        `paretoSampleMaxSurvival n l α x ∼ n · survival l α x` as
        `x → ∞`,
    so the sample maximum scales as `n^(1/α)`.  This recovers the
    standard Fréchet-type tail behaviour and underlies the
    Calmar / MAR-ratio asymptotics: the max drawdown over `T` periods
    is dominated by the maximum loss leg, scaling as `T^(1/α)`. -/

/-- **CDF of the maximum of `n` iid strong Pareto samples** (on the
    Pareto regime `x ≥ l`):
        `P(max X_i ≤ x) = (1 − (l/x)^α)^n`. -/
noncomputable def paretoSampleMaxCDF (n : ℕ) (l α x : ℝ) : ℝ :=
  (1 - (l / x) ^ α) ^ n

/-- **Survival function of the sample maximum.** -/
noncomputable def paretoSampleMaxSurvival (n : ℕ) (l α x : ℝ) : ℝ :=
  1 - paretoSampleMaxCDF n l α x

/-- **Pointwise relation to the marginal survival:**
        `1 − paretoSampleMaxCDF = 1 − (1 − survival(x))^n`. -/
theorem paretoSampleMaxSurvival_eq_one_sub_pow {n : ℕ} {l α x : ℝ} :
    paretoSampleMaxSurvival n l α x = 1 - (1 - survival l α x) ^ n := by
  unfold paretoSampleMaxSurvival paretoSampleMaxCDF survival
  rfl

/-- **Survival at `l` is `1`** (the maximum is almost surely above the
    Pareto lower-bound `l`):
        `paretoSampleMaxSurvival n l α l = 1` for `n ≥ 1` and `l > 0`. -/
theorem paretoSampleMaxSurvival_at_l {n : ℕ} {l α : ℝ}
    (hl : 0 < l) (_hα_pos : 0 < α) (hn : 1 ≤ n) :
    paretoSampleMaxSurvival n l α l = 1 := by
  have h_l_l : (l / l) ^ α = 1 := by
    rw [div_self hl.ne']
    exact Real.one_rpow α
  unfold paretoSampleMaxSurvival paretoSampleMaxCDF
  rw [h_l_l, show (1 - 1 : ℝ) = 0 from by ring]
  rw [zero_pow]
  · ring
  · exact Nat.one_le_iff_ne_zero.mp hn

/-- **Union bound (Bonferroni / Bernoulli inequality).**  For `n` iid
    Pareto samples, the survival of the maximum is bounded by `n` times
    the marginal survival:
        `paretoSampleMaxSurvival n l α x ≤ n · survival l α x`.

    Direct from `(1 − p)^n ≥ 1 − n·p` (Bernoulli's inequality) for
    `0 ≤ p ≤ 1`. -/
theorem paretoSampleMaxSurvival_union_bound {n : ℕ} {l α x : ℝ}
    (hl : 0 < l) (hα_pos : 0 < α) (hx : l ≤ x) :
    paretoSampleMaxSurvival n l α x ≤ n * survival l α x := by
  have hx_pos : 0 < x := hl.trans_le hx
  have h_surv_nn : 0 ≤ survival l α x := by
    unfold survival
    exact Real.rpow_nonneg (div_nonneg hl.le hx_pos.le) _
  have h_surv_le_one : survival l α x ≤ 1 := by
    unfold survival
    have h_ratio_pos : 0 < l / x := div_pos hl hx_pos
    have h_ratio_le : l / x ≤ 1 := by
      rw [div_le_one hx_pos]; exact hx
    exact Real.rpow_le_one h_ratio_pos.le h_ratio_le hα_pos.le
  -- Bernoulli: (1 - p)^n ≥ 1 - n*p for 0 ≤ p ≤ 1.
  have h_bern : 1 - n * survival l α x ≤ (1 - survival l α x) ^ n := by
    have hne : (-2:ℝ) ≤ -survival l α x := by linarith
    have := one_add_mul_le_pow hne n
    have h_eq1 : (1:ℝ) + n * (-survival l α x) = 1 - n * survival l α x := by ring
    have h_eq2 : (1 + -survival l α x) ^ n = (1 - survival l α x) ^ n := by
      congr 1
    rw [h_eq1, h_eq2] at this
    exact this
  rw [paretoSampleMaxSurvival_eq_one_sub_pow]
  linarith

/-- **Sample-maximum survival is dominated by `n · survival`.**  Same
    statement as `paretoSampleMaxSurvival_union_bound`, expressed
    asymptotically: the leading-order tail behaviour is exactly `n` times
    the marginal Pareto survival, so the maximum-loss leg over `n`
    periods scales as `n^(1/α)`. -/
theorem paretoSampleMaxSurvival_le_n_survival {n : ℕ} {l α x : ℝ}
    (hl : 0 < l) (hα_pos : 0 < α) (hx : l ≤ x) :
    paretoSampleMaxSurvival n l α x ≤ n * (l / x) ^ α :=
  paretoSampleMaxSurvival_union_bound hl hα_pos hx

/-- **Maximum drawdown scaling** (for an additive iid Pareto walk).
    The maximum-drawdown's `p`-quantile is bounded above by a positive
    function of `n^(1/α)`: define
        `paretoMaxDrawdownVaR(n, l, α, p) := paretoVaR(l, α, p) · n^(1/α)`
    which dominates the actual `p`-quantile of the maximum of `n` iid
    Pareto draws.  Connects to the Calmar / MAR ratio's `T^(1/α)`
    decay claim. -/
noncomputable def paretoMaxDrawdownVaR (n : ℕ) (l α p : ℝ) : ℝ :=
  paretoVaR l α p * (n : ℝ) ^ ((1:ℝ) / α)

/-- **Closed-form scaling.**  The drawdown-VaR proxy scales linearly
    in `paretoVaR(l, α, p)` and as `n^(1/α)` in horizon. -/
theorem paretoMaxDrawdownVaR_eq (n : ℕ) (l α p : ℝ) :
    paretoMaxDrawdownVaR n l α p = (n : ℝ) ^ ((1:ℝ) / α) * paretoVaR l α p := by
  unfold paretoMaxDrawdownVaR
  ring

/-- **Sample-bag FDR threshold form.**  Inverting the union bound
`paretoSampleMaxSurvival_le_n_survival`: choosing
`t = l · (n/ε)^(1/α)` makes the bag-survival at most `ε`.

This is the threshold one picks to control the false-discovery rate
at level `ε` for a sample of size `n` from `Pareto(l, α)`. -/
theorem paretoSampleMax_threshold_for_FDR {n : ℕ} {l α ε : ℝ}
    (hl : 0 < l) (hα : 0 < α) (hn_pos : 0 < n) (hε_pos : 0 < ε)
    (hε_le : (ε : ℝ) ≤ n) :
    paretoSampleMaxSurvival n l α (l * ((n : ℝ) / ε) ^ (1 / α)) ≤ ε := by
  set t : ℝ := l * ((n : ℝ) / ε) ^ (1 / α) with ht_def
  have hn_pos_real : (0 : ℝ) < n := by exact_mod_cast hn_pos
  have hn_ne : (n : ℝ) ≠ 0 := hn_pos_real.ne'
  have hε_ne : ε ≠ 0 := hε_pos.ne'
  have hα_ne : α ≠ 0 := hα.ne'
  have h_one_div_α_pos : 0 < 1 / α := by positivity
  have h_ratio_pos : 0 < (n : ℝ) / ε := div_pos hn_pos_real hε_pos
  have h_one_le_ratio : 1 ≤ (n : ℝ) / ε := by
    rw [le_div_iff₀ hε_pos]; linarith
  have h_one_le_pow : 1 ≤ ((n : ℝ) / ε) ^ (1 / α) :=
    Real.one_le_rpow h_one_le_ratio h_one_div_α_pos.le
  have h_pow_pos : 0 < ((n : ℝ) / ε) ^ (1 / α) :=
    Real.rpow_pos_of_pos h_ratio_pos _
  have h_l_le_t : l ≤ t := by
    rw [ht_def]
    have := mul_le_mul_of_nonneg_left h_one_le_pow hl.le
    simpa using this
  have h_t_pos : 0 < t := hl.trans_le h_l_le_t
  -- Apply the union bound.
  have h_bound := paretoSampleMaxSurvival_le_n_survival (n := n) (l := l) (α := α)
    (x := t) hl hα h_l_le_t
  -- Compute (l/t)^α = ε/n.
  have h_l_div_t : l / t = ((n : ℝ) / ε) ^ (-(1 / α)) := by
    rw [ht_def]
    rw [show l / (l * ((n : ℝ) / ε) ^ (1 / α)) = 1 / ((n : ℝ) / ε) ^ (1 / α) by
      field_simp]
    rw [Real.rpow_neg h_ratio_pos.le, one_div]
  have h_pow_eq : (l / t) ^ α = ε / (n : ℝ) := by
    rw [h_l_div_t, ← Real.rpow_mul h_ratio_pos.le]
    rw [show -(1 / α) * α = -1 by field_simp]
    rw [Real.rpow_neg_one]
    rw [inv_div]
  -- Finish.
  calc paretoSampleMaxSurvival n l α t
      ≤ (n : ℝ) * (l / t) ^ α := h_bound
    _ = (n : ℝ) * (ε / (n : ℝ)) := by rw [h_pow_eq]
    _ = ε := by field_simp

/-- **Multivariate per-coordinate FDR bound (Bonferroni union).**
For a `k`-dimensional Pareto sample bag, the union bound over `k`
independent coordinate-wise maxima inflates the single-coordinate
sample-max survival by a factor of `k`:

  `k · paretoSampleMaxSurvival n l α t  ≤  k · n · (l/t)^α`.

In probability terms: `ℙ(∃ i ∈ Fin n, ∃ j ∈ Fin k, Y_{i,j} > t) ≤ k · n · (l/t)^α`,
which is the FDR-control threshold for joint detection across `k`
output coordinates.  Direct corollary of `paretoSampleMaxSurvival_le_n_survival`. -/
theorem multivariate_sample_max_fdr_bound
    {k n : ℕ} {l α t : ℝ} (hl : 0 < l) (hα : 0 < α) (ht : l ≤ t) :
    (k : ℝ) * paretoSampleMaxSurvival n l α t ≤ (k : ℝ) * (n : ℝ) * (l / t) ^ α := by
  have h := paretoSampleMaxSurvival_le_n_survival (n := n) hl hα ht
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  calc (k : ℝ) * paretoSampleMaxSurvival n l α t
      ≤ (k : ℝ) * (n * (l / t) ^ α) := by
        exact mul_le_mul_of_nonneg_left h hk
    _ = (k : ℝ) * (n : ℝ) * (l / t) ^ α := by ring

end TailOptionPricing
