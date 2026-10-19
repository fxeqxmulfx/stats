module

/-
  Candidate maximum-tail and drawdown-scale expressions under Pareto.

  The theorems prove polynomial union bounds and threshold substitutions
  for explicit scalar formulas. This module does not construct an iid
  sample maximum, an additive walk, a path drawdown, a quantile law or a
  false-discovery procedure. Those probability interpretations require
  separate law and model bridges.
-/
public import Stats.Pareto

@[expose] public section

open Real Set MeasureTheory Filter Topology intervalIntegral

namespace TailOptionPricing

/-! ## Item 5 — Candidate Pareto maximum expressions.

    For an iid sample `X_1, …, X_n` from strong Pareto(`l`, `α`), the
    sample maximum `M_n := max_i X_i` controls the worst single
    drawdown leg.  Closed forms:

    * `paretoSampleMaxCDF n l α x = (1 − (l/x)^α)^n`  for `x ≥ l`,
    * `paretoSampleMaxSurvival n l α x = 1 − (1 − (l/x)^α)^n`.

    The polynomial analog of the union bound gives
        `paretoSampleMaxSurvival n l α x ≤ n · survival l α x`,
    on positive scale/index and `x ≥ l`. The code below establishes
    that inequality and substitutes a threshold. It does not prove
    an asymptotic equivalence, an actual maximum law or a path-drawdown
    scaling law. A maximum sample value and an additive walk's maximum
    drawdown are different random variables. -/

/-- Candidate maximum-CDF expression `(1-(l/x)^α)^n`. A probability
    interpretation requires valid positive parameters, the supported
    domain and an actual iid maximum-law bridge. -/
noncomputable def paretoSampleMaxCDF (n : ℕ) (l α x : ℝ) : ℝ :=
  (1 - (l / x) ^ α) ^ n

/-- Candidate maximum-survival expression, complementary to the
    candidate CDF. It is not a supported survival law on all reals. -/
noncomputable def paretoSampleMaxSurvival (n : ℕ) (l α x : ℝ) : ℝ :=
  1 - paretoSampleMaxCDF n l α x

/-- **Pointwise relation to the marginal survival:**
        `1 − paretoSampleMaxCDF = 1 − (1 − survival(x))^n`. -/
theorem paretoSampleMaxSurvival_eq_one_sub_pow {n : ℕ} {l α x : ℝ} :
    paretoSampleMaxSurvival n l α x = 1 - (1 - survival l α x) ^ n := by
  unfold paretoSampleMaxSurvival paretoSampleMaxCDF survival
  rfl

/-- Boundary identity of the candidate maximum-survival expression for
every real `α`, positive scale and nonempty sample. Interpreting it as
an actual Pareto-maximum probability additionally needs a positive index
and an iid-law bridge; those facts are not assumed or proved here. -/
theorem paretoSampleMaxSurvival_at_l {n : ℕ} {l α : ℝ}
    (hl : 0 < l) (hn : 1 ≤ n) :
    paretoSampleMaxSurvival n l α l = 1 := by
  have h_l_l : (l / l) ^ α = 1 := by
    rw [div_self hl.ne']
    exact Real.one_rpow α
  unfold paretoSampleMaxSurvival paretoSampleMaxCDF
  rw [h_l_l, show (1 - 1 : ℝ) = 0 from by ring]
  rw [zero_pow]
  · ring
  · exact Nat.one_le_iff_ne_zero.mp hn

/-- Polynomial union-bound inequality for the candidate maximum tail:
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

/-- The same pointwise candidate-tail bound with `survival` expanded.
    It does not assert asymptotic equivalence or maximum-loss scaling. -/
theorem paretoSampleMaxSurvival_le_n_survival {n : ℕ} {l α x : ℝ}
    (hl : 0 < l) (hα_pos : 0 < α) (hx : l ≤ x) :
    paretoSampleMaxSurvival n l α x ≤ n * (l / x) ^ α :=
  paretoSampleMaxSurvival_union_bound hl hα_pos hx

/-- Drawdown-VaR proxy `paretoVaR(l,α,p)*n^(1/α)`. No path drawdown
    or quantile is constructed, and no comparison with an actual
    drawdown or maximum quantile is proved here. -/
noncomputable def paretoMaxDrawdownVaR (n : ℕ) (l α p : ℝ) : ℝ :=
  paretoVaR l α p * (n : ℝ) ^ ((1:ℝ) / α)

/-- **Closed-form scaling.**  The drawdown-VaR proxy scales linearly
    in `paretoVaR(l, α, p)` and as `n^(1/α)` in horizon. -/
theorem paretoMaxDrawdownVaR_eq (n : ℕ) (l α p : ℝ) :
    paretoMaxDrawdownVaR n l α p = (n : ℝ) ^ ((1:ℝ) / α) * paretoVaR l α p := by
  unfold paretoMaxDrawdownVaR
  ring

/-- Threshold substitution for the candidate-tail bound. Inverting
`paretoSampleMaxSurvival_le_n_survival`: choosing
`t = l · (n/ε)^(1/α)` makes the bag-survival at most `ε`.

An actual exceedance interpretation needs a maximum-law bridge. A
false-discovery rate additionally needs a testing procedure, null model
and the expected false-discovery proportion; none appears here. -/
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

/-- Scalar multiple of the candidate-tail bound, motivated by a
Bonferroni union estimate:
For a `k`-dimensional Pareto sample bag, the union bound over `k`
independent coordinate-wise maxima inflates the single-coordinate
sample-max survival by a factor of `k`:

  `k · paretoSampleMaxSurvival n l α t  ≤  k · n · (l/t)^α`.

In probability terms: `ℙ(∃ i ∈ Fin n, ∃ j ∈ Fin k, Y_{i,j} > t) ≤ k · n · (l/t)^α`,
This is a deterministic inequality. No joint coordinate law or FDR
procedure is constructed. The historical declaration name is retained. -/
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
