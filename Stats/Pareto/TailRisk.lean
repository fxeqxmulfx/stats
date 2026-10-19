module

/-
  Strong-Pareto core: tail-risk measures from
    Taleb–Yarckin–Mann–Delic–Spitznagel,
    "Tail Option Pricing Under Power Laws", arXiv:1908.02347v3 (March 2023).

  ## Stats.Pareto.TailRisk — VaR, CVaR, tail expectation.

  Closed forms for tail-risk measures under the strong-Pareto
  density: `paretoTailExpectation`, `paretoVaR`, `paretoCVaR`,
  and their interrelations with `callPrice`.

  See `Stats/Pareto.lean` for the umbrella module.
-/
public import Stats.Pareto.Basic

@[expose] public section

open Real Set MeasureTheory Filter Topology intervalIntegral

namespace TailOptionPricing

/-! ## Tail-risk measures: VaR, CVaR, tail expectation under strong Pareto.

    Closed forms for `S ~ strong Pareto(l, α)`:
    `VaR_p` (the `p`-quantile), `CVaR_p = E[S | S > VaR_p]` (Expected
    Shortfall), and the tail expectation `E[S; S > K]`.  The tail
    expectation has a clean bridge to option pricing:
        paretoTailExpectation(K) = α · callPrice(K). -/

/-- **Tail expectation** of `S ~ strong Pareto(l, α)` above the threshold `K`:
        E[S; S > K] := ∫_{Ioi K} s · α·l^α / s^(α+1) ds. -/
noncomputable def paretoTailExpectation (l α K : ℝ) : ℝ :=
  ∫ s in Ioi K, s * (α * l ^ α / s ^ (α + 1))

/-- **Closed form of the tail expectation:** for `l ≤ K` and `α > 1`,
        E[S; S > K] = α · l^α · K^(1−α) / (α−1). -/
theorem paretoTailExpectation_eq {l α K : ℝ} (hα : 1 < α) (hl : 0 < l)
    (hK : l ≤ K) :
    paretoTailExpectation l α K = α * l ^ α * K ^ (1 - α) / (α - 1) := by
  have hK_pos : 0 < K := hl.trans_le hK
  have hα_neg : -α < -1 := by linarith
  have hα1_ne : (α - 1 : ℝ) ≠ 0 := sub_ne_zero.mpr hα.ne'
  have h_pt : ∀ s ∈ Ioi K, s * (α * l ^ α / s ^ (α + 1))
      = α * l ^ α * s ^ (-α) := by
    intro s hs
    have hs_pos : 0 < s := hK_pos.trans hs
    have hs_ne : s ≠ 0 := hs_pos.ne'
    have hs_α_pos : 0 < s ^ α := Real.rpow_pos_of_pos hs_pos _
    have hs_α_ne : s ^ α ≠ 0 := hs_α_pos.ne'
    rw [show s ^ (α + 1) = s ^ α * s from by
          rw [Real.rpow_add hs_pos, Real.rpow_one],
        Real.rpow_neg hs_pos.le]
    field_simp
  unfold paretoTailExpectation
  rw [setIntegral_congr_fun measurableSet_Ioi h_pt,
      MeasureTheory.integral_const_mul,
      integral_Ioi_rpow_of_lt hα_neg hK_pos]
  rw [show (-α + 1 : ℝ) = -(α - 1) from by ring, neg_div_neg_eq,
      show (1 - α : ℝ) = -(α - 1) from by ring]
  ring

/-- **Bridge to option pricing:** the tail expectation is `α` times the call
    price (both have `l^α · K^(1−α)/(α−1)` decay; only the leading factor
    differs). -/
theorem paretoTailExpectation_eq_alpha_callPrice {l α K : ℝ}
    (hα : 1 < α) (hl : 0 < l) (hK : l ≤ K) :
    paretoTailExpectation l α K = α * callPrice l α K := by
  rw [paretoTailExpectation_eq hα hl hK, callPrice_eq hα hl hK]
  ring

/-- **Conditional expectation in the tail:** for `l ≤ K`,
        E[S | S > K] = paretoTailExpectation(K) / survival(K) = α·K / (α−1). -/
theorem paretoTailExpectation_div_survival {l α K : ℝ}
    (hα : 1 < α) (hl : 0 < l) (hK : l ≤ K) :
    paretoTailExpectation l α K / survival l α K = α * K / (α - 1) := by
  have hK_pos : 0 < K := hl.trans_le hK
  have hα1_ne : (α - 1 : ℝ) ≠ 0 := sub_ne_zero.mpr hα.ne'
  have hl_pow_pos : 0 < l ^ α := Real.rpow_pos_of_pos hl _
  have hK_pow_pos : 0 < K ^ α := Real.rpow_pos_of_pos hK_pos _
  have h_pow : K ^ (1 - α) * K ^ α = K := by
    rw [← Real.rpow_add hK_pos, show (1 - α + α : ℝ) = 1 from by ring,
        Real.rpow_one]
  rw [paretoTailExpectation_eq hα hl hK]
  unfold survival
  rw [Real.div_rpow hl.le hK_pos.le]
  rw [show α * l ^ α * K ^ (1 - α) / (α - 1) / (l ^ α / K ^ α)
        = α * (K ^ (1 - α) * K ^ α) / (α - 1) from by
    have := hl_pow_pos.ne'
    have := hK_pow_pos.ne'
    field_simp]
  rw [h_pow]

/-- **Value-at-Risk** at level `p` for `S ~ strong Pareto(l, α)`:
        VaR_p := l · (1 − p)^(−1/α),
    the unique threshold such that `ℙ(S > VaR_p) = 1 − p`. -/
noncomputable def paretoVaR (l α p : ℝ) : ℝ := l * (1 - p) ^ (-(1 / α))

/-- **Quantile equation:** `ℙ(S > VaR_p) = 1 − p`. -/
theorem survival_paretoVaR {l α p : ℝ} (hα_pos : 0 < α) (hl : 0 < l)
    (hp_lt : p < 1) :
    survival l α (paretoVaR l α p) = 1 - p := by
  have h1mp_pos : 0 < 1 - p := by linarith
  have hα_ne : (α : ℝ) ≠ 0 := hα_pos.ne'
  have hl_ne : (l : ℝ) ≠ 0 := hl.ne'
  have hpow_pos : 0 < (1 - p) ^ (1 / α) := Real.rpow_pos_of_pos h1mp_pos _
  have hpow_ne : (1 - p) ^ (1 / α) ≠ 0 := hpow_pos.ne'
  unfold survival paretoVaR
  rw [Real.rpow_neg h1mp_pos.le]
  rw [show l / (l * ((1 - p) ^ (1 / α))⁻¹) = (1 - p) ^ (1 / α) from by
    field_simp]
  rw [← Real.rpow_mul h1mp_pos.le]
  rw [show (1 / α * α : ℝ) = 1 from by field_simp]
  exact Real.rpow_one _

/-- `paretoVaR ≥ l`: the `p`-quantile lies in the strong-Pareto regime,
    so `paretoTailExpectation_eq` and friends apply at `K = paretoVaR`. -/
theorem paretoVaR_ge_l {l α p : ℝ} (hα_pos : 0 < α) (hl : 0 ≤ l)
    (hp : 0 ≤ p) (hp_lt : p < 1) :
    l ≤ paretoVaR l α p := by
  have h1mp_pos : 0 < 1 - p := by linarith
  have h1mp_le : 1 - p ≤ 1 := by linarith
  have h_rpow_pos : 0 < (1 - p) ^ (1 / α) := Real.rpow_pos_of_pos h1mp_pos _
  have h_rpow_le : (1 - p) ^ (1 / α) ≤ 1 :=
    Real.rpow_le_one h1mp_pos.le h1mp_le (one_div_nonneg.mpr hα_pos.le)
  have h_inv_ge_one : 1 ≤ ((1 - p) ^ (1 / α))⁻¹ :=
    (one_le_inv₀ h_rpow_pos).mpr h_rpow_le
  unfold paretoVaR
  rw [Real.rpow_neg h1mp_pos.le]
  calc l = l * 1 := (mul_one l).symm
    _ ≤ l * ((1 - p) ^ (1 / α))⁻¹ := mul_le_mul_of_nonneg_left h_inv_ge_one hl

/-- **Conditional Value-at-Risk** (Expected Shortfall) at level `p` for
    `S ~ strong Pareto(l, α)`:
        CVaR_p := α/(α−1) · VaR_p. -/
noncomputable def paretoCVaR (l α p : ℝ) : ℝ :=
  α / (α - 1) * paretoVaR l α p

/-- **CVaR justification:** `paretoCVaR_p = E[S; S > VaR_p] / ℙ(S > VaR_p)`,
    i.e. it is the conditional tail expectation `E[S | S > VaR_p]`. -/
theorem paretoCVaR_eq_conditional {l α p : ℝ}
    (hα : 1 < α) (hl : 0 < l) (hp : 0 ≤ p) (hp_lt : p < 1) :
    paretoTailExpectation l α (paretoVaR l α p) / (1 - p) = paretoCVaR l α p := by
  have hα_pos : 0 < α := by linarith
  have h_VaR_ge_l : l ≤ paretoVaR l α p :=
    paretoVaR_ge_l hα_pos hl.le hp hp_lt
  have h_surv : survival l α (paretoVaR l α p) = 1 - p :=
    survival_paretoVaR hα_pos hl hp_lt
  have h := paretoTailExpectation_div_survival hα hl h_VaR_ge_l
  rw [h_surv] at h
  rw [h]
  unfold paretoCVaR
  ring


end TailOptionPricing
