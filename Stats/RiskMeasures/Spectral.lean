/-
  Risk measures & portfolio theory under Pareto.

  ## Stats.RiskMeasures.Spectral — spectral risk measures (Item 2).

  Parametric family `M_φ := ∫_0^1 φ(p)·VaR_p dp`, with CVaR at
  confidence `t` recovered by `φ_t(p) := (1−t)⁻¹ · 1_{[t,1]}(p)`.
  Closed forms under Pareto for several `φ` families.

  See `Stats/RiskMeasures.lean` for the umbrella module.
-/
import Stats.RiskMeasures.CVaR

open Real Set MeasureTheory Filter Topology intervalIntegral

namespace TailOptionPricing

/-! ## Item 2 — Spectral risk measures.

    A spectral risk measure with weight `φ : ℝ → ℝ` is
        M_φ(l, α) := ∫_0^1 φ(p) · VaR_p dp.
    Under strong Pareto `VaR_p = l · (1 − p)^(−1/α)`, the substitution
    `u = 1 − p` reduces every closed-form weight choice to an
    `rpow`-integral.  We formalise three standard choices:

    1. **Constant weight `φ ≡ 1`** — recovers the unconditional Pareto
       mean `α · l / (α − 1)`.
    2. **CVaR weight `φ_t(p) := (1−t)⁻¹ · 1_{[t,1]}(p)`** — recovers
       `paretoCVaR l α t`.  This realises the standard recovery
       statement that CVaR is a spectral measure.
    3. **Power weight `φ(p) := (1 − p)^β`** — gives a one-parameter
       family `M_β = l · α / (α(β + 1) − 1)` interpolating between
       the mean (`β = 0`) and CVaR-like measures (`β → −1`).

    Positive homogeneity in `l` is a consequence of `paretoVaR_scale`. -/

/-- **Spectral risk measure** under strong Pareto `VaR`:
        M_φ(l, α) := ∫_0^1 φ(p) · VaR_p dp.
    Defined for arbitrary `φ`; closed forms below cover several
    standard weight families. -/
noncomputable def spectralRiskMeasure (φ : ℝ → ℝ) (l α : ℝ) : ℝ :=
  ∫ p in (0:ℝ)..1, φ p * paretoVaR l α p

/-- **Pareto VaR integral via substitution `u = 1 − p`.**  For `α > 1`
    and any endpoints `a, b`, the integral of `paretoVaR` on
    `[a, b]` reduces to the closed-form `rpow` integral on
    `[1 − b, 1 − a]`. -/
private theorem integral_paretoVaR_eq {l α a b : ℝ} (hα : 1 < α) :
    ∫ p in a..b, paretoVaR l α p
      = l * (((1 - a) ^ (1 - 1 / α) - (1 - b) ^ (1 - 1 / α)) /
              (1 - 1 / α)) := by
  have hα_pos : 0 < α := by linarith
  have h_inv_α_lt_one : 1 / α < 1 := by
    rw [div_lt_one hα_pos]; exact hα
  have h_neg_inv_α_gt_neg_one : (-1 : ℝ) < -(1 / α) := by linarith
  have h_exp_eq : (-(1 / α) + 1 : ℝ) = 1 - 1 / α := by ring
  have h_step1 : ∫ p in a..b, paretoVaR l α p
      = ∫ p in a..b, l * (1 - p) ^ (-(1 / α)) := rfl
  have h_step2 : ∫ p in a..b, l * (1 - p) ^ (-(1 / α))
      = l * ∫ p in a..b, (1 - p) ^ (-(1 / α)) :=
    intervalIntegral.integral_const_mul l _
  have h_step3 : ∫ p in a..b, (1 - p) ^ (-(1 / α))
      = ∫ u in (1 - b)..(1 - a), u ^ (-(1 / α)) :=
    intervalIntegral.integral_comp_sub_left (fun u => u ^ (-(1/α))) 1
  have h_step4 : ∫ u in (1 - b)..(1 - a), u ^ (-(1 / α))
      = ((1 - a) ^ (-(1 / α) + 1) - (1 - b) ^ (-(1 / α) + 1)) /
          (-(1 / α) + 1) :=
    integral_rpow (Or.inl h_neg_inv_α_gt_neg_one)
  rw [h_step1, h_step2, h_step3, h_step4, h_exp_eq]

/-- **Spectral risk measure with constant weight `φ ≡ 1` equals the
    Pareto mean:**  `∫_0^1 VaR_p dp = α · l / (α − 1)`.

    Standard identity: the integral of a non-negative random variable's
    quantile function over `(0, 1)` equals its expectation. -/
theorem spectralRiskMeasure_const_one {l α : ℝ}
    (hα : 1 < α) :
    spectralRiskMeasure (fun _ => 1) l α = α * l / (α - 1) := by
  have hα_pos : 0 < α := by linarith
  have hα1_pos : 0 < α - 1 := by linarith
  have hα_ne : (α : ℝ) ≠ 0 := hα_pos.ne'
  have hα1_ne : (α - 1 : ℝ) ≠ 0 := hα1_pos.ne'
  have h_inv_α_lt_one : 1 / α < 1 := by
    rw [div_lt_one hα_pos]; exact hα
  have h1_minus_inv_pos : 0 < 1 - 1/α := by linarith
  have h1_minus_inv_ne : (1 - 1 / α : ℝ) ≠ 0 := h1_minus_inv_pos.ne'
  unfold spectralRiskMeasure
  have h_simp : ∀ p, (1 : ℝ) * paretoVaR l α p = paretoVaR l α p := by
    intro p; ring
  simp_rw [h_simp]
  rw [integral_paretoVaR_eq (a := 0) (b := 1) hα]
  rw [show ((1:ℝ) - 0) = 1 from by ring,
      show ((1:ℝ) - 1) = 0 from by ring,
      Real.one_rpow, Real.zero_rpow h1_minus_inv_ne, sub_zero]
  field_simp

/-- **Spectral CVaR recovery.**  With weight
    `φ_t(p) := (1−t)⁻¹ · 1_{[t,1]}(p)` (encoded here as the scaled
    integral over `[t, 1]`), the spectral risk measure reduces to
    `paretoCVaR l α t`.  Realises the standard recovery statement
    that CVaR is a spectral measure. -/
theorem spectralRiskMeasure_cvar_recovery {l α t : ℝ}
    (hα : 1 < α) (ht_lt : t < 1) :
    (1 - t)⁻¹ * (∫ p in t..1, paretoVaR l α p) = paretoCVaR l α t := by
  have hα_pos : 0 < α := by linarith
  have hα1_pos : 0 < α - 1 := by linarith
  have hα1_ne : (α - 1 : ℝ) ≠ 0 := hα1_pos.ne'
  have hα_ne : (α : ℝ) ≠ 0 := hα_pos.ne'
  have h_inv_α_lt_one : 1 / α < 1 := by
    rw [div_lt_one hα_pos]; exact hα
  have h1_minus_inv_pos : 0 < 1 - 1/α := by linarith
  have h1_minus_inv_ne : (1 - 1 / α : ℝ) ≠ 0 := h1_minus_inv_pos.ne'
  have h1mt_pos : 0 < 1 - t := by linarith
  have h1mt_ne : (1 - t : ℝ) ≠ 0 := h1mt_pos.ne'
  rw [integral_paretoVaR_eq (a := t) (b := 1) hα]
  rw [show ((1:ℝ) - 1) = 0 from by ring,
      Real.zero_rpow h1_minus_inv_ne, sub_zero]
  -- Goal: (1-t)⁻¹ * (l * ((1-t)^{1-1/α} / (1-1/α))) = paretoCVaR l α t
  unfold paretoCVaR paretoVaR
  -- paretoCVaR l α t = α/(α-1) * (l * (1-t)^(-(1/α)))
  -- We want to show LHS = α/(α-1) * l * (1-t)^(-(1/α))
  -- (1-t)⁻¹ * (1-t)^{1-1/α} = (1-t)^{1 - 1/α - 1} = (1-t)^{-1/α}
  have h_pow_combine :
      (1 - t)⁻¹ * (1 - t) ^ (1 - 1 / α) = (1 - t) ^ (-(1 / α)) := by
    rw [show ((1 - t)⁻¹ : ℝ) = (1 - t) ^ (-(1:ℝ)) from by
      rw [Real.rpow_neg h1mt_pos.le, Real.rpow_one]]
    rw [← Real.rpow_add h1mt_pos]
    congr 1; ring
  -- factor of (1 - 1/α)⁻¹ vs α/(α-1): identity
  have h_factor_eq : (1 - 1 / α)⁻¹ = α / (α - 1) := by
    rw [show (1 - 1 / α : ℝ) = (α - 1) / α from by field_simp]
    rw [inv_div]
  calc (1 - t)⁻¹ * (l * ((1 - t) ^ (1 - 1 / α) / (1 - 1 / α)))
      = ((1 - t)⁻¹ * (1 - t) ^ (1 - 1 / α)) * (l * (1 - 1 / α)⁻¹) := by
        rw [div_eq_mul_inv]; ring
    _ = (1 - t) ^ (-(1 / α)) * (l * (1 - 1 / α)⁻¹) := by rw [h_pow_combine]
    _ = α / (α - 1) * (l * (1 - t) ^ (-(1 / α))) := by
        rw [h_factor_eq]; ring

/-- **Positive homogeneity of spectral risk measures in `l`.**  For any
    weight `φ`, `spectralRiskMeasure φ (c · l) α = c · spectralRiskMeasure φ l α`. -/
theorem spectralRiskMeasure_scale (c l α : ℝ) (φ : ℝ → ℝ) :
    spectralRiskMeasure φ (c * l) α = c * spectralRiskMeasure φ l α := by
  unfold spectralRiskMeasure
  rw [show (c * ∫ p in (0:ℝ)..1, φ p * paretoVaR l α p)
        = ∫ p in (0:ℝ)..1, c * (φ p * paretoVaR l α p) from
        (intervalIntegral.integral_const_mul c _).symm]
  congr 1; funext p
  rw [paretoVaR_scale]; ring


end TailOptionPricing
