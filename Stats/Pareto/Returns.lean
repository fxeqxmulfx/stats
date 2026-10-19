module

/-
  Strong-Pareto core: Result 2 from
    Taleb–Yarckin–Mann–Delic–Spitznagel,
    "Tail Option Pricing Under Power Laws", arXiv:1908.02347v3 (March 2023).

  ## Stats.Pareto.Returns — geometric return in the regular variation class.

  Result 2 (Eqs. 4–6): `survivalReturns`, `callPriceReturns`,
  `callPriceReturns_eq`, `callPriceReturns_pow_eq`,
  `callPriceReturns_invert`, `callPriceReturns_ratio`.

  See `Stats/Pareto.lean` for the umbrella module.
-/
public import Stats.Pareto.Basic

@[expose] public section

open Real Set MeasureTheory Filter Topology intervalIntegral

namespace TailOptionPricing

/-! ## Result 2.  Geometric return is in the regular variation class. -/

/-- Survival function under Pareto returns: `ℙ(S > s) = ((s − S₀)/(l·S₀))^(−α)`. -/
noncomputable def survivalReturns (l α S₀ s : ℝ) : ℝ :=
  ((s - S₀) / (l * S₀)) ^ (-α)

/-- European call price under Pareto returns. -/
noncomputable def callPriceReturns (l α S₀ K : ℝ) : ℝ :=
  ∫ s in Ioi K, survivalReturns l α S₀ s

/-- **Result 2, Eq. (5).** Closed form of the call price under Pareto returns. -/
theorem callPriceReturns_eq {l α S₀ K : ℝ} (hα : 1 < α) (hl : 0 < l) (hS₀ : 0 < S₀)
    (hK : S₀ * (1 + l) ≤ K) :
    callPriceReturns l α S₀ K = (l * S₀) ^ α * (K - S₀) ^ (1 - α) / (α - 1) := by
  have hα_neg : -α < -1 := by linarith
  have hα1_ne : (α - 1 : ℝ) ≠ 0 := sub_ne_zero.mpr hα.ne'
  have hlS₀_pos : 0 < l * S₀ := mul_pos hl hS₀
  have hS₀_lt_K : S₀ < K := by nlinarith
  have h_pt : ∀ s ∈ Ioi K, ((s - S₀) / (l * S₀)) ^ (-α) =
      (l * S₀) ^ α * (s - S₀) ^ (-α) := by
    intro s hs
    have hs_lt : S₀ < s := hS₀_lt_K.trans hs
    have hsmS₀_pos : 0 < s - S₀ := sub_pos.mpr hs_lt
    rw [Real.div_rpow hsmS₀_pos.le hlS₀_pos.le, Real.rpow_neg hsmS₀_pos.le,
        Real.rpow_neg hlS₀_pos.le]
    field_simp
  unfold callPriceReturns survivalReturns
  rw [setIntegral_congr_fun measurableSet_Ioi h_pt,
      MeasureTheory.integral_const_mul,
      integral_Ioi_sub_rpow_of_lt hα_neg hS₀_lt_K]
  rw [show (-α + 1 : ℝ) = -(α - 1) from by ring, neg_div_neg_eq,
      show (1 - α : ℝ) = -(α - 1) from by ring]
  ring

/-- **Calibration identity (Section II.B), α-th power form.**  Inverting Eq. (5):
    given a market call price `Cm = C(K)` for the anchor strike `K ≥ S₀(1+l)`,
    the product `l · S₀` satisfies

        (l · S₀)^α = (α − 1) · Cm · (K − S₀)^(α − 1).

    This is the symbolic step behind the paper's fitting formula for `l`. -/
theorem callPriceReturns_pow_eq {α S₀ K Cm l : ℝ}
    (hα : 1 < α) (hl : 0 < l) (hS₀ : 0 < S₀) (hK : S₀ * (1 + l) ≤ K)
    (h_match : Cm = callPriceReturns l α S₀ K) :
    (l * S₀) ^ α = (α - 1) * Cm * (K - S₀) ^ (α - 1) := by
  have hα1_ne : (α - 1 : ℝ) ≠ 0 := sub_ne_zero.mpr hα.ne'
  have hK_sub_pos : 0 < K - S₀ := by nlinarith
  rw [h_match, callPriceReturns_eq hα hl hS₀ hK]
  have h_factor : (α - 1) * ((l * S₀) ^ α * (K - S₀) ^ (1 - α) / (α - 1)) =
      (l * S₀) ^ α * (K - S₀) ^ (1 - α) := by field_simp
  rw [h_factor, mul_assoc, ← Real.rpow_add hK_sub_pos,
      show (1 - α + (α - 1) : ℝ) = 0 from by ring, Real.rpow_zero, mul_one]

/-- **Section II.B fitting / calibration formula.**  Closed-form recovery of
    `l · S₀` from the market price `Cm` of the anchor call:

        l · S₀ = (α − 1)^(1/α) · Cm^(1/α) · (K − S₀)^(1 − 1/α).

    This is the formula used in the paper's empirical work to back out `l`
    from observed option prices. -/
theorem callPriceReturns_invert {α S₀ K Cm l : ℝ}
    (hα : 1 < α) (hl : 0 < l) (hS₀ : 0 < S₀) (hK : S₀ * (1 + l) ≤ K)
    (h_match : Cm = callPriceReturns l α S₀ K) :
    l * S₀ = (α - 1) ^ ((1 : ℝ) / α) * Cm ^ ((1 : ℝ) / α) *
             (K - S₀) ^ (1 - 1 / α) := by
  have hα_pos : 0 < α := by linarith
  have hα_ne : α ≠ 0 := hα_pos.ne'
  have hα1_pos : 0 < α - 1 := by linarith
  have hlS₀_pos : 0 < l * S₀ := mul_pos hl hS₀
  have hK_sub_pos : 0 < K - S₀ := by nlinarith
  have hCm_pos : 0 < Cm := by
    rw [h_match, callPriceReturns_eq hα hl hS₀ hK]; positivity
  have h_pow := callPriceReturns_pow_eq hα hl hS₀ hK h_match
  have h_id : l * S₀ = (l * S₀) ^ ((α : ℝ) * (1 / α)) := by
    rw [mul_one_div, div_self hα_ne, Real.rpow_one]
  rw [h_id, Real.rpow_mul hlS₀_pos.le, h_pow,
      Real.mul_rpow (mul_nonneg hα1_pos.le hCm_pos.le)
        (Real.rpow_nonneg hK_sub_pos.le _),
      Real.mul_rpow hα1_pos.le hCm_pos.le,
      ← Real.rpow_mul hK_sub_pos.le,
      show (α - 1) * (1 / α) = 1 - 1 / α from by field_simp]

/-- **Result 2, Eq. (6).** Relative pricing under Pareto returns. The
    Karamata constant `l` and the absolute scale cancel. -/
theorem callPriceReturns_ratio {l α S₀ K₁ K₂ : ℝ} (hα : 1 < α) (hl : 0 < l)
    (hS₀ : 0 < S₀) (hK₁ : S₀ * (1 + l) ≤ K₁) (hK₂ : S₀ * (1 + l) ≤ K₂) :
    callPriceReturns l α S₀ K₂ =
      ((K₂ - S₀) / (K₁ - S₀)) ^ (1 - α) * callPriceReturns l α S₀ K₁ := by
  have hα1_ne : (α - 1 : ℝ) ≠ 0 := sub_ne_zero.mpr hα.ne'
  have hK₁_sub_pos : 0 < K₁ - S₀ := by nlinarith
  have hK₂_sub_pos : 0 < K₂ - S₀ := by nlinarith
  have hK₁_sub_pow_pos : 0 < (K₁ - S₀) ^ (1 - α) := Real.rpow_pos_of_pos hK₁_sub_pos _
  rw [callPriceReturns_eq hα hl hS₀ hK₁, callPriceReturns_eq hα hl hS₀ hK₂,
      Real.div_rpow hK₂_sub_pos.le hK₁_sub_pos.le]
  field_simp


end TailOptionPricing
