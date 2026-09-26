/-
  Strong-Pareto core: definitions and Result 1 from
    Taleb–Yarckin–Mann–Delic–Spitznagel,
    "Tail Option Pricing Under Power Laws", arXiv:1908.02347v3 (March 2023).

  ## Stats.Pareto.Basic — survival function, call price, Result 1.

  This submodule contains:

    * Helper: shifted rpow integral on `Ioi`.
    * Result 1 (Eqs. 2–3): `survival`, `callPrice`, `callPrice_eq`,
      `callPrice_ratio`, `callPrice_invert`,
      `integrableOn_rpow_mul_survival`.

  See `Stats/Pareto.lean` for the umbrella module.
-/
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open Real Set MeasureTheory Filter Topology intervalIntegral

namespace TailOptionPricing

/-! ## Helper: shifted rpow integral on `Ioi`. -/

lemma integrableOn_Ioi_sub_rpow_of_lt {a S₀ K : ℝ} (ha : a < -1) (hK : S₀ < K) :
    IntegrableOn (fun s : ℝ ↦ (s - S₀) ^ a) (Ioi K) := by
  have h := integrableOn_add_rpow_Ioi_of_lt (a := a) (m := -S₀) (c := K) ha (by linarith)
  simpa [sub_eq_add_neg] using h

lemma integral_Ioi_sub_rpow_of_lt {a S₀ K : ℝ} (ha : a < -1) (hK : S₀ < K) :
    ∫ s in Ioi K, (s - S₀) ^ a = -(K - S₀) ^ (a + 1) / (a + 1) := by
  have hap1_ne : a + 1 ≠ 0 := by linarith
  have hd : ∀ x ∈ Ici K, HasDerivAt (fun t : ℝ ↦ (t - S₀) ^ (a + 1) / (a + 1))
      ((x - S₀) ^ a) x := by
    intro x hx
    have hx_pos : 0 < x - S₀ := by linarith [mem_Ici.mp hx]
    have h₁ : HasDerivAt (fun t : ℝ ↦ t - S₀) 1 x := (hasDerivAt_id x).sub_const S₀
    have h₂ := (h₁.rpow_const (p := a + 1) (Or.inl hx_pos.ne')).div_const (a + 1)
    convert h₂ using 1
    rw [show (a + 1 - 1 : ℝ) = a from by ring]
    field_simp
  have ht : Tendsto (fun t : ℝ ↦ (t - S₀) ^ (a + 1) / (a + 1)) atTop
      (𝓝 (0 / (a + 1))) := by
    apply Tendsto.div_const
    have hpos : 0 < -(a + 1) := by linarith
    have h_shift : Tendsto (fun t : ℝ ↦ t - S₀) atTop atTop := by
      simpa [sub_eq_add_neg] using
        tendsto_atTop_add_const_right atTop (-S₀) tendsto_id
    rw [← neg_neg (a + 1)]
    exact (tendsto_rpow_neg_atTop hpos).comp h_shift
  have hi := integrableOn_Ioi_sub_rpow_of_lt ha hK
  convert integral_Ioi_of_hasDerivAt_of_tendsto' hd hi ht using 1
  simp only [zero_div, zero_sub, neg_div]

/-! ## Result 1.  S in the regular variation class. -/

/-- Strong Pareto survival function on `s ≥ l`. -/
noncomputable def survival (l α s : ℝ) : ℝ := (l / s) ^ α

/-- European call price under the strong Pareto law, defined via the
    layer-cake representation `C(K) = ∫_K^∞ ℙ(S > s) ds`. -/
noncomputable def callPrice (l α K : ℝ) : ℝ :=
  ∫ s in Ioi K, survival l α s

/-- **Result 1, Eq. (2).** Closed form of the call price under a strong
    Pareto tail. -/
theorem callPrice_eq {l α K : ℝ} (hα : 1 < α) (hl : 0 < l) (hK : l ≤ K) :
    callPrice l α K = l ^ α * K ^ (1 - α) / (α - 1) := by
  have hK_pos : 0 < K := hl.trans_le hK
  have hα_neg : -α < -1 := by linarith
  have hα1_ne : (α - 1 : ℝ) ≠ 0 := sub_ne_zero.mpr hα.ne'
  have h_pt : ∀ s ∈ Ioi K, (l / s) ^ α = l ^ α * s ^ (-α) := by
    intro s hs
    have hs_pos : 0 < s := hK_pos.trans hs
    rw [Real.div_rpow hl.le hs_pos.le, Real.rpow_neg hs_pos.le, ← div_eq_mul_inv]
  unfold callPrice survival
  rw [setIntegral_congr_fun measurableSet_Ioi h_pt,
      MeasureTheory.integral_const_mul,
      integral_Ioi_rpow_of_lt hα_neg hK_pos]
  rw [show (-α + 1 : ℝ) = -(α - 1) from by ring, neg_div_neg_eq,
      show (1 - α : ℝ) = -(α - 1) from by ring]
  ring

/-- **Result 1, Eq. (3).** Relative pricing: the call-price ratio depends only
    on the strikes and the tail index `α`. The Karamata constant `l` cancels. -/
theorem callPrice_ratio {l α K₁ K₂ : ℝ} (hα : 1 < α) (hl : 0 < l)
    (hK₁ : l ≤ K₁) (hK₂ : l ≤ K₂) :
    callPrice l α K₂ = (K₂ / K₁) ^ (1 - α) * callPrice l α K₁ := by
  have hK₁_pos : 0 < K₁ := hl.trans_le hK₁
  have hK₂_pos : 0 < K₂ := hl.trans_le hK₂
  have hα1_ne : (α - 1 : ℝ) ≠ 0 := sub_ne_zero.mpr hα.ne'
  have hK₁_pow_pos : 0 < K₁ ^ (1 - α) := Real.rpow_pos_of_pos hK₁_pos _
  rw [callPrice_eq hα hl hK₁, callPrice_eq hα hl hK₂,
      Real.div_rpow hK₂_pos.le hK₁_pos.le]
  field_simp

/-- **Section II.A fitting / calibration formula (strong Pareto).**
    Given a market call price `Cm = C(K)` for the anchor strike `K ≥ l`,
    the Karamata constant `l` is recovered by
        `l = ((α − 1) · Cm · K^(α − 1))^(1/α)`.
    This is the strong-Pareto analogue of `callPriceReturns_invert`. -/
theorem callPrice_invert {α K Cm l : ℝ}
    (hα : 1 < α) (hl : 0 < l) (hK : l ≤ K)
    (h_match : Cm = callPrice l α K) :
    l = ((α - 1) * Cm * K ^ (α - 1)) ^ ((1 : ℝ) / α) := by
  have hα_pos : 0 < α := by linarith
  have hα_ne : α ≠ 0 := hα_pos.ne'
  have hα1_pos : 0 < α - 1 := by linarith
  have hα1_ne : (α - 1 : ℝ) ≠ 0 := hα1_pos.ne'
  have hK_pos : 0 < K := hl.trans_le hK
  -- (α-1)·Cm·K^(α-1) = l^α via the closed-form callPrice_eq.
  have h_pow : (α - 1) * Cm * K ^ (α - 1) = l ^ α := by
    rw [h_match, callPrice_eq hα hl hK]
    rw [show (α - 1) * (l ^ α * K ^ (1 - α) / (α - 1)) * K ^ (α - 1) =
        l ^ α * (K ^ (1 - α) * K ^ (α - 1)) from by field_simp]
    rw [← Real.rpow_add hK_pos,
        show (1 - α + (α - 1) : ℝ) = 0 from by ring,
        Real.rpow_zero, mul_one]
  rw [h_pow, ← Real.rpow_mul hl.le, mul_one_div, div_self hα_ne, Real.rpow_one]

/-- **Higher Pareto moments are finite.**  Under the strong Pareto law on
    `[l, ∞)` with tail index `α > 0`, the integrand `s^k · (l/s)^α` (which
    is the integrand of the `(k+1)`-st raw moment) is integrable on
    `(l, ∞)` whenever `k < α − 1`.  Direct corollary of
    `integrableOn_Ioi_rpow_of_lt`. -/
theorem integrableOn_rpow_mul_survival {l k α : ℝ}
    (hl : 0 < l) (hk : k < α - 1) :
    IntegrableOn (fun s => s ^ k * survival l α s) (Set.Ioi l) := by
  have h_target : IntegrableOn (fun s : ℝ => l ^ α * s ^ (k - α)) (Set.Ioi l) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) hl).const_mul (l ^ α)
  refine h_target.congr_fun ?_ measurableSet_Ioi
  intro s hs
  simp only [Set.mem_Ioi] at hs
  have hs_pos : 0 < s := hl.trans hs
  have hs_α_pos : 0 < s ^ α := Real.rpow_pos_of_pos hs_pos α
  show l ^ α * s ^ (k - α) = s ^ k * survival l α s
  unfold survival
  rw [show s ^ k * (l / s) ^ α = s ^ k * (l ^ α / s ^ α) from by
        rw [Real.div_rpow hl.le hs_pos.le]]
  rw [show k - α = k + (-α) from by ring,
      Real.rpow_add hs_pos, Real.rpow_neg hs_pos.le]
  field_simp


end TailOptionPricing
