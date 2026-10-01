/-
  Risk measures & portfolio theory under Pareto.

  ## Stats.RiskMeasures.Moments — moment finiteness (Item 3).

  `paretoMoment` — `k`-th raw moment integrand finite iff `α > k`,
  with closed form `α · l^k / (α − k)` when finite.  Variance
  finite iff `α > 2`.

  See `Stats/RiskMeasures.lean` for the umbrella module.
-/
import Stats.Pareto

open Real Set MeasureTheory Filter Topology intervalIntegral

namespace TailOptionPricing

/-! ## Item 3 — Moment-finiteness theorem.

    The `k`-th raw moment of `S ~ strong Pareto(l, α)` is finite iff
    `α > k`, with closed form `E[S^k] = α · l^k / (α − k)` in that
    regime.  Foundational disclaimer: explains why Markowitz / Sharpe
    / variance-swap / ARCH-style models break down in the Pareto
    regime (variance finite iff `α > 2`).

    The proof reduces the density-form integrand
    `s^k · α · l^α / s^(α+1)` to the layer-cake form
    `s^(k−1) · survival l α s` via
        `s^k · paretoDensity l α s = α · (s^(k−1) · survival l α s)`,
    and applies the existing biconditional
    `rpow_mul_survival_integrableOn_iff`. -/

/-- **Pareto `k`-th moment integrand.**  Defined so that its integral
    on `(l, ∞)` is the `k`-th raw moment `E[S^k]` when `S ~ strong
    Pareto(l, α)`. -/
noncomputable def paretoMomentIntegrand (l α k s : ℝ) : ℝ :=
  s ^ k * paretoDensity l α s

/-- **Pointwise identity** relating the density-form moment integrand
    to the layer-cake form:
        `s^k · paretoDensity = α · s^(k−1) · survival`. -/
theorem paretoMomentIntegrand_eq_layerCake {l α k s : ℝ}
    (hl : 0 < l) (hs : l < s) :
    paretoMomentIntegrand l α k s = α * (s ^ (k - 1) * survival l α s) := by
  have hs_pos : 0 < s := hl.trans hs
  have hs_α_pos : 0 < s ^ α := Real.rpow_pos_of_pos hs_pos _
  have hs_α_ne : s ^ α ≠ 0 := hs_α_pos.ne'
  have hs_α1_pos : 0 < s ^ (α + 1) := Real.rpow_pos_of_pos hs_pos _
  have hs_α1_ne : s ^ (α + 1) ≠ 0 := hs_α1_pos.ne'
  have h_lhs : paretoMomentIntegrand l α k s = α * l ^ α * s ^ (k - α - 1) := by
    unfold paretoMomentIntegrand paretoDensity
    have h_split : s ^ k = s ^ (k - α - 1) * s ^ (α + 1) := by
      rw [← Real.rpow_add hs_pos]; congr 1; ring
    rw [h_split]
    field_simp
  have h_rhs : α * (s ^ (k - 1) * survival l α s) = α * l ^ α * s ^ (k - α - 1) := by
    unfold survival
    rw [Real.div_rpow hl.le hs_pos.le]
    have h_split : s ^ (k - 1) = s ^ (k - α - 1) * s ^ α := by
      rw [← Real.rpow_add hs_pos]; congr 1; ring
    rw [h_split]
    field_simp
  rw [h_lhs, h_rhs]

/-- **Moment-finiteness biconditional (density form).**  For
    `S ~ strong Pareto(l, α)` with `l > 0` and `α > 0`, the integrand
    of the `k`-th raw moment is integrable on `(l, ∞)` iff `α > k`.

    The positivity assumption on `α` is needed because at `α = 0` the
    Pareto density formally vanishes (`α · l^α / s^(α+1) ≡ 0`), making
    the integrand trivially integrable for any `k`. -/
theorem paretoMomentIntegrand_integrableOn_iff {l α k : ℝ}
    (hl : 0 < l) (hα_pos : 0 < α) :
    IntegrableOn (paretoMomentIntegrand l α k) (Ioi l) volume ↔ k < α := by
  have hα_ne : (α : ℝ) ≠ 0 := hα_pos.ne'
  have hα_unit : IsUnit α := isUnit_iff_ne_zero.mpr hα_ne
  have hα_eq_iff : k - 1 < α - 1 ↔ k < α := by
    constructor <;> intro h <;> linarith
  -- Connect to `s^(k-1) * survival l α s` via the pointwise identity.
  have h_eqOn : EqOn (paretoMomentIntegrand l α k)
      (fun s => α * (s ^ (k - 1) * survival l α s)) (Ioi l) := by
    intro s hs
    simp only [Set.mem_Ioi] at hs
    exact paretoMomentIntegrand_eq_layerCake hl hs
  rw [integrableOn_congr_fun h_eqOn measurableSet_Ioi]
  -- IntegrableOn (α * (s^(k-1) * survival)) ↔ IntegrableOn (s^(k-1) * survival)
  show Integrable (fun s : ℝ => α * (s ^ (k - 1) * survival l α s))
        (volume.restrict (Ioi l)) ↔ k < α
  rw [integrable_const_mul_iff hα_unit]
  exact (rpow_mul_survival_integrableOn_iff hl).trans hα_eq_iff

/-- **Pareto `k`-th moment (closed form).**  When the integrand is
    integrable (equivalently `α > k`), the `k`-th raw moment evaluates
    to `α · l^k / (α − k)`. -/
noncomputable def paretoMoment (l α k : ℝ) : ℝ :=
  ∫ s in Ioi l, paretoMomentIntegrand l α k s

/-- **Closed-form `k`-th raw moment.**  For `α > k > 0` (sufficient
    for both convergence and meaningful `l^k`):
        `E[S^k] = α · l^k / (α − k)`. -/
theorem paretoMoment_eq {l α k : ℝ}
    (hα : k < α) (hl : 0 < l) (hk : 0 ≤ k) :
    paretoMoment l α k = α * l ^ k / (α - k) := by
  have hα_pos : 0 < α := hk.trans_lt hα
  have hαk_pos : 0 < α - k := by linarith
  have hαk_ne : (α - k : ℝ) ≠ 0 := hαk_pos.ne'
  have hα_ne : (α : ℝ) ≠ 0 := hα_pos.ne'
  have hl_pow_pos : 0 < l ^ α := Real.rpow_pos_of_pos hl _
  -- Reduce paretoMoment to α · l^α · ∫_l^∞ s^(k-α-1) ds.
  have h_neg : k - α - 1 < -1 := by linarith
  have h_int_target : IntegrableOn (fun s : ℝ => s ^ (k - α - 1)) (Ioi l) :=
    integrableOn_Ioi_rpow_of_lt h_neg hl
  -- Pointwise identity on (l, ∞).
  have h_pt : ∀ s ∈ Ioi l,
      paretoMomentIntegrand l α k s = α * l ^ α * s ^ (k - α - 1) := by
    intro s hs
    simp only [Set.mem_Ioi] at hs
    have hs_pos : 0 < s := hl.trans hs
    unfold paretoMomentIntegrand paretoDensity
    rw [show s ^ (α + 1) = s ^ (α + 1 - k) * s ^ k from by
          rw [← Real.rpow_add hs_pos]; congr 1; ring,
        show s ^ (k - α - 1) = (s ^ (α + 1 - k))⁻¹ from by
          rw [← Real.rpow_neg hs_pos.le]; congr 1; ring]
    have hs_pow_pos : 0 < s ^ (α + 1 - k) := Real.rpow_pos_of_pos hs_pos _
    have hs_k_pos : 0 < s ^ k := Real.rpow_pos_of_pos hs_pos _
    field_simp
  unfold paretoMoment
  rw [setIntegral_congr_fun measurableSet_Ioi h_pt]
  rw [MeasureTheory.integral_const_mul,
      integral_Ioi_rpow_of_lt h_neg hl]
  have h_exp_eq : (k - α - 1 + 1 : ℝ) = k - α := by ring
  rw [h_exp_eq]
  have hl_pow_combine : l ^ α * l ^ (k - α) = l ^ k := by
    rw [← Real.rpow_add hl]
    congr 1; ring
  have hkα_ne : (k - α : ℝ) ≠ 0 := by
    intro h; apply hαk_ne; linarith
  -- Goal: α * l ^ α * (-l ^ (k - α) / (k - α)) = α * l ^ k / (α - k)
  rw [show -l ^ (k - α) / (k - α) = l ^ (k - α) / (α - k) by
        rw [neg_div, ← div_neg, neg_sub]]
  rw [show α * l ^ α * (l ^ (k - α) / (α - k))
        = α * (l ^ α * l ^ (k - α)) / (α - k) from by ring,
      hl_pow_combine]

/-- **Variance finite iff `α > 2`.**  Direct corollary at `k = 2`. -/
theorem paretoSecondMoment_integrableOn_iff {l α : ℝ}
    (hl : 0 < l) (hα_pos : 0 < α) :
    IntegrableOn (paretoMomentIntegrand l α 2) (Ioi l) volume ↔ 2 < α :=
  paretoMomentIntegrand_integrableOn_iff hl hα_pos

/-- **Closed form of `E[S^2]` for `α > 2`:** `α · l² / (α − 2)`
    (writing `l^2 = l*l` rather than `Real.rpow l 2`).  The variance
    itself is `E[S²] − (E[S])² = α · l² / ((α − 1)² · (α − 2))`. -/
theorem paretoSecondMoment_eq {l α : ℝ} (hα : 2 < α) (hl : 0 < l) :
    paretoMoment l α 2 = α * l ^ (2:ℝ) / (α - 2) :=
  paretoMoment_eq hα hl (by norm_num)

/-- MAD-vs-MSE integrability gap for Pareto(l, α) with α ∈ (1, 2]:
the first absolute moment of the Pareto density is integrable on `(l, ∞)`
while the second moment is not. -/
theorem mad_integrable_mse_not {l α : ℝ}
    (hl : 0 < l) (hα_lb : 1 < α) (hα_ub : α ≤ 2) :
    IntegrableOn (paretoMomentIntegrand l α 1) (Ioi l) volume
      ∧ ¬ IntegrableOn (paretoMomentIntegrand l α 2) (Ioi l) volume := by
  have hα_pos : (0:ℝ) < α := by linarith
  refine ⟨?_, ?_⟩
  · exact (paretoMomentIntegrand_integrableOn_iff hl hα_pos).mpr hα_lb
  · rw [paretoMomentIntegrand_integrableOn_iff hl hα_pos]
    exact not_lt.mpr hα_ub

end TailOptionPricing
