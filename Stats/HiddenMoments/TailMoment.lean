module

/-
  Analytic ingredients for arXiv:2004.05894v1, Eq. 2 and Remark 1.
  Actual sample-law identifications are provided by the sibling modules.
-/
public import Stats.Pareto

@[expose] public section

open Real Set Filter Topology MeasureTheory Finset

namespace TailOptionPricing

/-! ## Pareto p-th tail moment (paper Eq. 2). -/

/-- **Pareto `p`-th tail moment** above threshold `K`:
        `μ_{K, p}(K) := ∫_K^∞ x^p · paretoDensity(l, α, x) dx`. -/
noncomputable def paretoTailMoment (l α p K : ℝ) : ℝ :=
  ∫ s in Ioi K, s ^ p * paretoDensity l α s

/-- **Closed integral form (paper Eq. 2):** For `α > p`, `l > 0`, `l ≤ K`,
        μ_{K, p}(K) = α · l^α · K^{p − α} / (α − p).
    The integral identity is valid for any real `α` with `p < α`.
    Its Pareto moment interpretation additionally requires `α > 0`;
    that formerly unused hypothesis is removed from the algebraic API.
    At positive `α`, this generalises the tail expectation at `p = 1`
    and recovers the supported-tail formula at `p = 0`. -/
theorem paretoTailMoment_eq {l α p K : ℝ}
    (hl : 0 < l) (hp : p < α) (hK : l ≤ K) :
    paretoTailMoment l α p K = α * l ^ α * K ^ (p - α) / (α - p) := by
  have hK_pos : 0 < K := hl.trans_le hK
  have hαp_pos : 0 < α - p := by linarith
  have hαp_ne : (α - p : ℝ) ≠ 0 := hαp_pos.ne'
  have h_neg : p - α - 1 < -1 := by linarith
  -- Reduce the integrand to a constant times an `rpow`.
  have h_pt : ∀ s ∈ Ioi K,
      s ^ p * paretoDensity l α s = (α * l ^ α) * s ^ (p - α - 1) := by
    intros s hs
    have hs_pos : 0 < s := hK_pos.trans hs
    unfold paretoDensity
    have hs_α1_pos : 0 < s ^ (α + 1) := Real.rpow_pos_of_pos hs_pos _
    have hs_α1_ne : s ^ (α + 1) ≠ 0 := hs_α1_pos.ne'
    have h_split : s ^ p / s ^ (α + 1) = s ^ (p - (α + 1)) := by
      rw [← Real.rpow_sub hs_pos]
    rw [show s ^ p * (α * l ^ α / s ^ (α + 1))
          = (α * l ^ α) * (s ^ p / s ^ (α + 1)) from by ring]
    rw [h_split, show (p - (α + 1) : ℝ) = p - α - 1 from by ring]
  unfold paretoTailMoment
  rw [setIntegral_congr_fun measurableSet_Ioi h_pt,
      MeasureTheory.integral_const_mul,
      integral_Ioi_rpow_of_lt h_neg hK_pos]
  -- ∫_K^∞ s^(p - α - 1) ds = -K^(p-α)/(p-α) = K^(p-α)/(α-p).
  rw [show (p - α - 1 + 1 : ℝ) = p - α from by ring]
  rw [show (p - α : ℝ) = -(α - p) from by ring, neg_div_neg_eq]
  ring

/-- **At p = 0**, the tail moment equals the survival function:
        μ_{K, 0}(K) = (l/K)^α = survival(l, α, K). -/
theorem paretoTailMoment_at_zero {l α K : ℝ}
    (hα : 0 < α) (hl : 0 < l) (hK : l ≤ K) :
    paretoTailMoment l α 0 K = survival l α K := by
  have hα_ne : α ≠ 0 := hα.ne'
  have hK_pos : 0 < K := hl.trans_le hK
  rw [paretoTailMoment_eq hl (by linarith : (0:ℝ) < α) hK]
  unfold survival
  rw [show (0 - α : ℝ) = -α from by ring,
      show (α - 0 : ℝ) = α from by ring,
      Real.div_rpow hl.le hK_pos.le, Real.rpow_neg hK_pos.le]
  have hK_α_pos : 0 < K ^ α := Real.rpow_pos_of_pos hK_pos _
  have hK_α_ne : K ^ α ≠ 0 := hK_α_pos.ne'
  field_simp

/-- **At p = 1**, the tail moment equals `paretoTailExpectation`. -/
theorem paretoTailMoment_at_one {l α K : ℝ}
    (hα : 1 < α) (hl : 0 < l) (hK : l ≤ K) :
    paretoTailMoment l α 1 K = paretoTailExpectation l α K := by
  rw [paretoTailMoment_eq hl hα hK,
      paretoTailExpectation_eq hα hl hK]

end TailOptionPricing
