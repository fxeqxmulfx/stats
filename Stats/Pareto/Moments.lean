module

/-
  Actual Pareto moments and their integrability, connecting the
  density calculation in arXiv:2004.05894v1, Eq. 2, to expectations.
  The moment threshold also supplies the strong-Pareto probability
  interpretation of arXiv:2007.16096v1, Remark 3.
-/
public import Stats.Pareto.Integration

@[expose] public section

open Real Set MeasureTheory

namespace TailOptionPricing

/-- The power of an actual Pareto observation is integrable exactly
when its exponent is smaller than the positive tail index. -/
theorem paretoMeasure_integrable_rpow_iff {l α p : ℝ}
    (hl : 0 < l) (hα : 0 < α) :
    Integrable (fun s : ℝ => s ^ p) (paretoMeasure l α) ↔ p < α := by
  rw [paretoMeasure_integrable_iff hl hα]
  exact paretoMomentIntegrand_integrableOn_iff hl hα

/-- Actual population moment of the supported Pareto law. Its finite
expectation is justified by `paretoMeasure_integrable_rpow_iff`. -/
theorem paretoMeasure_integral_rpow {l α p : ℝ}
    (hl : 0 < l) (hα : 0 < α) (hp : p < α) :
    (∫ s : ℝ, s ^ p ∂paretoMeasure l α) = α * l ^ p / (α - p) := by
  rw [paretoMeasure_integral hl hα]
  change paretoTailMoment l α p l = _
  rw [paretoTailMoment_eq hl hp le_rfl]
  have he : l ^ α * l ^ (p - α) = l ^ p := by
    rw [← Real.rpow_add hl]
    congr 1
    ring
  calc α * l ^ α * l ^ (p - α) / (α - p)
      = α * (l ^ α * l ^ (p - α)) / (α - p) := by ring
    _ = α * l ^ p / (α - p) := by rw [he]

theorem paretoMeasure_integrable_id_iff {l α : ℝ} (hl : 0 < l) (hα : 0 < α) :
    Integrable (fun s : ℝ => s) (paretoMeasure l α) ↔ 1 < α := by
  simpa only [Real.rpow_one] using paretoMeasure_integrable_rpow_iff (p := 1) hl hα

theorem paretoMeasure_mean {l α : ℝ} (hl : 0 < l) (hα : 1 < α) :
    (∫ s : ℝ, s ∂paretoMeasure l α) = α * l / (α - 1) := by
  simpa only [Real.rpow_one] using
    paretoMeasure_integral_rpow (p := 1) hl (by linarith : 0 < α) hα

/-- The actual truncated population moment agrees with the density
tail integral above the support boundary. Finiteness is separate. -/
theorem paretoMeasure_tailMoment {l α k : ℝ} (hl : 0 < l) (hα : 0 < α)
    (p : ℝ) (hk : l ≤ k) :
    (∫ s in Ioi k, s ^ p ∂paretoMeasure l α) = paretoTailMoment l α p k := by
  rw [paretoMeasure_setIntegral hl hα _ measurableSet_Ioi]
  have he : Ioi l ∩ Ioi k = Ioi k := by
    ext s
    simp only [mem_inter_iff, mem_Ioi]
    exact ⟨fun h => h.2, fun h => ⟨hk.trans_lt h, h⟩⟩
  rw [he]
  rfl

/-- Eq. 2 as a genuine truncated expectation under the Pareto law. -/
theorem paretoMeasure_tailMoment_eq {l α p k : ℝ} (hl : 0 < l) (hα : 0 < α)
    (hp : p < α) (hk : l ≤ k) :
    (∫ s in Ioi k, s ^ p ∂paretoMeasure l α) = α * l ^ α * k ^ (p - α) / (α - p) := by
  rw [paretoMeasure_tailMoment hl hα p hk, paretoTailMoment_eq hl hp hk]

example : Integrable (fun s : ℝ => s) (paretoMeasure 1 2) :=
  (paretoMeasure_integrable_id_iff (by norm_num) (by norm_num)).mpr (by norm_num)

example : ¬ Integrable (fun s : ℝ => s ^ (2 : ℝ)) (paretoMeasure 1 2) := by
  rw [paretoMeasure_integrable_rpow_iff (by norm_num) (by norm_num)]
  norm_num

example : (∫ s : ℝ, s ∂paretoMeasure 1 2) = 2 := by
  rw [paretoMeasure_mean (by norm_num) (by norm_num)]
  norm_num

example : (∫ s in Ioi (2 : ℝ), s ∂paretoMeasure 1 2) = 1 := by
  have h := paretoMeasure_tailMoment_eq (l := 1) (α := 2) (p := 1) (k := 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [Real.rpow_neg_one, Real.rpow_ofNat] at h
  exact h

end TailOptionPricing
