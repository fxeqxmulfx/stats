module

/-
  The corrected Pareto row of Taleb, arXiv:1802.05495v3, Table I.
  Finite Beta differences give a continuous integrand and a strictly
  positive ratio. These are analytic results about the corrected formula;
  identifying it with a genuine iid-sum MAD remains separate work.
-/
public import Stats.Kappa.Pareto.Beta

@[expose] public section

open Real Set Filter Topology MeasureTheory

namespace TailOptionPricing

/-- Both Beta endpoints of the Table I Pareto row lie strictly inside the
support when `y ≥ 0`, so the corrected integrals avoid both singularities. -/
theorem pareto_beta_endpoints {y : ℝ} (hy : 0 ≤ y) :
    1 / (y + 2) ∈ Ioo (0 : ℝ) 1 ∧ (y + 1) / (y + 2) ∈ Ioo (0 : ℝ) 1 := by
  have hd : 0 < y + 2 := by linarith
  exact ⟨⟨div_pos (by norm_num) hd, (div_lt_one hd).mpr (by linarith)⟩,
    ⟨div_pos (by linarith) hd, (div_lt_one hd).mpr (by linarith)⟩⟩

example : 1 / (1 + 2) ∈ Ioo (0 : ℝ) 1 ∧ (1 + 1) / (1 + 2) ∈ Ioo (0 : ℝ) 1 :=
  pareto_beta_endpoints (by norm_num)

/-- The corrected Table I Pareto integrand is strictly positive in the
interior of its integration interval for every `α > 1`. -/
theorem paretoIntegrand_pos {α y : ℝ} (hα : 1 < α)
    (hy : 0 < y) (hyU : y < 2 / (α - 1)) : 0 < paretoIntegrand α y := by
  have hend := pareto_beta_endpoints hy.le
  have hab : 1 / (y + 2) < (y + 1) / (y + 2) :=
    div_lt_div_of_pos_right (by linarith) (by linarith)
  have hBeta := incompleteBetaCentered_strictMonoOn (-α) (1 - α) hend.1 hend.2 hab
  have hc := mul_neg_of_neg_of_pos
    (mul_neg_of_neg_of_pos
      (mul_neg_of_neg_of_pos (by norm_num : (-2 : ℝ) < 0)
        (pow_pos (by linarith : 0 < α) 2))
      (Real.rpow_pos_of_pos (by linarith : 0 < y + 2) (-2 * α - 1)))
    (sub_pos.mpr hyU)
  exact mul_pos_of_neg_of_neg hc (sub_neg.mpr hBeta)

example : 0 < paretoIntegrand 2 1 :=
  paretoIntegrand_pos (by norm_num) (by norm_num) (by norm_num)

/-- The corrected Pareto integrand is continuous on `y ≥ 0`; its primitive
arguments stay in `(0,1)` for every real parameter `α`. -/
theorem paretoIntegrand_continuousOn (α : ℝ) :
    ContinuousOn (paretoIntegrand α) (Ici 0) := by
  have hden : ContinuousOn (fun y : ℝ => y + 2) (Ici 0) :=
    continuousOn_id.add continuousOn_const
  have hd : ∀ y ∈ Ici (0 : ℝ), y + 2 ≠ 0 := by
    intro y hy
    have hy0 : 0 ≤ y := hy
    linarith
  have ha : ContinuousOn (fun y : ℝ => 1 / (y + 2)) (Ici 0) :=
    continuousOn_const.div hden hd
  have hb : ContinuousOn (fun y : ℝ => (y + 1) / (y + 2)) (Ici 0) :=
    (continuousOn_id.add continuousOn_const).div hden hd
  have hprim := incompleteBetaCentered_continuousOn (-α) (1 - α)
  have hA : ContinuousOn
      (fun y => incompleteBetaCentered (1 / (y + 2)) (-α) (1 - α)) (Ici 0) :=
    hprim.comp ha (fun _ hy => (pareto_beta_endpoints hy).1)
  have hB : ContinuousOn
      (fun y => incompleteBetaCentered ((y + 1) / (y + 2)) (-α) (1 - α)) (Ici 0) :=
    hprim.comp hb (fun _ hy => (pareto_beta_endpoints hy).2)
  have hp : ContinuousOn (fun y : ℝ => (y + 2) ^ (-2 * α - 1)) (Ici 0) :=
    hden.rpow_const (fun y hy => Or.inl (hd y hy))
  unfold paretoIntegrand
  exact ((continuousOn_const.mul hp).mul
    (continuousOn_const.sub continuousOn_id)).mul (hA.sub hB)

/-- The corrected outer integral from Table I is a convergent ordinary
integral for `α > 1`, not a zero value assigned to a divergent expression. -/
theorem paretoIntegrand_intervalIntegrable {α : ℝ} (hα : 1 < α) :
    IntervalIntegrable (paretoIntegrand α) volume 0 (2 / (α - 1)) := by
  have hU : 0 < 2 / (α - 1) := div_pos (by norm_num) (by linarith)
  apply ContinuousOn.intervalIntegrable
  apply (paretoIntegrand_continuousOn α).mono
  intro y hy
  rw [uIcc_of_le hU.le] at hy
  exact hy.1

example : IntervalIntegrable (paretoIntegrand 2) volume 0 2 := by
  have h := paretoIntegrand_intervalIntegrable (by norm_num : (1 : ℝ) < 2)
  norm_num at h
  exact h

/-- The corrected analytic ratio in Table I is strictly positive throughout
the paper's `α > 1` range. A genuine MAD identification is not used here. -/
theorem paretoRatio_pos {α : ℝ} (hα : 1 < α) : 0 < paretoRatio α := by
  have hαpos : 0 < α := by linarith
  have hU : 0 < 2 / (α - 1) := div_pos (by norm_num) (by linarith)
  have hi := intervalIntegral.intervalIntegral_pos_of_pos_on
    (paretoIntegrand_intervalIntegrable hα)
    (fun _ hy => paretoIntegrand_pos hα hy.1 hy.2) hU
  exact mul_pos (mul_pos (Real.rpow_pos_of_pos (by linarith : 0 < α - 1) _)
    (Real.rpow_pos_of_pos hαpos _)) hi

example : 0 < paretoRatio 2 := paretoRatio_pos (by norm_num)

end TailOptionPricing
