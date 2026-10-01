/-
  Reproducible certificates for the semantic issues described in REVIEW.md.
  These theorems describe the current definitions; they do not validate the
  corresponding probabilistic claims in the papers.
-/
import Stats.Kappa.TableI
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

open Real Set MeasureTheory

namespace StatsReview

/-- The incomplete Beta integral used in the Pareto row diverges at zero,
    so the total Bochner integral in the current definition equals zero. -/
theorem incompleteBeta_pareto_eq_zero {α z : ℝ}
    (hα : 1 < α) (hz : 0 < z) (hz1 : z < 1) :
    TailOptionPricing.incompleteBeta z (-α) (1 - α) = 0 := by
  unfold TailOptionPricing.incompleteBeta
  apply intervalIntegral.integral_undef
  intro h
  have h_int := (intervalIntegrable_iff_integrableOn_Ioo_of_le hz.le).mp h
  have h_pow : IntegrableOn (fun t : ℝ => t ^ (-α - 1)) (Ioo 0 z) volume := by
    apply h_int.mono' (measurable_id.pow_const _).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have ht_pos : 0 < t := ht.1
    have ht_lt_one : t < 1 := ht.2.trans hz1
    have hfactor : 1 ≤ (1 - t) ^ (1 - α - 1) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos
        (by linarith) (by linarith) (by linarith)
    rw [Real.norm_eq_abs, show id t = t from rfl,
      abs_of_nonneg (Real.rpow_nonneg ht_pos.le _)]
    exact le_mul_of_one_le_right (Real.rpow_nonneg ht_pos.le _) hfactor
  have h_exp := (intervalIntegral.integrableOn_Ioo_rpow_iff hz).mp h_pow
  linarith

/-- Both Beta terms in the current Pareto integrand vanish. -/
theorem paretoIntegrand_eq_zero {α y : ℝ} (hα : 1 < α) (hy : 0 ≤ y) :
    TailOptionPricing.paretoIntegrand α y = 0 := by
  have hd : 0 < y + 2 := by linarith
  have hz₁ : 0 < 1 / (y + 2) := div_pos zero_lt_one hd
  have hz₁_lt : 1 / (y + 2) < 1 := (div_lt_one hd).mpr (by linarith)
  have hz₂ : 0 < (y + 1) / (y + 2) := div_pos (by linarith) hd
  have hz₂_lt : (y + 1) / (y + 2) < 1 := (div_lt_one hd).mpr (by linarith)
  simp only [TailOptionPricing.paretoIntegrand,
    incompleteBeta_pareto_eq_zero hα hz₁ hz₁_lt,
    incompleteBeta_pareto_eq_zero hα hz₂ hz₂_lt, sub_self, mul_zero]

/-- The current closed-form Pareto ratio is zero for every α > 1. -/
theorem paretoRatio_eq_zero {α : ℝ} (hα : 1 < α) :
    TailOptionPricing.paretoRatio α = 0 := by
  have hu : 0 ≤ 2 / (α - 1) := by positivity
  have hint : (∫ y in (0 : ℝ)..(2 / (α - 1)),
      TailOptionPricing.paretoIntegrand α y) = 0 := by
    calc
      _ = ∫ _y in (0 : ℝ)..(2 / (α - 1)), (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro y hy
        rw [uIcc_of_le hu] at hy
        exact paretoIntegrand_eq_zero hα hy.1
      _ = 0 := by simp
  simp only [TailOptionPricing.paretoRatio, hint, mul_zero]

/-- Consequently the project's Pareto κ expression is always 2. -/
theorem paretoKappa_eq_two {α : ℝ} (hα : 1 < α) :
    TailOptionPricing.paretoKappa α = 2 := by
  simp [TailOptionPricing.paretoKappa, paretoRatio_eq_zero hα]

/-- The current minimum-size definition includes the zero-size sample. -/
theorem n_min_eq_zero_of_nonneg {Mν Mg : ℕ → ℝ} {ng : ℕ}
    (h : 0 ≤ TailOptionPricing.sampleMeanMAD Mg ng) :
    TailOptionPricing.n_min Mν Mg ng = 0 := by
  apply Nat.le_zero.mp
  apply TailOptionPricing.n_min_le_of_witness
  simpa only [TailOptionPricing.sampleMeanMAD, Nat.cast_zero, div_zero] using h

#print axioms incompleteBeta_pareto_eq_zero
#print axioms paretoIntegrand_eq_zero
#print axioms paretoRatio_eq_zero
#print axioms paretoKappa_eq_two
#print axioms n_min_eq_zero_of_nonneg

end StatsReview
