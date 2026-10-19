module

/-
  Reproducible certificates for the semantic issues described in REVIEW.md.
  These theorems check historical broken definitions and the repaired
  minimum-size criterion. They do not validate the papers' probability claims.

  Source: Taleb, arXiv:1802.05495v3, Table I's Pareto row and incomplete-Beta
  footnote, Definition 1, "Equivalence for stable distributions", and the
  positive-size criterion `md` in "Practical significance for sample
  sufficiency". The historical zero-size defect was in this repository;
  the paper already excludes zero. Constant MAD functions below are
  synthetic checks of the definitions, without a distributional claim.
-/
public import Stats.Kappa.TableI
public import Stats.Review.ParetoLegacy
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

@[expose] public section

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

/-- Both Beta terms in the historical Pareto integrand vanish. -/
theorem legacy_paretoIntegrand_eq_zero {α y : ℝ} (hα : 1 < α) (hy : 0 ≤ y) :
    legacyParetoIntegrand α y = 0 := by
  have hd : 0 < y + 2 := by linarith
  have hz₁ : 0 < 1 / (y + 2) := div_pos zero_lt_one hd
  have hz₁_lt : 1 / (y + 2) < 1 := (div_lt_one hd).mpr (by linarith)
  have hz₂ : 0 < (y + 1) / (y + 2) := div_pos (by linarith) hd
  have hz₂_lt : (y + 1) / (y + 2) < 1 := (div_lt_one hd).mpr (by linarith)
  simp only [legacyParetoIntegrand,
    incompleteBeta_pareto_eq_zero hα hz₁ hz₁_lt,
    incompleteBeta_pareto_eq_zero hα hz₂ hz₂_lt, sub_self, mul_zero]

/-- The historical Pareto ratio is zero for every α > 1. -/
theorem legacy_paretoRatio_eq_zero {α : ℝ} (hα : 1 < α) :
    legacyParetoRatio α = 0 := by
  have hu : 0 ≤ 2 / (α - 1) := by positivity
  have hint : (∫ y in (0 : ℝ)..(2 / (α - 1)),
      legacyParetoIntegrand α y) = 0 := by
    calc
      _ = ∫ _y in (0 : ℝ)..(2 / (α - 1)), (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro y hy
        rw [uIcc_of_le hu] at hy
        exact legacy_paretoIntegrand_eq_zero hα hy.1
      _ = 0 := by simp
  simp only [legacyParetoRatio, hint, mul_zero]

/-- The historical Pareto κ expression was always 2. -/
theorem legacy_paretoKappa_eq_two {α : ℝ} (hα : 1 < α) :
    legacyParetoKappa α = 2 := by
  simp [legacyParetoKappa, legacy_paretoRatio_eq_zero hα]

/-- Historical minimum-size definition, retained only to certify the old bug. -/
noncomputable def legacyNMin (Mν Mg : ℕ → ℝ) (ng : ℕ) : ℕ :=
  sInf {n : ℕ | TailOptionPricing.sampleMeanMAD Mν n ≤
    TailOptionPricing.sampleMeanMAD Mg ng}

/-- The historical candidate set incorrectly includes a zero-size sample. -/
theorem legacy_n_min_eq_zero_of_nonneg {Mν Mg : ℕ → ℝ} {ng : ℕ}
    (h : 0 ≤ TailOptionPricing.sampleMeanMAD Mg ng) :
    legacyNMin Mν Mg ng = 0 := by
  apply Nat.le_zero.mp
  apply Nat.sInf_le
  show TailOptionPricing.sampleMeanMAD Mν 0 ≤ TailOptionPricing.sampleMeanMAD Mg ng
  simpa only [TailOptionPricing.sampleMeanMAD, Nat.cast_zero, div_zero] using h

/-- A zero-MAD model needs one observation, rather than the old zero answer. -/
theorem n_min_zero_mad_eq_one :
    TailOptionPricing.n_min (fun _ => 0) (fun _ => 0) 1 = 1 := by
  have hw : ∃ k : ℕ, 0 < k ∧
      TailOptionPricing.sampleMeanMAD (fun _ => 0) k ≤
        TailOptionPricing.sampleMeanMAD (fun _ => 0) 1 :=
    ⟨1, by norm_num [TailOptionPricing.sampleMeanMAD]⟩
  have hpos := TailOptionPricing.n_min_pos hw
  have hle := TailOptionPricing.n_min_le_of_witness
    (M_ν := fun _ => 0) (M_g := fun _ => 0) (n_g := 1) (n_ν := 1)
    (by norm_num) (by norm_num [TailOptionPricing.sampleMeanMAD])
  omega

/-- The corrected minimum can exceed one: 1/n reaches 1/3 first at n = 3. -/
theorem n_min_unit_mad_eq_three :
    TailOptionPricing.n_min (fun _ => 1) (fun _ => 1) 3 = 3 := by
  have hw : ∃ k : ℕ, 0 < k ∧
      TailOptionPricing.sampleMeanMAD (fun _ => 1) k ≤
        TailOptionPricing.sampleMeanMAD (fun _ => 1) 3 :=
    ⟨3, by norm_num [TailOptionPricing.sampleMeanMAD]⟩
  have hmem := TailOptionPricing.n_min_mem hw
  have hle := TailOptionPricing.n_min_le_of_witness
    (M_ν := fun _ => 1) (M_g := fun _ => 1) (n_g := 3) (n_ν := 3)
    (by norm_num) (by norm_num [TailOptionPricing.sampleMeanMAD])
  have hreal : (0 : ℝ) < TailOptionPricing.n_min (fun _ => 1) (fun _ => 1) 3 :=
    Nat.cast_pos.mpr hmem.1
  have hcmp := (div_le_div_iff₀ hreal (by norm_num : (0 : ℝ) < 3)).mp hmem.2
  have hge : 3 ≤ TailOptionPricing.n_min (fun _ => 1) (fun _ => 1) 3 := by
    exact_mod_cast (show (3 : ℝ) ≤
      TailOptionPricing.n_min (fun _ => 1) (fun _ => 1) 3 by simpa using hcmp)
  omega

#print axioms incompleteBeta_pareto_eq_zero
#print axioms legacy_paretoIntegrand_eq_zero
#print axioms legacy_paretoRatio_eq_zero
#print axioms legacy_paretoKappa_eq_two
#print axioms legacy_n_min_eq_zero_of_nonneg
#print axioms n_min_zero_mad_eq_one
#print axioms n_min_unit_mad_eq_three

/-! Concrete witnesses for every diagnostic theorem's hypotheses. -/

example : TailOptionPricing.incompleteBeta (1 / 2) (-2) (1 - 2) = 0 :=
  incompleteBeta_pareto_eq_zero (α := 2) (by norm_num) (by norm_num) (by norm_num)

example : legacyParetoIntegrand 2 0 = 0 :=
  legacy_paretoIntegrand_eq_zero (by norm_num) (by norm_num)

example : legacyParetoRatio 2 = 0 :=
  legacy_paretoRatio_eq_zero (by norm_num)

example : legacyParetoKappa 2 = 2 :=
  legacy_paretoKappa_eq_two (by norm_num)

example : legacyNMin (fun _ => 1) (fun _ => 1) 1 = 0 :=
  legacy_n_min_eq_zero_of_nonneg (by norm_num [TailOptionPricing.sampleMeanMAD])

/-! Reference curves witness the algebraic hypotheses, not probability laws. -/

example : TailOptionPricing.kappa (fun k => Real.sqrt k) 1 2 = 0 :=
  TailOptionPricing.kappa_gaussian (c := 1) (by norm_num)
    (by intro k _; simp) (by norm_num) (by norm_num)

example : TailOptionPricing.kappa (fun k => (k : ℝ)) 1 2 = 1 :=
  TailOptionPricing.kappa_cauchy (c := 1) (by norm_num)
    (by intro k _; simp) (by norm_num) (by norm_num)

example : TailOptionPricing.kappa (fun k => (k : ℝ) ^ ((1 : ℝ) / (3 / 2))) 1 2 =
    2 - (3 : ℝ) / 2 :=
  TailOptionPricing.kappa_stable_invariance (c := 1) (ᾱ := 3 / 2)
    (by norm_num) (by norm_num) (by intro k _; simp) (by norm_num) (by norm_num)

example : TailOptionPricing.n_nu 30 0 = 30 :=
  TailOptionPricing.n_nu_gaussian 30 (by norm_num)

-- The singular parameter is a value of the total formula, not a sample-size claim.
example : TailOptionPricing.n_nu 30 1 = 1 := by
  norm_num [TailOptionPricing.n_nu]

end StatsReview
