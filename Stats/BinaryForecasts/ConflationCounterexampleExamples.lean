module

/-
  Actual Exp(1) witnesses for the fixed-density counterexample and corrected
  converse/strict gap (arXiv:1907.11162v3, Definition 5). The threshold is
  positive, the PDF is normalized and the tail has positive probability.
-/
public import Stats.BinaryForecasts.ConflationCounterexample
public import Stats.BinaryForecasts.PayoffGap

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory Filter Topology

namespace TailOptionPricing

local notation "ν" => expMeasure (1 : ℝ)

local instance conflationExampleLaw_probability : IsProbabilityMeasure ν :=
  isProbabilityMeasure_expMeasure (by norm_num)

example : (∫ x : ℝ, exponentialPDFReal 1 x) = 1 :=
  integral_exponentialPDFReal (by norm_num)

example : ∀ x : ℝ, 0 ≤ exponentialPDFReal 1 x := exponentialPDFReal_nonneg (by norm_num)

example : exponentialPDFReal 1 0 = 1 := by
  rw [exponentialPDFReal_of_nonneg (by norm_num)]
  norm_num

example : 0 < exponentialPDFReal 1 2 ∧ 0 < exponentialPDFReal 1 4 :=
  ⟨exponentialPDFReal_pos (by norm_num) (by norm_num),
    exponentialPDFReal_pos (by norm_num) (by norm_num)⟩

example : (∫ x in Ioi (1 : ℝ), conflationCounterPayoff x ∂ν) =
    ∫ x in Ioi (1 : ℝ), conflationCounterPayoff x * exponentialPDFReal 1 x :=
  expMeasure_setIntegral (by norm_num) _ _

example : IntegrableOn conflationCounterPayoff (Ioi (1 : ℝ)) ν ↔
    IntegrableOn (fun x => conflationCounterPayoff x * exponentialPDFReal 1 x) (Ioi 1) :=
  expMeasure_integrableOn_iff (by norm_num) _ _ measurableSet_Ioi

example : I1 conflationCounterPayoff (exponentialPDFReal 1) 1 = Real.exp (-1) :=
  conflationCounter_I1

example : I2 conflationCounterPayoff (exponentialPDFReal 1) 1 = Real.exp (-1) :=
  conflationCounter_I2

example : (∫ x in Ioi (1 : ℝ), conflationCounterPayoff x ∂ν) = Real.exp (-1) :=
  conflationCounter_actual_integral

example : IntegrableOn conflationCounterPayoff (Ioi (1 : ℝ)) ν :=
  conflationCounter_actual_integrable

example : ¬ ∃ c : ℝ, ∀ x ∈ Ioi (1 : ℝ), conflationCounterPayoff x = c :=
  conflationCounter_not_constant

private theorem conflationExample_tail_mass : (ν).real (Ioi 1) = Real.exp (-1) := by
  rw [expMeasure_real_Ioi (by norm_num)]
  norm_num

-- Equal positive payoffs here come from cancellation, not an empty tail.
example : (∫ x in Ioi (1 : ℝ), conflationCounterPayoff x - 1 ∂ν) = 0 := by
  have h := tailPayoff_gap_eq_integral ν conflationCounter_actual_integrable
  rw [conflationCounter_actual_integral, conflationExample_tail_mass,
    show conflationCounterPayoff 1 = 1 by norm_num [conflationCounterPayoff]] at h
  norm_num at h
  exact h.symm

-- The corrected converse has a genuine nonzero constant-payoff witness.
example : (∫ _ in Ioi (1 : ℝ), (2 : ℝ) ∂ν) = 2 * Real.exp (-1) := by
  have h := (tailPayoff_eq_binary_iff_ae_eq ν (g := fun _ => (2 : ℝ)) (K := 1)
    (integrable_const _) (Filter.Eventually.of_forall (fun _ => le_rfl))).mpr
      (Filter.Eventually.of_forall (fun _ => rfl))
  rw [conflationExample_tail_mass] at h
  exact h

private theorem conflationExample_linear_integrable :
    IntegrableOn (fun x : ℝ => x) (Ioi (1 : ℝ)) ν := by
  rw [expMeasure_integrableOn_iff (by norm_num) _ _ measurableSet_Ioi]
  have h := integrableOn_rpow_mul_exp_neg_rpow (s := 1) (p := 1) (by norm_num) (by norm_num)
  simp only [Real.rpow_one] at h
  apply (h.mono_set (Ioi_subset_Ioi (by norm_num))).congr_fun
  · intro x hx
    dsimp only
    rw [exponentialPDFReal_of_nonneg ((lt_trans (by norm_num : (0 : ℝ) < 1) hx).le)]
    norm_num
  · exact measurableSet_Ioi

example : (ν).real (Ioi 1) < ∫ x in Ioi (1 : ℝ), x ∂ν := by
  have hp : 0 < (ν).real (Ioi 1) := by
    rw [conflationExample_tail_mass]
    exact Real.exp_pos _
  have hs : ∀ᵐ x ∂(ν).restrict (Ioi 1), (1 : ℝ) < x :=
    ae_restrict_of_forall_mem measurableSet_Ioi (fun _ hx => hx)
  have h := tailPayoff_strict_gap ν conflationExample_linear_integrable hp hs
  simpa only [one_mul] using h

#print axioms conflationCounter_actual_integral
#print axioms conflation_fixed_density_counterexample
#print axioms tailPayoff_eq_binary_iff_ae_eq
#print axioms tailPayoff_strict_gap

example : (ν).real (Ioi 1) < (∫ x in Ioi (1 : ℝ), x ∂ν) ↔
    0 < ((ν).restrict (Ioi 1)).real {x : ℝ | 1 < x} := by
  have hm : ∀ᵐ x ∂(ν).restrict (Ioi 1), (1 : ℝ) ≤ x :=
    ae_restrict_of_forall_mem measurableSet_Ioi (fun _ hx => hx.le)
  have h := tailPayoff_strict_gap_iff ν conflationExample_linear_integrable hm
  simpa only [one_mul] using h

#print axioms tailPayoff_strict_gap_iff

end TailOptionPricing
