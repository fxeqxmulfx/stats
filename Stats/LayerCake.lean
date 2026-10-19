module

/-
  Layer-cake bridge: connects our `callPrice` (defined as `∫_K^∞ ℙ(S > s) ds`)
  to the expected payoff `E[(S − K)⁺]`.  Closes the gap between the
  layer-cake form (used in the rest of the development) and the standard
  expectation-form definition of European calls.
  The converse L1 transfer and actual tail first-moment identity support
  arXiv:1907.11162v3, Definition 4 and its linear-payoff Theorem 1.
-/
public import Stats.Pareto
public import Stats.Pareto.Moments
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.MeasureTheory.Group.MeasurableEquiv

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory Filter Topology

namespace TailOptionPricing

/-- **Layer-cake bridge** (general).  For a measurable random variable `S` with
    integrable positive part `(S − K)⁺`, the expected payoff equals the
    integral of the survival function on `(K, ∞)`. -/
theorem expectation_max_eq_integral_survival
    {Ω : Type*} {_ : MeasurableSpace Ω} (μ : Measure Ω)
    {S : Ω → ℝ} (K : ℝ)
    (h_int : Integrable (fun ω => max (S ω - K) 0) μ) :
    ∫ ω, max (S ω - K) 0 ∂μ = ∫ s in Ioi K, μ.real {ω | s < S ω} := by
  set f : Ω → ℝ := fun ω => max (S ω - K) 0 with hf
  have f_nn : 0 ≤ᵐ[μ] f := Filter.Eventually.of_forall (fun _ => le_max_right _ _)
  have h_lc := h_int.integral_eq_integral_meas_lt f_nn
  rw [h_lc]
  have h_set : ∀ t ∈ Ioi (0:ℝ),
      μ.real {a : Ω | t < f a} = μ.real {a : Ω | K + t < S a} := by
    intro t ht
    congr 1
    ext ω
    simp only [Set.mem_ofPred_eq, hf, lt_max_iff]
    constructor
    · rintro (h | h)
      · linarith
      · exact (lt_irrefl _ (h.trans ht)).elim
    · intro h; left; linarith
  rw [setIntegral_congr_fun measurableSet_Ioi h_set]
  -- Change of variables `s = K + t` via translation invariance.
  have h_pres : MeasurePreserving ((K : ℝ) + ·) volume volume :=
    measurePreserving_add_left volume K
  have h_emb : MeasurableEmbedding ((K : ℝ) + ·) := measurableEmbedding_addLeft K
  have h_preimage : ((K : ℝ) + ·) ⁻¹' Ioi K = Ioi (0 : ℝ) := by
    ext t; simp [Set.mem_Ioi]
  have h_eq := h_pres.setIntegral_preimage_emb h_emb
    (fun s => μ.real {a | s < S a}) (Ioi K)
  rw [h_preimage] at h_eq
  exact h_eq

/-- **Layer-cake specialised to the strong Pareto law.**  If `S` is a
    non-negative random variable whose survival function is `ℙ(S > s) = (l/s)^α`
    on the relevant tail and whose call payoff is integrable, then the
    expected payoff at strike `K ≥ l` equals our `callPrice`. -/
theorem callPrice_eq_expectation
    {Ω : Type*} {_ : MeasurableSpace Ω} (μ : Measure Ω)
    {S : Ω → ℝ} {l α K : ℝ}
    (h_survival : ∀ s ∈ Ioi K, μ.real {ω | s < S ω} = (l / s) ^ α)
    (h_int : Integrable (fun ω => max (S ω - K) 0) μ) :
    ∫ ω, max (S ω - K) 0 ∂μ = callPrice l α K := by
  rw [expectation_max_eq_integral_survival μ K h_int]
  unfold callPrice survival
  exact setIntegral_congr_fun measurableSet_Ioi h_survival


/-- Tail-survival integrability implies genuine L1 of the upper-tail
observation; no condition on the lower tail is needed. This supplies L1
for arXiv:1907.11162v3, Definition 4 and Theorem 1. -/
theorem integrableOn_id_of_integrableOn_survival (ν : Measure ℝ) [IsFiniteMeasure ν]
    (K : ℝ) (ht : IntegrableOn (fun s : ℝ => ν.real (Ioi s)) (Ioi K)) :
    IntegrableOn (fun x : ℝ => x) (Ioi K) ν := by
  have hn : 0 ≤ᵐ[ν.restrict (Ioi K)] (fun x : ℝ => x - K) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact sub_nonneg.mpr hx.le
  have hc := lintegral_eq_lintegral_meas_lt (ν.restrict (Ioi K)) hn
    (measurable_id.sub_const K).aemeasurable
  have hp : ((fun t : ℝ => K + t) ⁻¹' Ioi K) = Ioi (0 : ℝ) := by
    ext t
    simp only [mem_preimage, mem_Ioi]
    constructor <;> intro h <;> linarith
  have htrans : IntegrableOn (fun t : ℝ => ν.real (Ioi (K + t))) (Ioi 0) := by
    have h := ((measurePreserving_add_left volume K).integrableOn_comp_preimage
      (measurableEmbedding_addLeft K)).mpr ht
    simpa only [hp, Function.comp_def] using h
  have he : (fun t : ℝ => (ν.restrict (Ioi K)) {x : ℝ | t < x - K})
      =ᵐ[volume.restrict (Ioi 0)] (fun t => ENNReal.ofReal (ν.real (Ioi (K + t)))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change 0 < t at ht
    have hs : {x : ℝ | t < x - K} = Ioi (K + t) := by
      ext x
      simp only [mem_ofPred_eq, mem_Ioi]
      constructor <;> intro h <;> linarith
    rw [hs, Measure.restrict_apply measurableSet_Ioi,
      inter_eq_left.mpr (Ioi_subset_Ioi (by linarith : K ≤ K + t))]
    exact (ENNReal.ofReal_toReal (measure_ne_top ν _)).symm
  have hfin : HasFiniteIntegral (fun x : ℝ => x - K) (ν.restrict (Ioi K)) := by
    rw [hasFiniteIntegral_iff_ofReal hn, hc, lintegral_congr_ae he]
    exact htrans.lintegral_lt_top
  have hi : Integrable (fun x : ℝ => x - K) (ν.restrict (Ioi K)) :=
    ⟨(measurable_id.sub_const K).aestronglyMeasurable, hfin⟩
  have hsum : Integrable (fun x : ℝ => (x - K) + K) (ν.restrict (Ioi K)) :=
    hi.add (integrable_const K)
  simpa only [IntegrableOn, sub_add_cancel] using hsum

/-- An actual upper-tail first moment is threshold times actual tail
probability plus the integrated survival; arXiv:1907.11162v3, Theorem 1
uses this bridge for its linear payoff. -/
theorem tailMean_eq_threshold_survival_add_integral (ν : Measure ℝ) [IsFiniteMeasure ν]
    (K : ℝ) (hi : IntegrableOn (fun x : ℝ => x) (Ioi K) ν) :
    (∫ x in Ioi K, x ∂ν) = K * ν.real (Ioi K) + ∫ s in Ioi K, ν.real (Ioi s) := by
  have he : (fun x : ℝ => x - K) =ᵐ[ν.restrict (Ioi K)]
      (fun x => max (x - K) 0) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact (max_eq_left (sub_nonneg.mpr hx.le)).symm
  have hs := expectation_max_eq_integral_survival (ν.restrict (Ioi K)) K
    ((hi.sub (integrable_const K)).congr he)
  rw [integral_congr_ae he.symm, integral_sub hi (integrable_const K),
    integral_const, measureReal_restrict_apply_univ, smul_eq_mul] at hs
  have htail : (∫ s in Ioi K, (ν.restrict (Ioi K)).real {x : ℝ | s < x}) =
      ∫ s in Ioi K, ν.real (Ioi s) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro s hs
    change (ν.restrict (Ioi K)).real (Ioi s) = _
    rw [measureReal_restrict_apply measurableSet_Ioi,
      inter_eq_left.mpr (Ioi_subset_Ioi hs.le)]
  rw [htail] at hs
  linarith

/-- Algebraic identification of normalized conditional mean with the
actual tail ratio (arXiv:1907.11162v3, Definition 4 and Theorem 1),
before any analytic limit or L1 assertion is made. -/
theorem condMean_div_eq_tailMean_ratio (ν : Measure ℝ) (K : ℝ) :
    (∫ x : ℝ, x ∂ν[|Ioi K]) / K = (∫ x in Ioi K, x ∂ν) / (K * ν.real (Ioi K)) := by
  rw [ProbabilityTheory.cond, integral_smul_measure, ENNReal.toReal_inv, smul_eq_mul]
  simp only [Measure.real, div_eq_mul_inv, mul_inv_rev]
  ring

-- A genuine finite-mean Pareto law supplies the analytic hypotheses.
private theorem paretoTwoThree_survival_integrable :
    IntegrableOn (fun s : ℝ => (paretoMeasure 2 3).real (Ioi s)) (Ioi 4) := by
  have hi : IntegrableOn (fun s : ℝ => 8 * s ^ (-3 : ℝ)) (Ioi 4) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-3 : ℝ) < -1) (by norm_num)).const_mul 8
  apply hi.congr_fun _ measurableSet_Ioi
  intro s hs
  change (4 : ℝ) < s at hs
  dsimp only
  rw [paretoMeasure_real_Ioi_eq_survival (by norm_num) (by norm_num) (by linarith),
    Real.div_rpow (by norm_num : (0 : ℝ) ≤ 2) (by linarith : 0 ≤ s),
    Real.rpow_neg (by linarith : 0 ≤ s)]
  norm_num [Real.rpow_ofNat, div_eq_mul_inv]

example : IntegrableOn (fun x : ℝ => x) (Ioi 4) (paretoMeasure 2 3) := by
  let : IsProbabilityMeasure (paretoMeasure 2 3) :=
    instIsProbabilityMeasureParetoMeasure 2 3 (by norm_num) (by norm_num)
  exact integrableOn_id_of_integrableOn_survival _ 4 paretoTwoThree_survival_integrable

example : (∫ x in Ioi (4 : ℝ), x ∂paretoMeasure 2 3) =
    4 * (paretoMeasure 2 3).real (Ioi 4) +
      ∫ s in Ioi (4 : ℝ), (paretoMeasure 2 3).real (Ioi s) := by
  let : IsProbabilityMeasure (paretoMeasure 2 3) :=
    instIsProbabilityMeasureParetoMeasure 2 3 (by norm_num) (by norm_num)
  exact tailMean_eq_threshold_survival_add_integral _ 4
    (integrableOn_id_of_integrableOn_survival _ 4 paretoTwoThree_survival_integrable)

#print axioms integrableOn_id_of_integrableOn_survival
#print axioms tailMean_eq_threshold_survival_add_integral
#print axioms condMean_div_eq_tailMean_ratio

end TailOptionPricing
