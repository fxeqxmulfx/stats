/-
  Pareto probability measure on ℝ.

  ## Stats.Pareto.Measure

  Construction of the strong-Pareto law as a `Measure ℝ` via
  `volume.withDensity`, with a density supported on `Ioi l`.
  Provides:
    * `paretoMeasure (l α : ℝ) : Measure ℝ`
    * `IsProbabilityMeasure (paretoMeasure l α)` instance (for `0 < l, 0 < α`)
    * `paretoMeasure_real_Ioi_eq_survival` : tail formula `μ(Ioi t) = (l/t)^α` for `l ≤ t`.

  Used as the base for Le Cam impossibility and for Pareto product
  detection-power bounds (todo7.md, tasks A4b and D4).
-/
import Stats.Pareto.Mispricing
import Stats.RiskMeasures.Moments
import Stats.HiddenMoments

open Real Set MeasureTheory Filter Topology

namespace TailOptionPricing

/-- The strong-Pareto law on ℝ, encoded as the Lebesgue measure weighted
by the Pareto density on the support `(l, ∞)`.  For `s ≤ l`, the
indicator zeroes out the density (the Pareto law has no mass on `(-∞, l]`). -/
noncomputable def paretoMeasure (l α : ℝ) : Measure ℝ :=
  volume.withDensity
    (fun s => if l < s then ENNReal.ofReal (paretoDensity l α s) else 0)

/-- **Measurability of the Pareto density.**  Lebesgue-measurable on the
whole real line; values at `s ≤ 0` are junk (the denominator `s^(α+1)`
may vanish via `Real.rpow`'s convention), but `Real.rpow` is measurable
for any fixed exponent. -/
theorem paretoDensity_measurable (l α : ℝ) :
    Measurable (fun s : ℝ => paretoDensity l α s) := by
  unfold paretoDensity
  exact (measurable_const).div (measurable_id.pow_const (α + 1))

/-- **Pointwise indicator form** of the `withDensity` integrand:
    the conditional `if l < s then ofReal d s else 0` equals the
    `Ioi l`-indicator of `ofReal ∘ d`. -/
private lemma paretoMeasure_integrand_eq_indicator (l α : ℝ) :
    (fun s : ℝ => if l < s then ENNReal.ofReal (paretoDensity l α s) else 0)
      = (Set.Ioi l).indicator (fun s => ENNReal.ofReal (paretoDensity l α s)) := by
  funext s
  by_cases h : l < s
  · rw [if_pos h, Set.indicator_of_mem (Set.mem_Ioi.mpr h)]
  · rw [if_neg h, Set.indicator_of_notMem (fun hm => h (Set.mem_Ioi.mp hm))]

/-- **Pareto density is nonneg on `Ioi l`** for `0 < l, 0 < α`. -/
private lemma paretoDensity_nonneg_on_Ioi {l α : ℝ}
    (hl : 0 < l) (hα : 0 ≤ α) :
    ∀ s ∈ Set.Ioi l, 0 ≤ paretoDensity l α s := by
  intro s hs
  have hs_pos : 0 < s := hl.trans hs
  unfold paretoDensity
  have hlα_nonneg : 0 ≤ l ^ α := (Real.rpow_pos_of_pos hl α).le
  have hsα1_pos : 0 < s ^ (α + 1) := Real.rpow_pos_of_pos hs_pos _
  positivity

/-- **`paretoMomentIntegrand l α 0 = paretoDensity l α` pointwise on `Ioi l`**.
The factor `s^0 = 1` collapses. -/
private lemma paretoMomentIntegrand_zero_eq_density {l α : ℝ}
    (hl : 0 < l) :
    ∀ s ∈ Set.Ioi l,
      paretoMomentIntegrand l α 0 s = paretoDensity l α s := by
  intro s hs
  have hs_pos : 0 < s := hl.trans hs
  unfold paretoMomentIntegrand
  rw [Real.rpow_zero, one_mul]

/-- **Pareto measure is a probability measure.**  For `0 < l` and `0 < α`,
the density integrates to 1 on `Ioi l`, hence total mass is 1. -/
theorem instIsProbabilityMeasureParetoMeasure
    (l α : ℝ) (hl : 0 < l) (hα : 0 < α) :
    IsProbabilityMeasure (paretoMeasure l α) := by
  refine ⟨?_⟩
  unfold paretoMeasure
  rw [withDensity_apply _ MeasurableSet.univ]
  -- `∫⁻ s in univ, …` simplifies to `∫⁻ s, …`.
  rw [Measure.restrict_univ]
  -- Rewrite the conditional as an `Ioi l`-indicator.
  rw [paretoMeasure_integrand_eq_indicator]
  rw [lintegral_indicator measurableSet_Ioi]
  -- Now: `∫⁻ s in Ioi l, ofReal (paretoDensity l α s) = 1`.
  -- Step 1: nonnegativity on Ioi l.
  have h_nonneg : ∀ s ∈ Set.Ioi l, 0 ≤ paretoDensity l α s :=
    paretoDensity_nonneg_on_Ioi hl hα.le
  -- Step 2: integrability on Ioi l, via `paretoMomentIntegrand` at k = 0.
  have h_int_mom : IntegrableOn (paretoMomentIntegrand l α 0) (Ioi l) volume :=
    (paretoMomentIntegrand_integrableOn_iff hl hα).mpr hα
  have h_int : IntegrableOn (fun s => paretoDensity l α s) (Ioi l) volume := by
    refine h_int_mom.congr_fun ?_ measurableSet_Ioi
    intro s hs
    exact paretoMomentIntegrand_zero_eq_density hl s hs
  -- Step 3: convert lintegral to integral (nonneg + integrable).
  have h_eq_int :
      ∫⁻ s in Ioi l, ENNReal.ofReal (paretoDensity l α s) ∂volume
        = ENNReal.ofReal (∫ s in Ioi l, paretoDensity l α s ∂volume) := by
    rw [← ofReal_integral_eq_lintegral_ofReal h_int]
    refine (ae_restrict_iff' measurableSet_Ioi).mpr ?_
    exact ae_of_all _ (fun s hs => h_nonneg s hs)
  rw [h_eq_int]
  -- Step 4: identify the Bochner integral with `paretoMoment l α 0`.
  have h_int_eq_mom : ∫ s in Ioi l, paretoDensity l α s ∂volume
                       = paretoMoment l α 0 := by
    unfold paretoMoment
    refine (setIntegral_congr_fun measurableSet_Ioi ?_).symm
    intro s hs
    exact paretoMomentIntegrand_zero_eq_density hl s hs
  rw [h_int_eq_mom]
  -- Step 5: `paretoMoment l α 0 = α * l^0 / (α - 0) = 1`.
  rw [paretoMoment_eq hα hl (le_refl 0)]
  rw [Real.rpow_zero, sub_zero, mul_one, div_self hα.ne']
  exact ENNReal.ofReal_one

/-- **Pareto tail formula.**  For `0 < l ≤ t` and `0 < α`,
    `(paretoMeasure l α).real (Ioi t) = (l / t)^α`. -/
theorem paretoMeasure_real_Ioi_eq_survival
    {l α t : ℝ} (hl : 0 < l) (hα : 0 < α) (ht : l ≤ t) :
    (paretoMeasure l α).real (Set.Ioi t) = (l / t) ^ α := by
  have ht_pos : 0 < t := hl.trans_le ht
  -- Compute the underlying ENNReal measure of `Ioi t`.
  have h_mass :
      paretoMeasure l α (Set.Ioi t)
        = ENNReal.ofReal ((l / t) ^ α) := by
    unfold paretoMeasure
    rw [withDensity_apply _ measurableSet_Ioi]
    -- Rewrite the conditional as `Ioi l`-indicator.
    rw [paretoMeasure_integrand_eq_indicator]
    rw [setLIntegral_indicator measurableSet_Ioi]
    -- `Ioi l ∩ Ioi t = Ioi t` since `l ≤ t`.
    have h_inter : Set.Ioi l ∩ Set.Ioi t = Set.Ioi t := by
      ext s
      simp only [Set.mem_inter_iff, Set.mem_Ioi]
      refine ⟨fun ⟨_, h⟩ => h, fun h => ⟨ht.trans_lt h, h⟩⟩
    rw [h_inter]
    -- Now: `∫⁻ s in Ioi t, ofReal (paretoDensity l α s) = ofReal ((l/t)^α)`.
    -- Nonneg on Ioi t (since Ioi t ⊆ Ioi l).
    have h_nonneg_on_t : ∀ s ∈ Set.Ioi t, 0 ≤ paretoDensity l α s := by
      intro s hs
      have hs_in_l : s ∈ Set.Ioi l := Set.mem_Ioi.mpr (ht.trans_lt hs)
      exact paretoDensity_nonneg_on_Ioi hl hα.le s hs_in_l
    -- Integrability of `paretoDensity` on Ioi t: comes from `paretoMomentIntegrand`
    -- on Ioi l restricted to the smaller set Ioi t.
    have h_int_mom_on_l : IntegrableOn
        (paretoMomentIntegrand l α 0) (Ioi l) volume :=
      (paretoMomentIntegrand_integrableOn_iff hl hα).mpr hα
    have h_subset : Set.Ioi t ⊆ Set.Ioi l := fun s hs => ht.trans_lt hs
    have h_int_mom_on_t : IntegrableOn
        (paretoMomentIntegrand l α 0) (Ioi t) volume :=
      h_int_mom_on_l.mono_set h_subset
    have h_int_on_t : IntegrableOn
        (fun s => paretoDensity l α s) (Ioi t) volume := by
      refine h_int_mom_on_t.congr_fun ?_ measurableSet_Ioi
      intro s hs
      have hs_in_l : s ∈ Set.Ioi l := Set.mem_Ioi.mpr (ht.trans_lt hs)
      exact paretoMomentIntegrand_zero_eq_density hl s hs_in_l
    -- Convert lintegral to integral.
    have h_eq_int :
        ∫⁻ s in Ioi t, ENNReal.ofReal (paretoDensity l α s) ∂volume
          = ENNReal.ofReal (∫ s in Ioi t, paretoDensity l α s ∂volume) := by
      rw [← ofReal_integral_eq_lintegral_ofReal h_int_on_t]
      refine (ae_restrict_iff' measurableSet_Ioi).mpr ?_
      exact ae_of_all _ (fun s hs => h_nonneg_on_t s hs)
    rw [h_eq_int]
    -- Identify `∫_t^∞ paretoDensity` with `paretoTailMoment l α 0 t`.
    have h_int_eq_tm : ∫ s in Ioi t, paretoDensity l α s ∂volume
                        = paretoTailMoment l α 0 t := by
      unfold paretoTailMoment
      refine setIntegral_congr_fun measurableSet_Ioi ?_
      intro s _
      show paretoDensity l α s = s ^ (0:ℝ) * paretoDensity l α s
      rw [Real.rpow_zero, one_mul]
    rw [h_int_eq_tm, paretoTailMoment_at_zero hα hl ht]
    rfl
  -- Now turn the `ENNReal` mass into a real via `.toReal`.
  rw [Measure.real, h_mass]
  have h_div_nonneg : 0 ≤ (l / t) ^ α := by
    have hltp : 0 < l / t := div_pos hl ht_pos
    exact (Real.rpow_pos_of_pos hltp α).le
  exact ENNReal.toReal_ofReal h_div_nonneg

/-- **Le Cam two-point inequality, scalar Pareto.**  For any
measurable set `A ⊆ ℝ`, the sum of false-positive and false-negative
probabilities (under two Pareto laws differing only in scale) is at
least `(l₀/l₁)^α` — the irreducible disagreement coming from the
strip `(l₁, ∞)` where both laws are supported and the smaller-scale
law has the dominated density.

This is the quantitative impossibility statement underlying the
identifiability section of `note.tex`: no statistic of a single
observation can drive both type-I and type-II errors below this bound. -/
theorem leCam_pareto_scale {l₀ l₁ α : ℝ}
    (hα : 0 < α) (hl₀ : 0 < l₀) (hl_lt : l₀ < l₁) :
    ∀ (A : Set ℝ), MeasurableSet A →
      (paretoMeasure l₀ α).real A + (paretoMeasure l₁ α).real Aᶜ
        ≥ (l₀ / l₁) ^ α := by
  intro A hA
  set P₀ : Measure ℝ := paretoMeasure l₀ α with hP₀_def
  set P₁ : Measure ℝ := paretoMeasure l₁ α with hP₁_def
  have hl₁ : 0 < l₁ := hl₀.trans hl_lt
  -- Probability-measure instances (give finiteness for measureReal manipulations).
  haveI : IsProbabilityMeasure P₀ := instIsProbabilityMeasureParetoMeasure l₀ α hl₀ hα
  haveI : IsProbabilityMeasure P₁ := instIsProbabilityMeasureParetoMeasure l₁ α hl₁ hα
  -- (1) Rewrite (l₀/l₁)^α as P₀.real (Ioi l₁).
  have h_target : (l₀ / l₁) ^ α = P₀.real (Set.Ioi l₁) :=
    (paretoMeasure_real_Ioi_eq_survival hl₀ hα hl_lt.le).symm
  rw [ge_iff_le, h_target]
  -- (2) Split P₀.real (Ioi l₁) into A and Aᶜ pieces.
  have hMeas_Ioi : MeasurableSet (Set.Ioi l₁) := measurableSet_Ioi
  have hMeas_A_Ioi  : MeasurableSet (A  ∩ Set.Ioi l₁) := hA.inter hMeas_Ioi
  have hMeas_Ac_Ioi : MeasurableSet (Aᶜ ∩ Set.Ioi l₁) := hA.compl.inter hMeas_Ioi
  have hdisj : Disjoint (A ∩ Set.Ioi l₁) (Aᶜ ∩ Set.Ioi l₁) := by
    refine Disjoint.mono Set.inter_subset_left Set.inter_subset_left ?_
    exact disjoint_compl_right
  have hunion : (A ∩ Set.Ioi l₁) ∪ (Aᶜ ∩ Set.Ioi l₁) = Set.Ioi l₁ := by
    ext x
    constructor
    · rintro (⟨_, hx⟩ | ⟨_, hx⟩) <;> exact hx
    · intro hx
      by_cases hxA : x ∈ A
      · exact Or.inl ⟨hxA, hx⟩
      · exact Or.inr ⟨hxA, hx⟩
  have h_split : P₀.real (Set.Ioi l₁)
      = P₀.real (A ∩ Set.Ioi l₁) + P₀.real (Aᶜ ∩ Set.Ioi l₁) := by
    have hu := measureReal_union (μ := P₀) hdisj hMeas_Ac_Ioi
      (measure_ne_top P₀ (A ∩ Set.Ioi l₁)) (measure_ne_top P₀ (Aᶜ ∩ Set.Ioi l₁))
    rw [hunion] at hu
    exact hu
  rw [h_split]
  -- (3) Monotonicity-1: P₀.real (A ∩ Ioi l₁) ≤ P₀.real A.
  have h1 : P₀.real (A ∩ Set.Ioi l₁) ≤ P₀.real A :=
    measureReal_mono Set.inter_subset_left
  -- (4) Density domination on Ioi l₁:  P₀.real B ≤ P₁.real B  for B ⊆ Ioi l₁ measurable.
  have h_dom : ∀ B : Set ℝ, MeasurableSet B → B ⊆ Set.Ioi l₁ →
      P₀.real B ≤ P₁.real B := by
    intro B hB hBsub
    -- Compute both ENNReal masses.
    have hP₀B : P₀ B
        = ∫⁻ s in B, ENNReal.ofReal (paretoDensity l₀ α s) ∂volume := by
      rw [hP₀_def]
      unfold paretoMeasure
      rw [withDensity_apply _ hB]
      refine setLIntegral_congr_fun hB (fun s hs => ?_)
      have hsl₀ : l₀ < s := hl_lt.trans (hBsub hs)
      simp [hsl₀]
    have hP₁B : P₁ B
        = ∫⁻ s in B, ENNReal.ofReal (paretoDensity l₁ α s) ∂volume := by
      rw [hP₁_def]
      unfold paretoMeasure
      rw [withDensity_apply _ hB]
      refine setLIntegral_congr_fun hB (fun s hs => ?_)
      have hsl₁ : l₁ < s := hBsub hs
      simp [hsl₁]
    -- Pointwise density inequality on B.
    have h_pw : ∀ s ∈ B,
        ENNReal.ofReal (paretoDensity l₀ α s)
          ≤ ENNReal.ofReal (paretoDensity l₁ α s) := by
      intro s hs
      have hs_l₁ : l₁ < s := hBsub hs
      have hs_pos : 0 < s := hl₁.trans hs_l₁
      have h_rpow : l₀ ^ α ≤ l₁ ^ α :=
        (Real.rpow_lt_rpow hl₀.le hl_lt hα).le
      have hsα1_pos : 0 < s ^ (α + 1) := Real.rpow_pos_of_pos hs_pos _
      unfold paretoDensity
      refine ENNReal.ofReal_le_ofReal ?_
      have hnum : α * l₀ ^ α ≤ α * l₁ ^ α := by
        exact mul_le_mul_of_nonneg_left h_rpow hα.le
      exact div_le_div_of_nonneg_right hnum hsα1_pos.le
    -- Lintegral inequality.
    have h_li : ∫⁻ s in B, ENNReal.ofReal (paretoDensity l₀ α s) ∂volume
        ≤ ∫⁻ s in B, ENNReal.ofReal (paretoDensity l₁ α s) ∂volume :=
      setLIntegral_mono' hB h_pw
    -- Pass to .real.
    have hP₁B_lt_top : P₁ B ≠ ⊤ := measure_ne_top P₁ B
    have hP₀B_le : P₀ B ≤ P₁ B := by rw [hP₀B, hP₁B]; exact h_li
    simp only [Measure.real]
    exact ENNReal.toReal_mono hP₁B_lt_top hP₀B_le
  -- (5) Apply h_dom to B := Aᶜ ∩ Ioi l₁.
  have h_dom_Ac : P₀.real (Aᶜ ∩ Set.Ioi l₁) ≤ P₁.real (Aᶜ ∩ Set.Ioi l₁) :=
    h_dom (Aᶜ ∩ Set.Ioi l₁) hMeas_Ac_Ioi Set.inter_subset_right
  -- (6) Monotonicity-2: P₁.real (Aᶜ ∩ Ioi l₁) ≤ P₁.real Aᶜ.
  have h2 : P₁.real (Aᶜ ∩ Set.Ioi l₁) ≤ P₁.real Aᶜ :=
    measureReal_mono Set.inter_subset_left
  linarith

/-- **Product Pareto measure**: `d` iid copies of the strong-Pareto law
on `Fin d → ℝ`, built as `MeasureTheory.Measure.pi` of `paretoMeasure l α`.
This is the joint distribution of an iid Pareto sample of size `d`. -/
noncomputable def productPareto (d : ℕ) (l α : ℝ) : Measure (Fin d → ℝ) :=
  MeasureTheory.Measure.pi (fun _ : Fin d => paretoMeasure l α)

/-- **Pareto-strip detection test for the scale-distinguishing problem.**
The set `(l₁, ∞)^d ⊆ ℝᵈ` — the test "reject `H₀ : l = l₀` iff every
coordinate exceeds `l₁`". -/
def paretoScaleStripTest {d : ℕ} (l₁ : ℝ) : Set (Fin d → ℝ) :=
  Set.pi Set.univ (fun _ : Fin d => Set.Ioi l₁)

/-- **Pareto product detection-power bound.**  The simple strip test
`paretoScaleStripTest l₁` (i.e. "all coordinates exceed `l₁`")
achieves total error (type-I + type-II) exactly `(l₀/l₁)^(α·d)`:
exponentially small in `d`.  This shows that, contra the scalar case
(A4b), multi-dimensional iid Pareto samples DO admit a consistent
scale-distinguishing test — identifiability is recovered in the product
case, justifying the multivariate part of the note.tex pipeline. -/
theorem paretoProduct_strip_test_error_eq
    {d : ℕ} {l₀ l₁ α : ℝ}
    (hα : 0 < α) (hl₀ : 0 < l₀) (hl_lt : l₀ < l₁) :
    (productPareto d l₀ α).real (paretoScaleStripTest l₁)
      + (productPareto d l₁ α).real (paretoScaleStripTest l₁)ᶜ
        = (l₀ / l₁) ^ ((α : ℝ) * (d : ℝ)) := by
  set μ₀ : Measure (Fin d → ℝ) := productPareto d l₀ α with hμ₀_def
  set μ₁ : Measure (Fin d → ℝ) := productPareto d l₁ α with hμ₁_def
  set T : Set (Fin d → ℝ) := paretoScaleStripTest l₁ with hT_def
  have hl₁ : 0 < l₁ := hl₀.trans hl_lt
  -- Probability-measure instances for the marginals and the product.
  haveI : IsProbabilityMeasure (paretoMeasure l₀ α) :=
    instIsProbabilityMeasureParetoMeasure l₀ α hl₀ hα
  haveI : IsProbabilityMeasure (paretoMeasure l₁ α) :=
    instIsProbabilityMeasureParetoMeasure l₁ α hl₁ hα
  haveI : IsProbabilityMeasure μ₀ := by
    rw [hμ₀_def]; unfold productPareto; infer_instance
  haveI : IsProbabilityMeasure μ₁ := by
    rw [hμ₁_def]; unfold productPareto; infer_instance
  -- Auxiliary 1: T is measurable.
  have hT_meas : MeasurableSet T := by
    rw [hT_def]
    unfold paretoScaleStripTest
    exact MeasurableSet.univ_pi (fun _ => measurableSet_Ioi)
  -- Auxiliary 2: μ₀(T) = (l₀/l₁)^(α·d).
  have hμ₀T : μ₀.real T = (l₀ / l₁) ^ ((α : ℝ) * (d : ℝ)) := by
    have h_div_nonneg : 0 ≤ l₀ / l₁ := (div_pos hl₀ hl₁).le
    have h_pi_eq : μ₀ T
        = ∏ _i : Fin d, (paretoMeasure l₀ α) (Set.Ioi l₁) := by
      rw [hμ₀_def, hT_def]
      unfold productPareto paretoScaleStripTest
      exact MeasureTheory.Measure.pi_pi _ _
    have h_real : μ₀.real T
        = ∏ _i : Fin d, (paretoMeasure l₀ α).real (Set.Ioi l₁) := by
      simp only [Measure.real, h_pi_eq, ENNReal.toReal_prod]
    rw [h_real]
    -- Each factor equals (l₀/l₁)^α.
    have h_factor : (paretoMeasure l₀ α).real (Set.Ioi l₁) = (l₀ / l₁) ^ α :=
      paretoMeasure_real_Ioi_eq_survival hl₀ hα hl_lt.le
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, h_factor]
    -- ((l₀/l₁)^α)^d = (l₀/l₁)^(α * d).
    rw [← Real.rpow_natCast ((l₀ / l₁) ^ α) d, ← Real.rpow_mul h_div_nonneg]
  -- Auxiliary 3: μ₁(T) = 1.
  have hμ₁T : μ₁.real T = 1 := by
    have h_pi_eq : μ₁ T
        = ∏ _i : Fin d, (paretoMeasure l₁ α) (Set.Ioi l₁) := by
      rw [hμ₁_def, hT_def]
      unfold productPareto paretoScaleStripTest
      exact MeasureTheory.Measure.pi_pi _ _
    have h_real : μ₁.real T
        = ∏ _i : Fin d, (paretoMeasure l₁ α).real (Set.Ioi l₁) := by
      simp only [Measure.real, h_pi_eq, ENNReal.toReal_prod]
    rw [h_real]
    have h_factor : (paretoMeasure l₁ α).real (Set.Ioi l₁) = 1 := by
      rw [paretoMeasure_real_Ioi_eq_survival hl₁ hα (le_refl l₁)]
      rw [div_self hl₁.ne', Real.one_rpow]
    rw [h_factor, Finset.prod_const_one]
  -- Auxiliary 4: μ₁(Tᶜ) = 0.
  have hμ₁Tc : μ₁.real Tᶜ = 0 := by
    have h_add : μ₁.real T + μ₁.real Tᶜ = μ₁.real Set.univ :=
      measureReal_add_measureReal_compl hT_meas
    rw [probReal_univ, hμ₁T] at h_add
    linarith
  -- Final assembly.
  rw [hμ₀T, hμ₁Tc, add_zero]

end TailOptionPricing
