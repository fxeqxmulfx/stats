module

/-
  Actual Normal--Gamma precision mixture, arXiv:1912.00277v2,
  Section VI, Eq. compoundGamma. Independently draw a proper Gamma
  precision and a standard Gaussian innovation, then form
  mu+precision^(-1/2)*innovation. The resulting probability law is
  normalized before evaluating any proposed Student density.
  Actual power L1 follows from Gamma inverse moments when a>k/2.
-/
public import Stats.Probability.GammaMoments
public import Stats.EpistemicUncertainty.CompoundLaw

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory

namespace TailOptionPricing

/-- Actual Gamma precision is positive a.e. The density's boundary
at zero is Lebesgue-null, including shapes below one (Section VI). -/
theorem gammaMeasure_ae_pos (a r : ℝ) : ∀ᵐ l ∂gammaMeasure a r, 0 < l := by
  change ∀ᵐ l ∂volume.withDensity (gammaPDF a r), 0 < l
  rw [ae_withDensity_iff (show Measurable (gammaPDF a r) by unfold gammaPDF; fun_prop)]
  have hg := gammaMeasure_rpow_density_ae a r 0
  simp only [Real.rpow_zero, one_mul, add_zero] at hg
  filter_upwards [hg] with l hl hp
  by_contra! hn
  have hout : l ∉ Ioi (0 : ℝ) := not_lt.mpr hn
  rw [indicator_of_notMem hout] at hl
  exact hp (by rw [gammaPDF, hl, ENNReal.ofReal_zero])

/-- The actual dispersion prior induced by the Section VI Gamma
precision. The second parameter r is the source density's RATE. -/
noncomputable def epistemicGammaScaleLaw (a r : ℝ) : Measure ℝ :=
  (gammaMeasure a r).map (fun l : ℝ => l ^ (-1 / 2 : ℝ))

theorem epistemicGammaScaleLaw_probability {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    IsProbabilityMeasure (epistemicGammaScaleLaw a r) := by
  let := isProbabilityMeasure_gammaMeasure ha hr
  unfold epistemicGammaScaleLaw
  exact (Measure.isProbabilityMeasure_map_iff (by fun_prop)).mpr inferInstance

theorem epistemicGammaScaleLaw_ae_pos (a r : ℝ) :
    ∀ᵐ s ∂epistemicGammaScaleLaw a r, 0 < s := by
  unfold epistemicGammaScaleLaw
  apply (ae_map_iff (by fun_prop) measurableSet_Ioi).mpr
  exact (gammaMeasure_ae_pos a r).mono (fun l hl => Real.rpow_pos_of_pos hl _)

/-- Sufficient actual scale-power L1 is derived from the genuine
Gamma inverse moment, independently of compound moments (Section VI).
The shape condition is a>k/2; it cannot be omitted for arbitrary k. -/
theorem epistemicGammaScaleLaw_integrable_pow {a r : ℝ} (ha : 0 < a) (hr : 0 < r)
    (k : ℕ) (hk : (k : ℝ) / 2 < a) :
    Integrable (fun s : ℝ => s ^ k) (epistemicGammaScaleLaw a r) := by
  have hm : Measurable (fun l : ℝ => l ^ (-1 / 2 : ℝ)) := by fun_prop
  have hf : Measurable (fun s : ℝ => s ^ k) := by fun_prop
  rw [epistemicGammaScaleLaw, integrable_map_measure hf.aestronglyMeasurable hm.aemeasurable]
  change Integrable (fun l : ℝ => (l ^ (-1 / 2 : ℝ)) ^ k) (gammaMeasure a r)
  have he : (fun l : ℝ => l ^ (-(k : ℝ) / 2)) =ᵐ[gammaMeasure a r]
      (fun l : ℝ => (l ^ (-1 / 2 : ℝ)) ^ k) := by
    filter_upwards [gammaMeasure_ae_pos a r] with l hl
    exact (epistemic_inverseSqrt_pow hl k).symm
  exact (gammaMeasure_integrable_rpow ha hr (p := -(k : ℝ) / 2) (by linarith)).congr he

/-- Actual moments of the induced dispersion prior, with L1 proved
separately. The Gamma rate contributes r^(k/2) (Section VI). -/
theorem epistemicGammaScaleLaw_moment_pow {a r : ℝ} (ha : 0 < a) (hr : 0 < r)
    (k : ℕ) (hk : (k : ℝ) / 2 < a) :
    (∫ s : ℝ, s ^ k ∂epistemicGammaScaleLaw a r) =
      r ^ ((k : ℝ) / 2) * Real.Gamma (a - (k : ℝ) / 2) / Real.Gamma a := by
  have hm : Measurable (fun l : ℝ => l ^ (-1 / 2 : ℝ)) := by fun_prop
  have hf : Measurable (fun s : ℝ => s ^ k) := by fun_prop
  rw [epistemicGammaScaleLaw, integral_map hm.aemeasurable hf.aestronglyMeasurable]
  calc
    _ = ∫ l : ℝ, l ^ (-(k : ℝ) / 2) ∂gammaMeasure a r := by
      apply integral_congr_ae
      filter_upwards [gammaMeasure_ae_pos a r] with l hl
      exact epistemic_inverseSqrt_pow hl k
    _ = _ := by
      rw [gammaMeasure_moment_rpow ha hr (by linarith)]
      have he₁ : -(-(k : ℝ) / 2) = (k : ℝ) / 2 := by ring
      have he₂ : a + (-(k : ℝ) / 2) = a - (k : ℝ) / 2 := by ring
      rw [he₁, he₂]

/-- Section VI's genuine Normal--Gamma compound law: conditional
Gaussian variance is 1/Lambda for the actual random Gamma precision. -/
noncomputable def epistemicNormalGammaLaw (μ a r : ℝ) : Measure ℝ :=
  epistemicGaussianMixtureLaw μ (epistemicGammaScaleLaw a r)

theorem epistemicNormalGammaLaw_probability (μ : ℝ) {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    IsProbabilityMeasure (epistemicNormalGammaLaw μ a r) := by
  let := epistemicGammaScaleLaw_probability ha hr
  unfold epistemicNormalGammaLaw
  infer_instance

/-- Independent Gamma precision and Gaussian innovation generate the
whole actual compound probability measure (Section VI), before any
closed density formula or Student identification is introduced. -/
theorem epistemicNormalGammaLaw_outcome_model (μ : ℝ) {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    ((gammaMeasure a r).prod (gaussianReal 0 1)).map
      (fun p : ℝ × ℝ => μ + p.1 ^ (-1 / 2 : ℝ) * p.2) = epistemicNormalGammaLaw μ a r := by
  let := isProbabilityMeasure_gammaMeasure ha hr
  have hm : Measurable (fun l : ℝ => l ^ (-1 / 2 : ℝ)) := by fun_prop
  have ho : Measurable (fun p : ℝ × ℝ => μ + p.1 * p.2) := by fun_prop
  have he := Measure.map_prod_map (gammaMeasure a r) (gaussianReal 0 1) hm measurable_id
  rw [Measure.map_id] at he
  rw [epistemicNormalGammaLaw, ← epistemicGaussianMixtureLaw_outcome_model,
    epistemicGammaScaleLaw, he, Measure.map_map ho (hm.prodMap measurable_id)]
  rfl

/-- Actual centered compound powers are L1 when a>k/2, derived from
the independent prior and Gaussian innovation moments (Section VI). -/
theorem epistemicNormalGammaLaw_integrable_sub_pow (μ : ℝ) {a r : ℝ}
    (ha : 0 < a) (hr : 0 < r) (k : ℕ) (hk : (k : ℝ) / 2 < a) :
    Integrable (fun x : ℝ => (x - μ) ^ k) (epistemicNormalGammaLaw μ a r) :=
  epistemicGaussianMixtureLaw_integrable_sub_pow μ _ k
    (epistemicGammaScaleLaw_integrable_pow ha hr k hk)

/-- Actual compound centered moments factor into the proved Gamma
inverse moment and standard Gaussian moment, with Fubini justified
by independent L1. Positive rate and a>k/2 are explicit (Section VI). -/
theorem epistemicNormalGammaLaw_momentAbout (μ : ℝ) {a r : ℝ}
    (ha : 0 < a) (hr : 0 < r) (k : ℕ) (hk : (k : ℝ) / 2 < a) :
    (∫ x : ℝ, (x - μ) ^ k ∂epistemicNormalGammaLaw μ a r) =
      (r ^ ((k : ℝ) / 2) * Real.Gamma (a - (k : ℝ) / 2) / Real.Gamma a) *
        (∫ z : ℝ, z ^ k ∂gaussianReal 0 1) := by
  let := epistemicGammaScaleLaw_probability ha hr
  rw [epistemicNormalGammaLaw,
    epistemicGaussianMixtureLaw_momentAbout μ _ k (epistemicGammaScaleLaw_integrable_pow ha hr k hk),
    epistemicGammaScaleLaw_moment_pow ha hr k hk]

example : ∀ᵐ l ∂gammaMeasure 3 2, 0 < l := gammaMeasure_ae_pos 3 2

example : IsProbabilityMeasure (epistemicGammaScaleLaw 3 2) :=
  epistemicGammaScaleLaw_probability (by norm_num) (by norm_num)

example : ∀ᵐ s ∂epistemicGammaScaleLaw 3 2, 0 < s := epistemicGammaScaleLaw_ae_pos 3 2

example : Integrable (fun s : ℝ => s ^ 4) (epistemicGammaScaleLaw 3 2) :=
  epistemicGammaScaleLaw_integrable_pow (by norm_num) (by norm_num) 4 (by norm_num)

example : (∫ s : ℝ, s ^ 4 ∂epistemicGammaScaleLaw 3 2) =
    (2 : ℝ) ^ ((4 : ℝ) / 2) * Real.Gamma (3 - (4 : ℝ) / 2) / Real.Gamma 3 :=
  epistemicGammaScaleLaw_moment_pow (by norm_num) (by norm_num) 4 (by norm_num)

example : IsProbabilityMeasure (epistemicNormalGammaLaw 1 3 2) :=
  epistemicNormalGammaLaw_probability 1 (by norm_num) (by norm_num)

example : ((gammaMeasure 3 2).prod (gaussianReal 0 1)).map
    (fun p : ℝ × ℝ => 1 + p.1 ^ (-1 / 2 : ℝ) * p.2) = epistemicNormalGammaLaw 1 3 2 :=
  epistemicNormalGammaLaw_outcome_model 1 (by norm_num) (by norm_num)

example : Integrable (fun x : ℝ => (x - 1) ^ 4) (epistemicNormalGammaLaw 1 3 2) :=
  epistemicNormalGammaLaw_integrable_sub_pow 1 (by norm_num) (by norm_num) 4 (by norm_num)

example : (∫ x : ℝ, (x - 1) ^ 4 ∂epistemicNormalGammaLaw 1 3 2) =
    ((2 : ℝ) ^ ((4 : ℝ) / 2) * Real.Gamma (3 - (4 : ℝ) / 2) / Real.Gamma 3) *
      (∫ z : ℝ, z ^ 4 ∂gaussianReal 0 1) :=
  epistemicNormalGammaLaw_momentAbout 1 (by norm_num) (by norm_num) 4 (by norm_num)

#print axioms gammaMeasure_ae_pos
#print axioms epistemicNormalGammaLaw_probability
#print axioms epistemicNormalGammaLaw_outcome_model
#print axioms epistemicNormalGammaLaw_integrable_sub_pow
#print axioms epistemicNormalGammaLaw_momentAbout

end TailOptionPricing
