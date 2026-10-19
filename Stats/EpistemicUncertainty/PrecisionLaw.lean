module

/-
  Actual precision products on the single infinite iid error space,
  arXiv:1912.00277v2, Section V, Eqs. errorn and lerrorn. The exact
  finite-product law is identified before taking logarithms or limits.
-/
public import Stats.EpistemicUncertainty.PrecisionErrors
public import Stats.EpistemicUncertainty.SignExpansion
public import Stats.EpistemicUncertainty.ScaleConcentration

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory Finset Filter Topology

namespace TailOptionPricing

/-- Section V's precision after n actual independent multiplicative
errors; the zero-based coordinate i represents the source's error i+1. -/
def epistemicPrecisionVariable (n : ℕ) (lhat ε : ℝ) (ω : ℕ → Bool) : ℝ :=
  lhat * ∏ i : Fin n, (1 + epistemicErrorVariable ε i ω)

theorem epistemicPrecisionVariable_measurable (n : ℕ) (lhat ε : ℝ) :
    Measurable (epistemicPrecisionVariable n lhat ε) := by
  have he (i : Fin n) : Measurable (epistemicErrorVariable ε i) :=
    (measurable_of_countable (epistemicErrorSign ε)).comp (measurable_pi_apply (i : ℕ))
  unfold epistemicPrecisionVariable
  fun_prop

theorem epistemicPrecisionVariable_eq_signScale (n : ℕ) (lhat ε : ℝ) (ω : ℕ → Bool) :
    epistemicPrecisionVariable n lhat ε ω =
      epistemicSignScale n lhat (fun _ => ε) (fun i : Fin n => ω i) := by
  unfold epistemicPrecisionVariable epistemicSignScale
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  cases h : ω i <;> simp [epistemicErrorVariable, epistemicErrorSign, h, sub_eq_add_neg]

/-- The true law of Section V's product on the infinite iid sample
space. This is a pushforward of the process, not a moment formula. -/
noncomputable def epistemicPrecisionLaw (n : ℕ) (lhat ε : ℝ) : Measure ℝ :=
  epistemicInfiniteSignLaw.map (epistemicPrecisionVariable n lhat ε)

instance epistemicPrecisionLaw_probability (n : ℕ) (lhat ε : ℝ) :
    IsProbabilityMeasure (epistemicPrecisionLaw n lhat ε) := by
  unfold epistemicPrecisionLaw
  exact (Measure.isProbabilityMeasure_map_iff
    (epistemicPrecisionVariable_measurable n lhat ε).aemeasurable).mpr inferInstance

/-- The actual iid precision product has the same whole measure as
the already constructed fair multiplicative scale law (Sections III,V). -/
theorem epistemicPrecisionLaw_eq_scaleLaw (n : ℕ) (lhat ε : ℝ) :
    epistemicPrecisionLaw n lhat ε = epistemicScaleLaw n lhat ε := by
  have hp : Measurable (fun ω : ℕ → Bool => fun i : Fin n => ω i) := by fun_prop
  rw [← epistemicLayerScaleLaw_const n lhat ε, epistemicLayerScaleLaw_eq_sign_map,
    ← epistemicInfiniteSignLaw_prefix n,
    Measure.map_map (measurable_of_countable _) hp]
  unfold epistemicPrecisionLaw
  congr 1
  funext ω
  exact epistemicPrecisionVariable_eq_signScale n lhat ε ω

/-- The actual precision remains unbiased despite the drift of its
logarithm; Section V's mean-zero errors alone do not center log precision. -/
theorem epistemicPrecisionLaw_mean (n : ℕ) (lhat ε : ℝ) :
    (∫ l : ℝ, l ∂epistemicPrecisionLaw n lhat ε) = lhat := by
  rw [epistemicPrecisionLaw_eq_scaleLaw, epistemicScaleLaw_mean]

theorem epistemicPrecisionLaw_ae_pos (n : ℕ) {lhat ε : ℝ}
    (hl : 0 < lhat) (hε₀ : 0 ≤ ε) (hε₁ : ε < 1) :
    ∀ᵐ l ∂epistemicPrecisionLaw n lhat ε, 0 < l := by
  rw [epistemicPrecisionLaw_eq_scaleLaw]
  exact epistemicScaleLaw_ae_pos n hl hε₀ hε₁

/-- Actual logarithm of the positive precision product, Section V's
Eq. lerrorn, prior to the source's linearization or CLT approximation. -/
noncomputable def epistemicLogPrecisionLaw (n : ℕ) (lhat ε : ℝ) : Measure ℝ :=
  (epistemicPrecisionLaw n lhat ε).map Real.log

instance epistemicLogPrecisionLaw_probability (n : ℕ) (lhat ε : ℝ) :
    IsProbabilityMeasure (epistemicLogPrecisionLaw n lhat ε) := by
  unfold epistemicLogPrecisionLaw
  exact (Measure.isProbabilityMeasure_map_iff Real.measurable_log.aemeasurable).mpr inferInstance

/-- On the actual positive product law, the log-precision upper tail
at zero equals the precision upper tail at one (Section V). -/
theorem epistemicLogPrecisionLaw_real_Ici_zero (n : ℕ) {lhat ε : ℝ}
    (hl : 0 < lhat) (hε₀ : 0 ≤ ε) (hε₁ : ε < 1) :
    (epistemicLogPrecisionLaw n lhat ε).real (Ici 0) =
      (epistemicScaleLaw n lhat ε).real (Ici 1) := by
  have he : Real.log ⁻¹' Ici 0 =ᵐ[epistemicPrecisionLaw n lhat ε] Ici 1 := by
    filter_upwards [epistemicPrecisionLaw_ae_pos n hl hε₀ hε₁] with l hl
    exact propext (Real.log_nonneg_iff hl)
  simp only [epistemicLogPrecisionLaw, measureReal_def,
    Measure.map_apply Real.measurable_log measurableSet_Ici]
  rw [measure_congr he, epistemicPrecisionLaw_eq_scaleLaw]

/-- Fixed, arbitrarily small nonzero iid mean-zero multiplicative
errors force P(log precision >= 0) to zero, not one half. This is
the exact product law in Section V with initial precision one. -/
theorem epistemicLogPrecisionLaw_tail_tendsto_zero {ε : ℝ} (hε₀ : 0 < ε) (hε₁ : ε < 1) :
    Tendsto (fun n => (epistemicLogPrecisionLaw n 1 ε).real (Ici 0)) atTop (𝓝 0) := by
  have he (n : ℕ) := epistemicLogPrecisionLaw_real_Ici_zero n
    (show (0 : ℝ) < 1 by norm_num) hε₀.le hε₁
  simp_rw [he]
  exact epistemicScaleLaw_tail_tendsto_zero (by norm_num) hε₀ hε₁ (by norm_num)

example : (∫ l : ℝ, l ∂epistemicPrecisionLaw 3 1 (1 / 100)) = 1 :=
  epistemicPrecisionLaw_mean _ _ _

example : ∀ᵐ l ∂epistemicPrecisionLaw 3 1 (1 / 100), 0 < l :=
  epistemicPrecisionLaw_ae_pos _ (by norm_num) (by norm_num) (by norm_num)

example : (epistemicLogPrecisionLaw 3 1 (1 / 100)).real (Ici 0) =
    (epistemicScaleLaw 3 1 (1 / 100)).real (Ici 1) :=
  epistemicLogPrecisionLaw_real_Ici_zero _ (by norm_num) (by norm_num) (by norm_num)

example : Tendsto (fun n => (epistemicLogPrecisionLaw n 1 (1 / 100)).real (Ici 0))
    atTop (𝓝 0) := epistemicLogPrecisionLaw_tail_tendsto_zero (by norm_num) (by norm_num)

#print axioms epistemicPrecisionLaw_eq_scaleLaw
#print axioms epistemicPrecisionLaw_ae_pos
#print axioms epistemicLogPrecisionLaw_real_Ici_zero
#print axioms epistemicLogPrecisionLaw_tail_tendsto_zero

end TailOptionPricing
