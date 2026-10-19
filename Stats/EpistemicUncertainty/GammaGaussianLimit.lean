module

/-
  Weak Gaussian boundary limit of the actual matched Normal--Gamma
  laws of arXiv:1912.00277v2, Section VI, Eq. compoundGamma.
  Positive epistemic log variances tend to zero. The actual Gamma
  precision concentrates at one, its dispersion does likewise,
  and the independent Gaussian generator gives the whole-law limit.
  The singular Gamma formulas at variance zero are never treated as
  a probability law. The limiting Gaussian has variance one.
-/
public import Stats.EpistemicUncertainty.GammaConcentration
public import Stats.EpistemicUncertainty.GammaOutcomeTail
public import Mathlib.MeasureTheory.Measure.FiniteMeasureProd

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory Filter Topology

namespace TailOptionPricing

/-- The actual matched Gamma precision probability measure (Section VI).
Positive epistemic log variance ensures proper shape and rate. -/
noncomputable def epistemicMatchedGammaPrecisionProba (v : ℝ) (hv : 0 < v) :
    ProbabilityMeasure ℝ :=
  ⟨gammaMeasure (epistemicGammaMatchShape v) (epistemicGammaMatchRate v),
    epistemicGammaMatch_probability hv⟩

/-- Actual matched dispersion, bundled using its proved normalization.
The positive parameter is Section VI's epistemic log variance. -/
noncomputable def epistemicMatchedGammaScaleProba (v : ℝ) (hv : 0 < v) :
    ProbabilityMeasure ℝ :=
  ⟨epistemicGammaScaleLaw (epistemicGammaMatchShape v) (epistemicGammaMatchRate v),
    epistemicGammaScaleLaw_probability
      (epistemicGammaMatchShape_pos hv) (epistemicGammaMatchRate_pos hv)⟩

/-- Actual matched output population, with the source's Gamma rate
convention and the corrected Student scale (Section VI). -/
noncomputable def epistemicMatchedGammaOutcomeProba (μ v : ℝ) (hv : 0 < v) :
    ProbabilityMeasure ℝ :=
  ⟨epistemicMatchedGammaOutcomeLaw μ v, epistemicMatchedGammaOutcomeLaw_probability μ hv⟩

/-- Section VI's actual matched precision laws converge weakly to
Dirac(1) as positive epistemic log variance tends to zero. -/
theorem epistemicMatchedGammaPrecisionProba_tendsto_dirac {ι : Type*} {l : Filter ι}
    [l.IsCountablyGenerated] [NeBot l] {v : ι → ℝ}
    (hv : ∀ i, 0 < v i) (hv₀ : Tendsto v l (𝓝 0)) :
    Tendsto (fun i => epistemicMatchedGammaPrecisionProba (v i) (hv i)) l
      (𝓝 (⟨Measure.dirac 1, inferInstance⟩ : ProbabilityMeasure ℝ)) := by
  apply probabilityMeasure_tendsto_dirac_of_concentration
  intro δ hδ
  exact epistemicGammaMatch_tail_tendsto_zero hv hv₀ hδ

/-- Actual matched dispersions concentrate at one. The precision-to-
dispersion map is continuous at one; its singularity at zero does not
enter this concentration argument (Section VI's Gaussian boundary). -/
theorem epistemicMatchedGammaScale_tail_tendsto_zero {ι : Type*} {l : Filter ι}
    {v : ι → ℝ} (hv : ∀ i, 0 < v i) (hv₀ : Tendsto v l (𝓝 0))
    {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun i => (epistemicGammaScaleLaw (epistemicGammaMatchShape (v i))
      (epistemicGammaMatchRate (v i))).real {s | δ ≤ |s - 1|}) l (𝓝 0) := by
  let : ∀ i, IsFiniteMeasure
      (gammaMeasure (epistemicGammaMatchShape (v i)) (epistemicGammaMatchRate (v i))) :=
    fun i => by
      let := epistemicGammaMatch_probability (hv i)
      infer_instance
  have hc : ContinuousAt (fun x : ℝ => x ^ (-1 / 2 : ℝ)) 1 :=
    Real.continuousAt_rpow_const _ _ (Or.inl one_ne_zero)
  have ht := measureReal_map_abs_sub_ge_tendsto_zero
    (μs := fun i => gammaMeasure (epistemicGammaMatchShape (v i))
      (epistemicGammaMatchRate (v i))) (by fun_prop) hc
        (fun ε hε => epistemicGammaMatch_tail_tendsto_zero hv hv₀ hε) hδ
  simpa only [epistemicGammaScaleLaw, Real.one_rpow] using ht

/-- The actual matched dispersion laws converge weakly to Dirac(1)
along every positive-variance family tending to zero. This proves the
whole-prior limit before mapping through the Gaussian generator. -/
theorem epistemicMatchedGammaScaleProba_tendsto_dirac {ι : Type*} {l : Filter ι}
    [l.IsCountablyGenerated] [NeBot l] {v : ι → ℝ}
    (hv : ∀ i, 0 < v i) (hv₀ : Tendsto v l (𝓝 0)) :
    Tendsto (fun i => epistemicMatchedGammaScaleProba (v i) (hv i)) l
      (𝓝 (⟨Measure.dirac 1, inferInstance⟩ : ProbabilityMeasure ℝ)) := by
  apply probabilityMeasure_tendsto_dirac_of_concentration
  intro δ hδ
  exact epistemicMatchedGammaScale_tail_tendsto_zero hv hv₀ hδ

/-- Actual weak Gaussian limit at Section VI's zero-uncertainty
boundary. For every positive log-variance family tending to zero,
the matched Gamma compounds tend to Normal(mu,1). Scalar limits of
the degrees of freedom and scale are not assumed to imply this limit:
it follows from actual precision concentration and the independent
Gaussian outcome model in Eq. compoundGamma. -/
theorem epistemicMatchedGammaOutcomeProba_tendsto_gaussian {ι : Type*} {l : Filter ι}
    [l.IsCountablyGenerated] [NeBot l] (μ : ℝ) {v : ι → ℝ}
    (hv : ∀ i, 0 < v i) (hv₀ : Tendsto v l (𝓝 0)) :
    Tendsto (fun i => epistemicMatchedGammaOutcomeProba μ (v i) (hv i)) l
      (𝓝 (⟨gaussianReal μ 1, inferInstance⟩ : ProbabilityMeasure ℝ)) := by
  let g : ProbabilityMeasure ℝ := ⟨gaussianReal 0 1, inferInstance⟩
  let d : ProbabilityMeasure ℝ := ⟨Measure.dirac 1, inferInstance⟩
  have hs : Tendsto (fun i => epistemicMatchedGammaScaleProba (v i) (hv i)) l (𝓝 d) :=
    epistemicMatchedGammaScaleProba_tendsto_dirac hv hv₀
  have hp : Tendsto (fun i => (epistemicMatchedGammaScaleProba (v i) (hv i)).prod g) l
      (𝓝 (d.prod g)) :=
    ProbabilityMeasure.continuous_prod.continuousAt.tendsto.comp
      (hs.prodMk_nhds tendsto_const_nhds)
  have hc : Continuous (fun p : ℝ × ℝ => μ + p.1 * p.2) :=
    continuous_const.add (continuous_fst.mul continuous_snd)
  have ht := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hp hc
  have he (i : ι) : ((epistemicMatchedGammaScaleProba (v i) (hv i)).prod g).map
      (fun p : ℝ × ℝ => μ + p.1 * p.2) = epistemicMatchedGammaOutcomeProba μ (v i) (hv i) := by
    apply Subtype.ext
    exact epistemicGaussianMixtureLaw_outcome_model μ _
  have hd : (d.prod g).map (fun p : ℝ × ℝ => μ + p.1 * p.2) =
      (⟨gaussianReal μ 1, inferInstance⟩ : ProbabilityMeasure ℝ) := by
    apply Subtype.ext
    change ((Measure.dirac (1 : ℝ)).prod (gaussianReal 0 1)).map
      (fun p : ℝ × ℝ => μ + p.1 * p.2) = gaussianReal μ 1
    rw [Measure.dirac_prod, Measure.map_map hc.measurable measurable_prodMk_left]
    change (gaussianReal 0 1).map (fun x : ℝ => μ + 1 * x) = gaussianReal μ 1
    simpa only [one_pow, NNReal.mk_one] using gaussianReal_map_affine_scale μ 1
  simpa only [he, hd] using ht

/-- The right boundary limit on the full domain of positive epistemic
log variances, not just on one chosen sequence (Section VI). The pulled-
back neighborhood filter restricts v to positive reals approaching zero. -/
theorem epistemicMatchedGammaOutcomeProba_tendsto_gaussian_right (μ : ℝ) :
    Tendsto (fun v : Ioi (0 : ℝ) => epistemicMatchedGammaOutcomeProba μ v v.property)
      (comap (fun v : Ioi (0 : ℝ) => (v : ℝ)) (𝓝 0))
        (𝓝 (⟨gaussianReal μ 1, inferInstance⟩ : ProbabilityMeasure ℝ)) := by
  have h₀ : (0 : ℝ) ∈ closure (Ioi (0 : ℝ)) := by
    rw [closure_Ioi]
    exact le_rfl
  let := mem_closure_iff_comap_neBot.mp h₀
  exact epistemicMatchedGammaOutcomeProba_tendsto_gaussian μ (fun v => v.property) tendsto_comap

example : Tendsto (fun n : ℕ => epistemicMatchedGammaPrecisionProba
    (Real.exp (-(n : ℝ))) (Real.exp_pos _)) atTop
      (𝓝 (⟨Measure.dirac 1, inferInstance⟩ : ProbabilityMeasure ℝ)) :=
  epistemicMatchedGammaPrecisionProba_tendsto_dirac (fun _ => Real.exp_pos _)
    (Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop)

example : Tendsto (fun n : ℕ =>
    (epistemicGammaScaleLaw (epistemicGammaMatchShape (Real.exp (-(n : ℝ))))
      (epistemicGammaMatchRate (Real.exp (-(n : ℝ))))).real {s | 1 ≤ |s - 1|})
        atTop (𝓝 0) :=
  epistemicMatchedGammaScale_tail_tendsto_zero (fun _ => Real.exp_pos _)
    (Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop) (by norm_num)

example : Tendsto (fun n : ℕ => epistemicMatchedGammaScaleProba
    (Real.exp (-(n : ℝ))) (Real.exp_pos _)) atTop
      (𝓝 (⟨Measure.dirac 1, inferInstance⟩ : ProbabilityMeasure ℝ)) :=
  epistemicMatchedGammaScaleProba_tendsto_dirac (fun _ => Real.exp_pos _)
    (Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop)

example : Tendsto (fun n : ℕ => epistemicMatchedGammaOutcomeProba 2
    (Real.exp (-(n : ℝ))) (Real.exp_pos _)) atTop
      (𝓝 (⟨gaussianReal 2 1, inferInstance⟩ : ProbabilityMeasure ℝ)) :=
  epistemicMatchedGammaOutcomeProba_tendsto_gaussian 2 (fun _ => Real.exp_pos _)
    (Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop)

#print axioms epistemicMatchedGammaScale_tail_tendsto_zero
#print axioms epistemicMatchedGammaPrecisionProba_tendsto_dirac
#print axioms epistemicMatchedGammaScaleProba_tendsto_dirac
#print axioms epistemicMatchedGammaOutcomeProba_tendsto_gaussian
#print axioms epistemicMatchedGammaOutcomeProba_tendsto_gaussian_right

end TailOptionPricing
