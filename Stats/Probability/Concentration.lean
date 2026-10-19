module

/-
  Concentration at a real point and weak probability limits. These
  elementary Markov and Portmanteau steps support the zero-uncertainty
  boundary of arXiv:1912.00277v2, Section VI. A transform need only be
  continuous at the concentration point, rather than on the whole line.
-/
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory Filter Topology

namespace TailOptionPricing

/-- Squared-distance Markov bound for an actual real measure.
Used for the precision concentration in Section VI. -/
theorem measureReal_abs_sub_ge_le_integral_sq {μ : Measure ℝ} {c δ : ℝ}
    (hδ : 0 < δ) (hi : Integrable (fun x : ℝ => (x - c) ^ 2) μ) :
    μ.real {x | δ ≤ |x - c|} ≤ (∫ x, (x - c) ^ 2 ∂μ) / δ ^ 2 := by
  have he : {x : ℝ | δ ^ 2 ≤ (x - c) ^ 2} = {x | δ ≤ |x - c|} := by
    ext x
    change δ ^ 2 ≤ (x - c) ^ 2 ↔ δ ≤ |x - c|
    rw [← sq_abs (x - c), sq_le_sq₀ hδ.le (abs_nonneg _)]
  have hm := mul_meas_ge_le_integral_of_nonneg
    (Eventually.of_forall (fun x : ℝ => sq_nonneg (x - c))) hi (δ ^ 2)
  rw [he] at hm
  exact (le_div_iff₀ (sq_pos_of_pos hδ)).mpr (by simpa only [mul_comm] using hm)

/-- A vanishing actual squared-distance moment forces concentration
at every fixed positive radius. No probability normalization is needed
for this Markov implication, used for Section VI's matched prior. -/
theorem measureReal_abs_sub_ge_tendsto_zero_of_integral_sq {ι : Type*} {l : Filter ι}
    {μs : ι → Measure ℝ} {c : ℝ}
    (hi : ∀ i, Integrable (fun x : ℝ => (x - c) ^ 2) (μs i))
    (ht : Tendsto (fun i => ∫ x, (x - c) ^ 2 ∂μs i) l (𝓝 0))
    {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun i => (μs i).real {x | δ ≤ |x - c|}) l (𝓝 0) := by
  apply squeeze_zero (fun _ => measureReal_nonneg)
    (fun i => measureReal_abs_sub_ge_le_integral_sq hδ (hi i))
  simpa only [zero_div] using ht.div_const (δ ^ 2)

/-- Concentration transfers through a measurable real transform that
is continuous at the concentration point. No global continuity, or
moment of the transformed variable, is assumed (Section VI). -/
theorem measureReal_map_abs_sub_ge_tendsto_zero {ι : Type*} {l : Filter ι}
    {μs : ι → Measure ℝ} [∀ i, IsFiniteMeasure (μs i)] {c : ℝ} {f : ℝ → ℝ}
    (hf : Measurable f) (hc : ContinuousAt f c)
    (h : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun i => (μs i).real {x | ε ≤ |x - c|}) l (𝓝 0))
    {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun i => ((μs i).map f).real {y | δ ≤ |y - f c|}) l (𝓝 0) := by
  obtain ⟨ε, hε, he⟩ := Metric.continuousAt_iff.mp hc δ hδ
  have hs : MeasurableSet {y : ℝ | δ ≤ |y - f c|} := by measurability
  have hsub : f ⁻¹' {y : ℝ | δ ≤ |y - f c|} ⊆ {x | ε ≤ |x - c|} := by
    intro x hx
    by_contra hn
    have hb : dist x c < ε := by simpa only [Real.dist_eq] using lt_of_not_ge hn
    have he' : |f x - f c| < δ := by simpa only [Real.dist_eq] using he hb
    exact (not_lt_of_ge hx) he'
  apply squeeze_zero (fun _ => measureReal_nonneg) _ (h ε hε)
  intro i
  change (((μs i).map f) {y | δ ≤ |y - f c|}).toReal ≤ _
  rw [Measure.map_apply hf hs]
  exact measureReal_mono hsub

/-- Vanishing probabilities outside every ball about c imply actual
weak convergence to Dirac(c). The closed-set Portmanteau bound is proved
directly, without assuming a law limit from parameter convergence. -/
theorem probabilityMeasure_tendsto_dirac_of_concentration {ι : Type*} {l : Filter ι}
    [l.IsCountablyGenerated] [NeBot l] {μs : ι → ProbabilityMeasure ℝ} {c : ℝ}
    (h : ∀ δ : ℝ, 0 < δ →
      Tendsto (fun i => (μs i : Measure ℝ).real {x | δ ≤ |x - c|}) l (𝓝 0)) :
    Tendsto μs l (𝓝 (⟨Measure.dirac c, inferInstance⟩ : ProbabilityMeasure ℝ)) := by
  apply tendsto_of_forall_isClosed_limsup_real_le'
  intro F hF
  change limsup (fun i => (μs i : Measure ℝ).real F) l ≤ (Measure.dirac c).real F
  by_cases hc : c ∈ F
  · have hd : (Measure.dirac c).real F = 1 := by
      simp [measureReal_def, Measure.dirac_apply' _ hF.measurableSet, hc]
    rw [hd]
    exact Filter.limsup_le_of_le
      (Filter.isCoboundedUnder_le_of_le l (fun i =>
        (show (0 : ℝ) ≤ (μs i : Measure ℝ).real F from measureReal_nonneg)))
      (Eventually.of_forall (fun _ => measureReal_le_one))
  · have hd : (Measure.dirac c).real F = 0 := by
      simp [measureReal_def, Measure.dirac_apply' _ hF.measurableSet, hc]
    rw [hd]
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (hF.isOpen_compl.mem_nhds hc)
    have hsub : F ⊆ {x : ℝ | δ ≤ |x - c|} := by
      intro x hx
      by_contra hn
      have hb : x ∈ Metric.ball c δ := by
        simpa only [Metric.mem_ball, Real.dist_eq] using lt_of_not_ge hn
      exact (hball hb) hx
    have ht : Tendsto (fun i => (μs i : Measure ℝ).real F) l (𝓝 0) :=
      squeeze_zero (fun _ => measureReal_nonneg) (fun _ => measureReal_mono hsub) (h δ hδ)
    exact ht.limsup_eq.le

/-- A vanishing squared-distance moment gives a weak point-mass limit
for actual probability laws. This combines the two independently
proved steps, Markov concentration and closed-set Portmanteau. -/
theorem probabilityMeasure_tendsto_dirac_of_integral_sq {ι : Type*} {l : Filter ι}
    [l.IsCountablyGenerated] [NeBot l] {μs : ι → ProbabilityMeasure ℝ} {c : ℝ}
    (hi : ∀ i, Integrable (fun x : ℝ => (x - c) ^ 2) (μs i : Measure ℝ))
    (ht : Tendsto (fun i => ∫ x, (x - c) ^ 2 ∂(μs i : Measure ℝ)) l (𝓝 0)) :
    Tendsto μs l (𝓝 (⟨Measure.dirac c, inferInstance⟩ : ProbabilityMeasure ℝ)) := by
  apply probabilityMeasure_tendsto_dirac_of_concentration
  intro δ hδ
  exact measureReal_abs_sub_ge_tendsto_zero_of_integral_sq hi ht hδ

example : (Measure.dirac (1 : ℝ)).real {x | 2 ≤ |x - 1|} ≤
    (∫ x : ℝ, (x - 1) ^ 2 ∂Measure.dirac 1) / 2 ^ 2 :=
  measureReal_abs_sub_ge_le_integral_sq (by norm_num) (integrable_dirac (by simp))

example : Tendsto (fun _ : ℕ => (Measure.dirac (1 : ℝ)).real
    {x | 2 ≤ |x - 1|}) atTop (𝓝 0) := by
  apply measureReal_abs_sub_ge_tendsto_zero_of_integral_sq
    (fun _ => integrable_dirac (by simp)) _ (by norm_num)
  simpa only [integral_dirac, sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

example : Tendsto (fun _ : ℕ => ((Measure.dirac (1 : ℝ)).map
    (fun x : ℝ => x + 2)).real {y | 1 ≤ |y - (1 + 2)|}) atTop (𝓝 0) := by
  apply measureReal_map_abs_sub_ge_tendsto_zero (by fun_prop) (by fun_prop) _ (by norm_num)
  intro ε hε
  have he : (Measure.dirac (1 : ℝ)).real {x | ε ≤ |x - 1|} = 0 := by
    simp [measureReal_def, Measure.dirac_apply', (show MeasurableSet {x : ℝ | ε ≤ |x - 1|}
      by measurability), not_le.mpr hε]
  simpa only [he] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

example : ∃ ρ : ProbabilityMeasure ℝ, (ρ : Measure ℝ) = Measure.dirac 1 ∧
    Tendsto (fun _ : ℕ => ρ) atTop (𝓝 ρ) := by
  let ρ : ProbabilityMeasure ℝ := ⟨Measure.dirac 1, inferInstance⟩
  refine ⟨ρ, rfl, ?_⟩
  apply probabilityMeasure_tendsto_dirac_of_concentration
  intro δ hδ
  change Tendsto (fun _ : ℕ => (Measure.dirac (1 : ℝ)).real {x | δ ≤ |x - 1|}) atTop (𝓝 0)
  have he : (Measure.dirac (1 : ℝ)).real {x | δ ≤ |x - 1|} = 0 := by
    simp [measureReal_def, Measure.dirac_apply', (show MeasurableSet {x : ℝ | δ ≤ |x - 1|}
      by measurability), not_le.mpr hδ]
  simpa only [he] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

#print axioms measureReal_abs_sub_ge_le_integral_sq
#print axioms measureReal_abs_sub_ge_tendsto_zero_of_integral_sq
#print axioms measureReal_map_abs_sub_ge_tendsto_zero
#print axioms probabilityMeasure_tendsto_dirac_of_concentration

example : ∃ ρ : ProbabilityMeasure ℝ, (ρ : Measure ℝ) = Measure.dirac 3 ∧
    Tendsto (fun _ : ℕ => ρ) atTop (𝓝 ρ) := by
  let ρ : ProbabilityMeasure ℝ := ⟨Measure.dirac 3, inferInstance⟩
  refine ⟨ρ, rfl, ?_⟩
  apply probabilityMeasure_tendsto_dirac_of_integral_sq
    (fun _ => integrable_dirac (by simp))
  change Tendsto (fun _ : ℕ => ∫ x : ℝ, (x - 3) ^ 2 ∂Measure.dirac 3) atTop (𝓝 0)
  simpa only [integral_dirac, sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

#print axioms probabilityMeasure_tendsto_dirac_of_integral_sq

end TailOptionPricing
