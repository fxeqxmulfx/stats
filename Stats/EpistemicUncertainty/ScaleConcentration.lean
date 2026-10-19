module

/-
  Actual dispersion concentration in the constant-error model of
  arXiv:1912.00277v2, Section III. Fractional moments yield shrinking
  tail probabilities and weak convergence of the dispersion laws to
  a point mass at zero, despite their fixed positive first moment.
  The corresponding outcome-law limit is a separate mapping step.
-/
public import Stats.EpistemicUncertainty.FractionalMoments
public import Mathlib.MeasureTheory.Measure.Portmanteau

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory Filter Topology

namespace TailOptionPricing

/-- Actual Markov bound for the positive dispersion in Section III.
Every real-order dispersion power is L1 under its finite actual law. -/
theorem epistemicScaleLaw_tail_le (n : ℕ) {σ ε δ p : ℝ} (hσ : 0 < σ)
    (hε₀ : 0 ≤ ε) (hε₁ : ε < 1) (hδ : 0 < δ) (hp : 0 < p) :
    (epistemicScaleLaw n σ ε).real (Ici δ) ≤
      (∫ s : ℝ, s ^ p ∂epistemicScaleLaw n σ ε) / δ ^ p := by
  have hs := epistemicScaleLaw_ae_pos n hσ hε₀ hε₁
  have hn : 0 ≤ᵐ[epistemicScaleLaw n σ ε] (fun s : ℝ => s ^ p) :=
    hs.mono (fun s hs => Real.rpow_nonneg hs.le p)
  have he : {s : ℝ | δ ^ p ≤ s ^ p} =ᵐ[epistemicScaleLaw n σ ε] Ici δ := by
    filter_upwards [hs] with s hs
    exact propext (Real.rpow_le_rpow_iff hδ.le hs.le hp)
  have hm := mul_meas_ge_le_integral_of_nonneg hn
    (epistemicScaleLaw_integrable n σ ε _) (δ ^ p)
  rw [measureReal_congr he] at hm
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hδ p)).mpr
  simpa only [mul_comm] using hm

/-- For every fixed positive threshold, the actual dispersion's tail
probability tends to zero (Section III's depth limit). The proof uses
an actual half-order moment, rather than its growing second moment. -/
theorem epistemicScaleLaw_tail_tendsto_zero {σ ε δ : ℝ} (hσ : 0 < σ)
    (hε₀ : 0 < ε) (hε₁ : ε < 1) (hδ : 0 < δ) :
    Tendsto (fun n => (epistemicScaleLaw n σ ε).real (Ici δ)) atTop (𝓝 0) := by
  have ht := (epistemicScaleLaw_fractional_moment_tendsto_zero
    hσ hε₀ hε₁ (show (0 : ℝ) < 1 / 2 by norm_num)
    (show (1 / 2 : ℝ) < 1 by norm_num)).div_const (δ ^ (1 / 2 : ℝ))
  apply squeeze_zero (fun _ => measureReal_nonneg)
    (fun n => epistemicScaleLaw_tail_le n hσ hε₀.le hε₁ hδ
      (show (0 : ℝ) < 1 / 2 by norm_num))
  simpa only [zero_div] using ht

/-- Actual dispersion laws bundled with their proved normalization,
so their weak limit is a statement in the probability-measure topology. -/
noncomputable def epistemicScaleProba (n : ℕ) (σ ε : ℝ) : ProbabilityMeasure ℝ :=
  ⟨epistemicScaleLaw n σ ε, inferInstance⟩

/-- The actual dispersion laws converge weakly to a point mass at zero
for fixed positive base scale and error in (0,1). This is a precise
depth-limit result for Section III, independent of moment divergence. -/
theorem epistemicScaleProba_tendsto_dirac {σ ε : ℝ} (hσ : 0 < σ)
    (hε₀ : 0 < ε) (hε₁ : ε < 1) :
    Tendsto (fun n => epistemicScaleProba n σ ε) atTop
      (𝓝 (⟨Measure.dirac 0, inferInstance⟩ : ProbabilityMeasure ℝ)) := by
  apply tendsto_of_forall_isClosed_limsup_real_le'
  intro F hF
  change limsup (fun n => (epistemicScaleLaw n σ ε).real F) atTop ≤
    (Measure.dirac (0 : ℝ)).real F
  by_cases h0 : 0 ∈ F
  · have hd : (Measure.dirac (0 : ℝ)).real F = 1 := by
      simp [measureReal_def, Measure.dirac_apply' _ hF.measurableSet, h0]
    rw [hd]
    exact Filter.limsup_le_of_le
      (Filter.isCoboundedUnder_le_of_le atTop (fun n =>
        (show (0 : ℝ) ≤ (epistemicScaleLaw n σ ε).real F from measureReal_nonneg)))
      (Eventually.of_forall (fun _ => measureReal_le_one))
  · have hd : (Measure.dirac (0 : ℝ)).real F = 0 := by
      simp [measureReal_def, Measure.dirac_apply' _ hF.measurableSet, h0]
    rw [hd]
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (hF.isOpen_compl.mem_nhds h0)
    have hsub : F ∩ Ioi (0 : ℝ) ⊆ Ici δ := by
      intro s hs
      by_contra hn
      have hsδ : s < δ := lt_of_not_ge hn
      have hb : s ∈ Metric.ball (0 : ℝ) δ := by
        simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hs.2] using hsδ
      exact (hball hb) hs.1
    have hbound (n : ℕ) : (epistemicScaleLaw n σ ε).real F ≤
        (epistemicScaleLaw n σ ε).real (Ici δ) := by
      have he : F =ᵐ[epistemicScaleLaw n σ ε] F ∩ Ioi (0 : ℝ) := by
        filter_upwards [epistemicScaleLaw_ae_pos n hσ hε₀.le hε₁] with s hs
        simp only [mem_inter_iff, mem_Ioi, hs, and_true]
      rw [measureReal_congr he]
      exact measureReal_mono hsub
    have ht : Tendsto (fun n => (epistemicScaleLaw n σ ε).real F) atTop (𝓝 0) :=
      squeeze_zero (fun _ => measureReal_nonneg) hbound
        (epistemicScaleLaw_tail_tendsto_zero hσ hε₀ hε₁ hδ)
    exact ht.limsup_eq.le

example : (epistemicScaleLaw 2 2 (1 / 2)).real (Ici 1) ≤
    (∫ s : ℝ, s ^ (1 / 2 : ℝ) ∂epistemicScaleLaw 2 2 (1 / 2)) / (1 : ℝ) ^ (1 / 2 : ℝ) :=
  epistemicScaleLaw_tail_le _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

example : Tendsto (fun n => (epistemicScaleLaw n 2 (1 / 2)).real (Ici 1)) atTop (𝓝 0) :=
  epistemicScaleLaw_tail_tendsto_zero (by norm_num) (by norm_num) (by norm_num) (by norm_num)

example : Tendsto (fun n => epistemicScaleProba n 2 (1 / 2)) atTop
    (𝓝 (⟨Measure.dirac 0, inferInstance⟩ : ProbabilityMeasure ℝ)) :=
  epistemicScaleProba_tendsto_dirac (by norm_num) (by norm_num) (by norm_num)

#print axioms epistemicScaleLaw_tail_le
#print axioms epistemicScaleLaw_tail_tendsto_zero
#print axioms epistemicScaleProba_tendsto_dirac

end TailOptionPricing
