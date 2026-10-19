module

/-
  Actual conditional uncertainty hierarchies, arXiv:1912.00277v2,
  Section II's nested scale mixtures. Each stage samples a measurable
  conditional probability law from the previous positive dispersion.
  Finite normalization and positive support are proved independently
  of the subsequent marginal-density and iterated-integral identities.
-/
public import Stats.EpistemicUncertainty.GaussianKernel

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory

namespace TailOptionPricing

/-- The fair two-branch scale transition of Section II as an actual
measurable conditional kernel. Both conditional atoms depend on the
incoming dispersion; this is a nonconstant uncertainty transition. -/
noncomputable def epistemicFairScaleKernel (ε : ℝ) : Kernel ℝ ℝ where
  toFun s := equalMixture (Measure.dirac (s * (1 + ε))) (Measure.dirac (s * (1 - ε)))
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro A hA
    simp only [equalMixture, Measure.add_apply, Measure.smul_apply, smul_eq_mul,
      Measure.dirac_apply' _ hA]
    have hc : Measurable (A.indicator (fun _ : ℝ => (1 : ENNReal))) :=
      measurable_const.indicator hA
    exact (measurable_const.mul (hc.comp (measurable_id.mul_const (1 + ε)))).add
      (measurable_const.mul (hc.comp (measurable_id.mul_const (1 - ε))))

instance epistemicFairScaleKernel_markov (ε : ℝ) :
    IsMarkovKernel (epistemicFairScaleKernel ε) := by
  constructor
  intro s
  change IsProbabilityMeasure
    (equalMixture (Measure.dirac (s * (1 + ε))) (Measure.dirac (s * (1 - ε))))
  infer_instance

/-- Each actual fair transition preserves positive scale on the
source domain 0<=epsilon<1 (Section II). -/
theorem epistemicFairScaleKernel_ae_pos {ε s : ℝ} (hs : 0 < s)
    (hε₀ : 0 ≤ ε) (hε₁ : ε < 1) :
    ∀ᵐ t ∂epistemicFairScaleKernel ε s, 0 < t := by
  have hp : ∀ᵐ t ∂Measure.dirac (s * (1 + ε)), 0 < t := by
    simpa only [ae_dirac_iff measurableSet_Ioi] using mul_pos hs (show 0 < 1 + ε by linarith)
  have hn : ∀ᵐ t ∂Measure.dirac (s * (1 - ε)), 0 < t := by
    simpa only [ae_dirac_iff measurableSet_Ioi] using mul_pos hs (show 0 < 1 - ε by linarith)
  change ∀ᵐ t ∂equalMixture (Measure.dirac (s * (1 + ε))) (Measure.dirac (s * (1 - ε))), 0 < t
  rw [equalMixture, ae_add_measure_iff]
  exact ⟨Measure.ae_smul_measure hp _, Measure.ae_smul_measure hn _⟩

private theorem hierarchy_bind_ae_pos (ν : Measure ℝ) (κ : Kernel ℝ ℝ)
    (hν : ∀ᵐ s ∂ν, 0 < s) (hκ : ∀ s, 0 < s → ∀ᵐ t ∂κ s, 0 < t) :
    ∀ᵐ t ∂ν.bind κ, 0 < t := by
  have he : {t : ℝ | ¬0 < t} = Iic (0 : ℝ) := by
    ext t
    simp only [Set.mem_ofPred_eq, Set.mem_Iic, not_lt]
  rw [ae_iff, he, Measure.bind_apply measurableSet_Iic κ.measurable.aemeasurable]
  calc _ = ∫⁻ s : ℝ, (0 : ENNReal) ∂ν := by
        apply lintegral_congr_ae
        filter_upwards [hν] with s hs
        have h := ae_iff.mp (hκ s hs)
        rw [he] at h
        exact h
    _ = 0 := by simp

/-- Actual conditional scale hierarchy of Section II. Starting with
prior nu, transition k samples the next dispersion using kernel kappa_k.
Only the first n conditional laws enter the finite population. -/
noncomputable def epistemicScaleHierarchy : ℕ → Measure ℝ → (ℕ → Kernel ℝ ℝ) → Measure ℝ
  | 0, ν, _ => ν
  | n + 1, ν, κ => (epistemicScaleHierarchy n ν κ).bind (κ n)

instance epistemicScaleHierarchy_probability (n : ℕ) (ν : Measure ℝ) (κ : ℕ → Kernel ℝ ℝ)
    [IsProbabilityMeasure ν] [∀ i, IsMarkovKernel (κ i)] :
    IsProbabilityMeasure (epistemicScaleHierarchy n ν κ) := by
  induction n with
  | zero => unfold epistemicScaleHierarchy; infer_instance
  | succ n ih =>
    let := ih
    unfold epistemicScaleHierarchy
    infer_instance

/-- Positive support propagates through every genuine conditional
uncertainty layer (Section II), rather than being assumed for the
final marginal used by the Gaussian density theorem. -/
theorem epistemicScaleHierarchy_ae_pos (n : ℕ) (ν : Measure ℝ) (κ : ℕ → Kernel ℝ ℝ)
    (hν : ∀ᵐ s ∂ν, 0 < s)
    (hκ : ∀ i < n, ∀ s, 0 < s → ∀ᵐ t ∂κ i s, 0 < t) :
    ∀ᵐ t ∂epistemicScaleHierarchy n ν κ, 0 < t := by
  induction n with
  | zero => exact hν
  | succ n ih =>
    exact hierarchy_bind_ae_pos _ _ (ih (fun i hi => hκ i (by omega)))
      (hκ n (Nat.lt_succ_self n))

example : IsMarkovKernel (epistemicFairScaleKernel (1 / 2)) := inferInstance

example : ∀ᵐ t ∂epistemicFairScaleKernel (1 / 2) 2, 0 < t :=
  epistemicFairScaleKernel_ae_pos (by norm_num) (by norm_num) (by norm_num)

example (n : ℕ) : IsProbabilityMeasure
    (epistemicScaleHierarchy n (Measure.dirac (2 : ℝ)) (fun _ => epistemicFairScaleKernel (1 / 2))) :=
  inferInstance

example (n : ℕ) : ∀ᵐ t ∂epistemicScaleHierarchy n (Measure.dirac (2 : ℝ))
    (fun _ => epistemicFairScaleKernel (1 / 2)), 0 < t := by
  apply epistemicScaleHierarchy_ae_pos
  · simpa only [ae_dirac_iff measurableSet_Ioi] using (show (0 : ℝ) < 2 by norm_num)
  · intro i hi s hs
    exact epistemicFairScaleKernel_ae_pos hs (by norm_num) (by norm_num)

#print axioms epistemicFairScaleKernel_markov
#print axioms epistemicScaleHierarchy_probability
#print axioms epistemicScaleHierarchy_ae_pos

end TailOptionPricing
