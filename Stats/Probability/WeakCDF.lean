module

/-
  Pointwise CDF convergence implies weak convergence of real probability
  measures. Bounded half-open intervals form a pi-system of neighborhoods.
  Used for the corrected asymptotic of arXiv:2004.05894v1, Remark 1.
-/
public import Mathlib.Probability.CDF
public import Mathlib.MeasureTheory.Measure.Portmanteau

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory Filter Topology

namespace TailOptionPricing

/-- Convergence of actual CDFs at every real threshold implies weak
convergence. This sufficient criterion does not assume continuity of the limit CDF. -/
theorem probabilityMeasure_tendsto_of_cdf {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {μs : ι → ProbabilityMeasure ℝ} {μ : ProbabilityMeasure ℝ}
    (h : ∀ x : ℝ, Tendsto (fun i => cdf (μs i : Measure ℝ) x) l
      (𝓝 (cdf (μ : Measure ℝ) x))) : Tendsto μs l (𝓝 μ) := by
  apply (isPiSystem_Ioc (id : ℝ → ℝ) (id : ℝ → ℝ)).tendsto_probabilityMeasure_of_tendsto_of_mem
  · rintro s ⟨a, b, hab, rfl⟩
    exact measurableSet_Ioc
  · intro u hu x hx
    obtain ⟨a, b, hab, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hu.mem_nhds hx)
    obtain ⟨c, hxc, hcb⟩ := exists_between hab.2
    refine ⟨Ioc a c, ⟨a, c, hab.1.trans hxc, rfl⟩, Ioc_mem_nhds hab.1 hxc, ?_⟩
    intro z hz
    exact hsub ⟨hz.1, hz.2.trans_lt hcb⟩
  · rintro s ⟨a, b, hab, rfl⟩
    change a < b at hab
    apply NNReal.tendsto_coe.mp
    simp only [id_eq]
    have he (ρ : ProbabilityMeasure ℝ) : (ρ (Ioc a b) : ℝ) =
        cdf (ρ : Measure ℝ) b - cdf (ρ : Measure ℝ) a := by
      rw [← ProbabilityMeasure.measureReal_eq_coe_coeFn, ← Iic_sdiff_Iic,
        measureReal_sdiff (μ := (ρ : Measure ℝ)) (Iic_subset_Iic.mpr hab.le) measurableSet_Iic,
        ← cdf_eq_real, ← cdf_eq_real]
    simpa only [he] using (h b).sub (h a)

end TailOptionPricing
