/-
  Lognormal survival function `survivalLN` and its basic properties:
  continuity, monotonicity, the quadratic Markov / Chernoff tail bound, and
  integrability on positive half-lines.

  `survivalLN S₀ μ v s = ∫ x ∈ Ioi (log(s/S₀)), gaussianPDFReal μ v x`
  is the risk-neutral lognormal tail probability of `S_T = S₀ · exp X`
  where `X ∼ 𝒩(μ, v)`.
-/
import Stats.Arbitrage
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.Basic

open Real Set MeasureTheory Filter Topology
open scoped NNReal

namespace TailOptionPricing

open ProbabilityTheory in
/-- Risk-neutral lognormal survival function: `Q(S_T > s) = Q(X > log(s/S₀))`
    where `X ∼ 𝒩(μ, v)`. -/
noncomputable def survivalLN (S₀ μ : ℝ) (v : ℝ≥0) (s : ℝ) : ℝ :=
  ∫ x in Set.Ioi (Real.log (s / S₀)), gaussianPDFReal μ v x

open ProbabilityTheory in
/-- The lognormal survival is continuous on `Ioi 0`. -/
theorem survivalLN_continuousOn {S₀ μ : ℝ} (hS₀ : 0 < S₀) (v : ℝ≥0) :
    ContinuousOn (survivalLN S₀ μ v) (Set.Ioi 0) := by
  have h_log_cont : ContinuousOn (fun s : ℝ => Real.log (s / S₀)) (Set.Ioi 0) := by
    apply ContinuousOn.log
    · exact ContinuousOn.div continuousOn_id continuousOn_const fun _ _ => hS₀.ne'
    · intro s hs; exact (div_pos hs hS₀).ne'
  have h_pdf_cont : Continuous (gaussianPDFReal μ v) := by
    unfold gaussianPDFReal; fun_prop
  have h_pdf_int : Integrable (gaussianPDFReal μ v) := integrable_gaussianPDFReal μ v
  have h_inner_cont : Continuous
      (fun c : ℝ => ∫ x in Set.Ioi c, gaussianPDFReal μ v x) := by
    rw [continuous_iff_continuousAt]
    intro c
    have hc : c - 1 < c := by linarith
    exact (hasDerivAt_integral_Ioi hc h_pdf_int.integrableOn
              h_pdf_cont.continuousOn).continuousAt
  intro s hs
  exact (h_inner_cont.continuousAt.comp_continuousWithinAt (h_log_cont s hs))

open ProbabilityTheory in
/-- The lognormal survival function is non-negative everywhere. -/
theorem survivalLN_nonneg (S₀ μ : ℝ) (v : ℝ≥0) (s : ℝ) :
    0 ≤ survivalLN S₀ μ v s :=
  setIntegral_nonneg measurableSet_Ioi
    (fun x _ => gaussianPDFReal_nonneg μ v x)

open ProbabilityTheory in
/-- The lognormal survival is bounded above by 1 (it is a probability). -/
theorem survivalLN_le_one {S₀ μ : ℝ} {v : ℝ≥0} (hv : v ≠ 0) (s : ℝ) :
    survivalLN S₀ μ v s ≤ 1 := by
  unfold survivalLN
  calc (∫ x in Set.Ioi (Real.log (s / S₀)), gaussianPDFReal μ v x)
      ≤ ∫ x, gaussianPDFReal μ v x := by
        apply MeasureTheory.setIntegral_le_integral (integrable_gaussianPDFReal μ v)
        exact ae_of_all _ (gaussianPDFReal_nonneg μ v)
    _ = 1 := integral_gaussianPDFReal_eq_one μ hv

open ProbabilityTheory in
/-- The lognormal survival is monotonically decreasing on `Ioi 0`. -/
theorem survivalLN_antitoneOn {S₀ μ : ℝ} {v : ℝ≥0} (hS₀ : 0 < S₀) :
    AntitoneOn (survivalLN S₀ μ v) (Set.Ioi 0) := by
  intro s₁ hs₁ s₂ hs₂ h_le
  unfold survivalLN
  have hs₁_pos : 0 < s₁ := hs₁
  have h_log_le : Real.log (s₁ / S₀) ≤ Real.log (s₂ / S₀) :=
    Real.log_le_log (div_pos hs₁_pos hS₀) (by gcongr)
  apply MeasureTheory.setIntegral_mono_set
    ((integrable_gaussianPDFReal μ v).integrableOn)
    (ae_of_all _ (gaussianPDFReal_nonneg μ v))
  exact Filter.Eventually.of_forall (Set.Ioi_subset_Ioi h_log_le)

open ProbabilityTheory in
/-- **Tail bound for the lognormal survival.**  Markov / Chernoff applied to
    `e^{2X}` with the Gaussian MGF identity gives a quadratic decay:
        survivalLN S₀ μ v s ≤ S₀² · exp(2μ + 2v) / s². -/
theorem survivalLN_le_quadratic {S₀ μ : ℝ} {v : ℝ≥0} (hS₀ : 0 < S₀)
    {s : ℝ} (hs : 0 < s) :
    survivalLN S₀ μ v s ≤ S₀ ^ 2 * Real.exp (2 * μ + 2 * (v : ℝ)) / s ^ 2 := by
  by_cases hv : v = 0
  · subst hv
    have h0 : survivalLN S₀ μ 0 s = 0 := by
      unfold survivalLN
      simp [gaussianPDFReal_zero_var]
    rw [h0]
    positivity
  have : NullSingletonClass (gaussianReal μ v) := nullSingletonClass_gaussianReal hv
  have h_eq : survivalLN S₀ μ v s =
      (gaussianReal μ v).real (Set.Ici (Real.log (s / S₀))) := by
    unfold survivalLN
    show ∫ x in Set.Ioi (Real.log (s / S₀)), gaussianPDFReal μ v x =
         ((gaussianReal μ v) (Set.Ici (Real.log (s / S₀)))).toReal
    rw [← measure_congr Ioi_ae_eq_Ici,
        gaussianReal_apply_eq_integral _ hv,
        ENNReal.toReal_ofReal (by
          apply MeasureTheory.setIntegral_nonneg measurableSet_Ioi
          intro x _; exact gaussianPDFReal_nonneg μ v x)]
  rw [h_eq]
  have h_int : Integrable (fun x => Real.exp (2 * x)) (gaussianReal μ v) :=
    integrable_exp_mul_gaussianReal 2
  have h_chernoff :=
    measure_ge_le_exp_mul_mgf (X := id) (μ := gaussianReal μ v)
      (Real.log (s / S₀)) (by norm_num : (0:ℝ) ≤ 2) h_int
  have h_mgf : mgf (id : ℝ → ℝ) (gaussianReal μ v) 2 =
      Real.exp (2 * μ + 2 * (v : ℝ)) := by
    have := congrFun (mgf_id_gaussianReal (μ := μ) (v := v)) 2
    rw [this]
    congr 1
    ring
  rw [h_mgf] at h_chernoff
  refine h_chernoff.trans ?_
  have h_log_eq : Real.log (S₀ ^ 2 / s ^ 2) = -(2 : ℝ) * Real.log (s / S₀) := by
    rw [Real.log_div (by positivity : (S₀^2 : ℝ) ≠ 0)
                     (by positivity : (s^2 : ℝ) ≠ 0)]
    rw [Real.log_pow, Real.log_pow, Real.log_div hs.ne' hS₀.ne']
    push_cast; ring
  rw [show (-2 : ℝ) * Real.log (s / S₀) = Real.log (S₀ ^ 2 / s ^ 2) from h_log_eq.symm,
      Real.exp_log (by positivity : (0:ℝ) < S₀^2 / s^2)]
  rw [div_mul_eq_mul_div]

open ProbabilityTheory in
/-- **Integrability of the lognormal survival on `Ioi a`.**  Combining the
    quadratic tail bound with the integrability of `s ↦ s^(−2)` on a
    positive half-line, the lognormal survival is itself integrable. -/
theorem integrableOn_survivalLN {S₀ μ a : ℝ} {v : ℝ≥0}
    (hS₀ : 0 < S₀) (ha : 0 < a) :
    IntegrableOn (survivalLN S₀ μ v) (Set.Ioi a) volume := by
  set C := S₀ ^ 2 * Real.exp (2 * μ + 2 * (v : ℝ))
  have hC_pos : 0 < C := by positivity
  have h_g_int : IntegrableOn (fun s : ℝ => C * s ^ (-2 : ℝ)) (Set.Ioi a) volume :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) ha).const_mul C
  refine MeasureTheory.Integrable.mono_nonneg h_g_int ?_ ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    exact (survivalLN_continuousOn hS₀ v).mono (Set.Ioi_subset_Ioi ha.le)
  · exact (ae_restrict_iff' measurableSet_Ioi).mpr
      (Filter.Eventually.of_forall (fun s _ => survivalLN_nonneg S₀ μ v s))
  · apply (ae_restrict_iff' measurableSet_Ioi).mpr
    refine Filter.Eventually.of_forall (fun s hs => ?_)
    have hs_pos : 0 < s := ha.trans hs
    have h_pow : s ^ (-2 : ℝ) = (s ^ 2)⁻¹ := by
      rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) from by norm_cast,
          Real.rpow_neg hs_pos.le, Real.rpow_natCast]
    calc survivalLN S₀ μ v s
        ≤ C / s ^ 2 := survivalLN_le_quadratic hS₀ hs_pos
      _ = C * s ^ (-2 : ℝ) := by rw [h_pow]; ring

end TailOptionPricing
