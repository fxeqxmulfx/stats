module

/-
  Lognormal survival function `survivalLN` and its basic properties:
  continuity, monotonicity, the quadratic Markov / Chernoff tail bound, and
  integrability on positive half-lines.

  `survivalLN S₀ μ v s = lognormalLaw S₀ μ v (Ioi s)` is the actual
  tail probability of `S_T = S₀ · exp X`, `X ∼ 𝒩(μ, v)`. The PDF tail
  formula requires positive spot, positive threshold and nonzero variance.
  Risk neutrality further requires μ = -v/2.
-/
public import Stats.Arbitrage
public import Stats.BlackScholes.LognormalLaw
public import Mathlib.Probability.Moments.Basic

@[expose] public section

open Real Set MeasureTheory Filter Topology
open scoped NNReal

namespace TailOptionPricing

open ProbabilityTheory in
/-- Actual survival of the Gaussian pushforward, including support and
degenerate-variance cases. It is risk-neutral when `μ = -v/2`. -/
noncomputable def survivalLN (S₀ μ : ℝ) (v : ℝ≥0) (s : ℝ) : ℝ :=
  (lognormalLaw S₀ μ v).real (Ioi s)

/-- The law transformation needs positive spot and threshold; unlike a
PDF representation, it does not require positive variance. -/
theorem survivalLN_eq_gaussianReal_real_Ioi {S₀ μ s : ℝ} {v : ℝ≥0}
    (hS₀ : 0 < S₀) (hs : 0 < s) :
    survivalLN S₀ μ v s =
      (ProbabilityTheory.gaussianReal μ v).real (Ioi (Real.log (s / S₀))) :=
  lognormalLaw_real_Ioi_of_pos hS₀ hs

open ProbabilityTheory in
/-- Density-tail representation on its correct domain. -/
theorem survivalLN_eq_integral {S₀ μ s : ℝ} {v : ℝ≥0}
    (hS₀ : 0 < S₀) (hv : v ≠ 0) (hs : 0 < s) :
    survivalLN S₀ μ v s = ∫ x in Ioi (Real.log (s / S₀)), gaussianPDFReal μ v x := by
  rw [survivalLN_eq_gaussianReal_real_Ioi hS₀ hs]
  show ((gaussianReal μ v) (Ioi (Real.log (s / S₀)))).toReal = _
  rw [gaussianReal_apply_eq_integral _ hv, ENNReal.toReal_ofReal
    (setIntegral_nonneg measurableSet_Ioi (fun x _ => gaussianPDFReal_nonneg μ v x))]

/-- A positive terminal value exceeds every nonpositive threshold. -/
theorem survivalLN_of_nonpos {S₀ μ s : ℝ} {v : ℝ≥0}
    (hS₀ : 0 < S₀) (hs : s ≤ 0) : survivalLN S₀ μ v s = 1 :=
  lognormalLaw_real_Ioi_of_nonpos hS₀ hs

/-- The zero-variance survival is a strict step at the deterministic value. -/
theorem survivalLN_zero_var (S₀ μ s : ℝ) :
    survivalLN S₀ μ 0 s = if s < S₀ * Real.exp μ then 1 else 0 := by
  by_cases h : s < S₀ * Real.exp μ <;>
    simp [survivalLN, lognormalLaw_zero_var, Measure.real, Measure.dirac_apply',
      measurableSet_Ioi, h]

open ProbabilityTheory in
/-- For nonzero variance the lognormal survival is continuous on `Ioi 0`.
The zero-variance survival has an atom and is excluded. -/
theorem survivalLN_continuousOn {S₀ μ : ℝ} {v : ℝ≥0}
    (hS₀ : 0 < S₀) (hv : v ≠ 0) :
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
  have hc : ContinuousOn
      (fun s => ∫ x in Ioi (Real.log (s / S₀)), gaussianPDFReal μ v x) (Ioi 0) :=
    fun s hs => h_inner_cont.continuousAt.comp_continuousWithinAt (h_log_cont s hs)
  exact hc.congr (fun s hs => survivalLN_eq_integral hS₀ hv hs)

open ProbabilityTheory in
/-- The lognormal survival function is non-negative everywhere. -/
theorem survivalLN_nonneg (S₀ μ : ℝ) (v : ℝ≥0) (s : ℝ) :
    0 ≤ survivalLN S₀ μ v s := measureReal_nonneg

open ProbabilityTheory in
/-- The lognormal survival is bounded above by 1 (it is a probability). -/
theorem survivalLN_le_one {S₀ μ : ℝ} {v : ℝ≥0} (s : ℝ) :
    survivalLN S₀ μ v s ≤ 1 := measureReal_le_one

/-- Survival is antitone for every probability law, including its atoms. -/
theorem survivalLN_antitone (S₀ μ : ℝ) (v : ℝ≥0) :
    Antitone (survivalLN S₀ μ v) :=
  fun _ _ h => measureReal_mono (Ioi_subset_Ioi h)

open ProbabilityTheory in
/-- The lognormal survival is monotonically decreasing on `Ioi 0`. -/
theorem survivalLN_antitoneOn {S₀ μ : ℝ} {v : ℝ≥0} :
    AntitoneOn (survivalLN S₀ μ v) (Set.Ioi 0) :=
  (survivalLN_antitone S₀ μ v).antitoneOn _

open ProbabilityTheory in
/-- **Tail bound for the lognormal survival.**  Markov / Chernoff applied to
    `e^{2X}` with the Gaussian MGF identity gives a quadratic decay:
        survivalLN S₀ μ v s ≤ S₀² · exp(2μ + 2v) / s². -/
theorem survivalLN_le_quadratic {S₀ μ : ℝ} {v : ℝ≥0} (hS₀ : 0 < S₀)
    {s : ℝ} (hs : 0 < s) :
    survivalLN S₀ μ v s ≤ S₀ ^ 2 * Real.exp (2 * μ + 2 * (v : ℝ)) / s ^ 2 := by
  have h_le : survivalLN S₀ μ v s ≤
      (gaussianReal μ v).real (Set.Ici (Real.log (s / S₀))) := by
    rw [survivalLN_eq_gaussianReal_real_Ioi hS₀ hs]
    exact measureReal_mono Ioi_subset_Ici_self
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
  refine h_le.trans (h_chernoff.trans ?_)
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
  · exact (survivalLN_antitone S₀ μ v).measurable.aestronglyMeasurable
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
