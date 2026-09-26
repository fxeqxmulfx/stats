/-
  Statistical differences between binary forecasts and real-world payoffs.
    Taleb, arXiv:1907.11162v3 (Dec 2019).

  ## Stats.BinaryForecasts.SigmaClosures — Eq. 8 integral closures.

  Closed-form Gaussian-tail integrals supporting the σ-sensitivity
  derivation, expressed via `stdNormalCdf` and the Gaussian PDF.

  See `Stats/BinaryForecasts.lean` for the umbrella module.
-/
import Stats.BinaryForecasts.SigmaSensitivity

open Real Set MeasureTheory Filter Topology
open scoped NNReal

namespace TailOptionPricing

open ProbabilityTheory

/-! ### Eq. 8 integral closures.

    Auxiliary integral identities that close the loop between the
    σ-derivative analytic computation (`gaussianEq8_sigmaSensitivity_eq`)
    and the paper-faithful integral form:

      `∫_K^∞ x · φ_σ(x) dx = σ · φ(K/σ)`,
      `∫_K^∞ φ_σ(x) dx     = 1 − Φ(K/σ)`,

    where `φ_σ(x) := (1/σ) · φ(x/σ) = (1/(σ√(2π)))·e^(−x²/(2σ²))` is
    the centered Gaussian density with variance `σ²`.

    Both follow by FTC, lifted through the linear scaling `x ↦ x/σ`. -/

open ProbabilityTheory MeasureTheory in
/-- **Centered Gaussian density with variance `σ²`** (paper's `φ_σ`).
    Connects Mathlib's standard normal `gaussianPDFReal 0 1` to the
    scale-`σ` variant. -/
noncomputable def gaussianPDF_σ (σ x : ℝ) : ℝ :=
  (1 / σ) * gaussianPDFReal 0 1 (x / σ)

open ProbabilityTheory MeasureTheory in
/-- **Antiderivative for `x · φ_σ(x)`.**
        `d/dx [−σ · φ(x/σ)] = x · φ_σ(x)`. -/
private theorem hasDerivAt_neg_σ_phi_div {σ : ℝ} (hσ : σ ≠ 0) (x : ℝ) :
    HasDerivAt (fun y : ℝ => -σ * gaussianPDFReal 0 1 (y / σ))
      (x * gaussianPDF_σ σ x) x := by
  have h_inner : HasDerivAt (fun y : ℝ => y / σ) (1 / σ) x :=
    (hasDerivAt_id x).div_const σ
  have h_phi : HasDerivAt (fun u : ℝ => gaussianPDFReal 0 1 u)
      (-(x / σ) * gaussianPDFReal 0 1 (x / σ)) (x / σ) :=
    gaussianPDFReal_std_hasDerivAt (x / σ)
  have h_comp := h_phi.comp x h_inner
  have h_const := h_comp.const_mul (-σ)
  convert h_const using 1
  unfold gaussianPDF_σ
  field_simp

open ProbabilityTheory MeasureTheory in
/-- **Antiderivative for `φ_σ(x)`.**
        `d/dx [Φ(x/σ)] = φ_σ(x)`. -/
private theorem hasDerivAt_stdNormalCdf_div {σ : ℝ} (_hσ : σ ≠ 0) (x : ℝ) :
    HasDerivAt (fun y : ℝ => stdNormalCdf (y / σ))
      (gaussianPDF_σ σ x) x := by
  have h_inner : HasDerivAt (fun y : ℝ => y / σ) (1 / σ) x :=
    (hasDerivAt_id x).div_const σ
  have h_cdf : HasDerivAt stdNormalCdf (gaussianPDFReal 0 1 (x / σ)) (x / σ) :=
    stdNormalCdf_hasDerivAt (x / σ)
  have h_comp := h_cdf.comp x h_inner
  convert h_comp using 1
  unfold gaussianPDF_σ
  ring

open ProbabilityTheory MeasureTheory in
/-- `−σ · φ(y/σ) → 0` as `y → ∞` (for `σ > 0`). -/
private theorem tendsto_neg_σ_phi_div_atTop {σ : ℝ} (hσ : 0 < σ) :
    Tendsto (fun y : ℝ => -σ * gaussianPDFReal 0 1 (y / σ))
      atTop (𝓝 0) := by
  have h_div : Tendsto (fun y : ℝ => y / σ) atTop atTop :=
    tendsto_id.atTop_div_const hσ
  have h_phi := tendsto_gaussianPDFReal_std_atTop.comp h_div
  have h_const_mul := h_phi.const_mul (-σ)
  simpa using h_const_mul

open ProbabilityTheory MeasureTheory in
/-- `Φ(y/σ) → 1` as `y → ∞` (for `σ > 0`).  Combines the standard
    normal CDF limit `Φ → 1` (via `tendsto_measure_Iic_atTop` on the
    probability measure `gaussianReal 0 1`) with `y/σ → ∞`. -/
private theorem tendsto_stdNormalCdf_div_atTop {σ : ℝ} (hσ : 0 < σ) :
    Tendsto (fun y : ℝ => stdNormalCdf (y / σ)) atTop (𝓝 1) := by
  have h_div : Tendsto (fun y : ℝ => y / σ) atTop atTop :=
    tendsto_id.atTop_div_const hσ
  -- Show stdNormalCdf y → 1 at +∞ first.
  have h_atTop : Tendsto stdNormalCdf atTop (𝓝 1) := by
    -- stdNormalCdf y = ((gaussianReal 0 1) (Iic y)).toReal.
    -- (Iic y) measure → 1 as y → ∞ (probability measure).
    have h_ennreal := tendsto_measure_Iic_atTop (gaussianReal (0 : ℝ) 1)
    have h_univ : (gaussianReal (0 : ℝ) 1) Set.univ = 1 := measure_univ
    rw [h_univ] at h_ennreal
    have h_one_ne_top : (1 : ENNReal) ≠ ⊤ := by norm_num
    have h_toReal_at_one : Tendsto ENNReal.toReal (𝓝 1) (𝓝 ((1 : ENNReal).toReal)) :=
      ENNReal.tendsto_toReal h_one_ne_top
    have h_comp := h_toReal_at_one.comp h_ennreal
    -- h_comp : Tendsto (fun y => ((gaussianReal 0 1)(Iic y)).toReal) atTop (𝓝 1)
    simp only [ENNReal.toReal_one] at h_comp
    convert h_comp using 1
  exact h_atTop.comp h_div

open ProbabilityTheory MeasureTheory in
/-- **Eq. 8 integral identity #1.**  For any `σ > 0` and `K ≥ 0`,
        `∫_K^∞ x · φ_σ(x) dx = σ · φ(K/σ)`.
    FTC on the antiderivative `−σ · φ(x/σ)`. -/
theorem integral_x_gaussianPDF_σ {K σ : ℝ} (hσ : 0 < σ) (hK : 0 ≤ K) :
    ∫ x in Ioi K, x * gaussianPDF_σ σ x =
      σ * gaussianPDFReal 0 1 (K / σ) := by
  have hσ_ne : σ ≠ 0 := hσ.ne'
  set F : ℝ → ℝ := fun y : ℝ => -σ * gaussianPDFReal 0 1 (y / σ) with hF_def
  have h_F_deriv : ∀ x : ℝ, HasDerivAt F (x * gaussianPDF_σ σ x) x := by
    intro x; exact hasDerivAt_neg_σ_phi_div hσ_ne x
  have h_F_tendsto : Tendsto F atTop (𝓝 0) := tendsto_neg_σ_phi_div_atTop hσ
  have h_nonneg : ∀ x ∈ Set.Ioi K, 0 ≤ x * gaussianPDF_σ σ x := by
    intro x hx
    have hx_pos : 0 ≤ x := le_of_lt (lt_of_le_of_lt hK hx)
    have h_pdf_nn : 0 ≤ gaussianPDF_σ σ x := by
      unfold gaussianPDF_σ
      have h_inv_pos : 0 ≤ 1 / σ := by positivity
      exact mul_nonneg h_inv_pos (gaussianPDFReal_nonneg 0 1 (x / σ))
    exact mul_nonneg hx_pos h_pdf_nn
  have h_int : IntegrableOn (fun x : ℝ => x * gaussianPDF_σ σ x)
      (Set.Ioi K) volume := by
    refine integrableOn_Ioi_deriv_of_nonneg ?_ ?_ h_nonneg h_F_tendsto
    · exact ((h_F_deriv K).continuousAt).continuousWithinAt
    · intro x _; exact h_F_deriv x
  have hFTC := integral_Ioi_of_hasDerivAt_of_tendsto
    (f := F) (a := K) (m := 0)
    (f' := fun x => x * gaussianPDF_σ σ x)
    ((h_F_deriv K).continuousAt.continuousWithinAt)
    (fun x _ => h_F_deriv x) h_int h_F_tendsto
  rw [hFTC, hF_def]
  ring

open ProbabilityTheory MeasureTheory in
/-- **Eq. 8 integral identity #2.**  For any `σ > 0`,
        `∫_K^∞ φ_σ(x) dx = 1 − Φ(K/σ)`.
    FTC on the antiderivative `Φ(x/σ)`. -/
theorem integral_gaussianPDF_σ {K σ : ℝ} (hσ : 0 < σ) :
    ∫ x in Ioi K, gaussianPDF_σ σ x = 1 - stdNormalCdf (K / σ) := by
  have hσ_ne : σ ≠ 0 := hσ.ne'
  set G : ℝ → ℝ := fun y : ℝ => stdNormalCdf (y / σ) with hG_def
  have h_G_deriv : ∀ x : ℝ, HasDerivAt G (gaussianPDF_σ σ x) x := by
    intro x; exact hasDerivAt_stdNormalCdf_div hσ_ne x
  have h_G_tendsto : Tendsto G atTop (𝓝 1) := tendsto_stdNormalCdf_div_atTop hσ
  have h_nonneg : ∀ x ∈ Set.Ioi K, 0 ≤ gaussianPDF_σ σ x := by
    intro x _
    unfold gaussianPDF_σ
    have h_inv_pos : 0 ≤ 1 / σ := by positivity
    exact mul_nonneg h_inv_pos (gaussianPDFReal_nonneg 0 1 (x / σ))
  have h_int : IntegrableOn (gaussianPDF_σ σ) (Set.Ioi K) volume := by
    refine integrableOn_Ioi_deriv_of_nonneg ?_ ?_ h_nonneg h_G_tendsto
    · exact ((h_G_deriv K).continuousAt).continuousWithinAt
    · intro x _; exact h_G_deriv x
  have hFTC := integral_Ioi_of_hasDerivAt_of_tendsto
    (f := G) (a := K) (m := 1)
    (f' := gaussianPDF_σ σ)
    ((h_G_deriv K).continuousAt.continuousWithinAt)
    (fun x _ => h_G_deriv x) h_int h_G_tendsto
  rw [hFTC, hG_def]


end TailOptionPricing
