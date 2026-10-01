/-
  Statistical differences between binary forecasts and real-world payoffs.
    Taleb, arXiv:1907.11162v3 (Dec 2019).

  ## Stats.BinaryForecasts.SigmaSensitivity — paper Eq. 8 σ-derivation.

  Contains:
    * Gaussian σ-sensitivity polynomial positivity at σ = 1.
    * Full σ-derivation underlying Eq. 8.

  See `Stats/BinaryForecasts.lean` for the umbrella module.
-/
import Stats.BinaryForecasts.CharacteristicScale

open Real Set MeasureTheory Filter Topology
open scoped NNReal

namespace TailOptionPricing

open ProbabilityTheory

/-! ## Gaussian σ-sensitivity (paper Eq. 8) — polynomial positivity.

    The derivative of the displayed Eq. 8 expression is proved below;
    its integral closures are in `SigmaClosures.lean`. The polynomial
    `K⁴ − K³ − K² + 2K` is its numerator at `σ = 1` and is positive
    for `K > 0`. This does not establish the source's claimed sign for
    every positive σ; see REVIEW.md, BF-21.

    Eq. 8 differentiates A − B, where A is the tail first moment and
    B the tail probability. For the linear payoff, the originally
    defined gap I₁ − I₂ is A − K·B; see REVIEW.md, BF-20.

    Proof: the algebraic identity
        K⁴ − K³ − K² + 2·K = K · ((K − 1)² · (K + 1) + 1)
    exhibits the polynomial as a positive product on `K > 0`. -/

/-- **Eq. 8 numerator polynomial positivity at σ = 1 (paper claim).**
    For any `K > 0`,
        K⁴ − K³ − K² + 2 · K > 0,
    via the factorisation `K⁴ − K³ − K² + 2·K = K·((K−1)²·(K+1) + 1)`. -/
theorem gaussian_eq8_polynomial_pos {K : ℝ} (hK : 0 < K) :
    0 < K ^ 4 - K ^ 3 - K ^ 2 + 2 * K := by
  have h_factor : K ^ 4 - K ^ 3 - K ^ 2 + 2 * K
      = K * ((K - 1) ^ 2 * (K + 1) + 1) := by ring
  rw [h_factor]
  have h_inner_pos : 0 < (K - 1) ^ 2 * (K + 1) + 1 := by
    have h_K1_nn : 0 ≤ (K - 1) ^ 2 := sq_nonneg _
    have h_Kp1_pos : 0 < K + 1 := by linarith
    have h_prod_nn : 0 ≤ (K - 1) ^ 2 * (K + 1) :=
      mul_nonneg h_K1_nn h_Kp1_pos.le
    linarith
  exact mul_pos hK h_inner_pos

/-! ### Eq. 8 — full σ-derivation.

    Headline (paper Eq. 8 verbatim, after closing the integrals via
    `∫_K^∞ x·φ_σ(x) dx = σ·φ(K/σ)` and `∫_K^∞ φ_σ(x) dx = 1 − Φ(K/σ)`):

      `∂²/∂σ² (σ·φ(K/σ)) − ∂²/∂σ² (1 − Φ(K/σ))`
        `= e^(−K²/(2σ²)) · ((K−1)·K³ − (K−2)·K·σ²) / (√(2π) · σ⁵)`.

    Derivation:  let `p(σ) := φ(K/σ)`.  Then by the chain rule
    `p'(σ) = (K²/σ³) · p(σ)` (using `φ'(z) = −z·φ(z)` and `d/dσ(K/σ)
    = −K/σ²`).  Applied twice:

      `A := σ·p,   A' = p · (1 + K²/σ²),   A'' = (K⁴ − K²σ²)/σ⁵ · p`,
      `B := 1 − Φ(K/σ),   B' = (K/σ²) · p,   B'' = (K³ − 2Kσ²)/σ⁵ · p`,

    and the difference `A'' − B'' = (K⁴ − K³ − K²σ² + 2Kσ²)/σ⁵ · p`
    matches the paper after factorisation. -/

open ProbabilityTheory MeasureTheory in
/-- **Derivative of the standard normal PDF.**  `φ'(x) = −x · φ(x)`,
    where `φ = gaussianPDFReal 0 1`.  Obtained by negating
    `hasDerivAt_neg_gaussianPDFReal_std`. -/
theorem gaussianPDFReal_std_hasDerivAt (x : ℝ) :
    HasDerivAt (fun y : ℝ => gaussianPDFReal 0 1 y)
      (-x * gaussianPDFReal 0 1 x) x := by
  have h := (hasDerivAt_neg_gaussianPDFReal_std x).neg
  -- h : HasDerivAt (-fun y => -(gaussianPDFReal 0 1 y)) (-(x·φ(x))) x.
  -- Goal needs `(fun y => gaussianPDFReal 0 1 y)` and `-x · φ(x)`.
  convert h using 1
  · funext y; simp
  · ring

open ProbabilityTheory MeasureTheory in
/-- **σ-derivative of `K/σ`.**  `d/dσ (K/σ) = −K/σ²` for `σ ≠ 0`. -/
private theorem hasDerivAt_K_div_sigma {K σ : ℝ} (hσ : σ ≠ 0) :
    HasDerivAt (fun s : ℝ => K / s) (-K / σ ^ 2) σ := by
  have h_inv : HasDerivAt (fun s : ℝ => s⁻¹) (-(σ ^ 2)⁻¹) σ :=
    hasDerivAt_inv hσ
  have h_mul := h_inv.const_mul K
  -- h_mul : HasDerivAt (fun s => K * s⁻¹) (K * -(σ ^ 2)⁻¹) σ.
  have h_fun_eq : (fun s : ℝ => K * s⁻¹) = (fun s : ℝ => K / s) := by
    funext s; rw [div_eq_mul_inv]
  have h_val_eq : K * -(σ ^ 2)⁻¹ = -K / σ ^ 2 := by
    rw [mul_neg, ← div_eq_mul_inv]; ring
  rw [h_fun_eq] at h_mul
  rw [h_val_eq] at h_mul
  exact h_mul

open ProbabilityTheory MeasureTheory in
/-- **σ-derivative of `φ(K/σ)`.**
        `d/dσ φ(K/σ) = (K²/σ³) · φ(K/σ)`,
    via chain rule on `K/σ → −K/σ²` and `φ' = −id · φ`. -/
private theorem gaussianPDF_K_div_sigma_hasDerivAt {K σ : ℝ} (hσ : σ ≠ 0) :
    HasDerivAt (fun s : ℝ => gaussianPDFReal 0 1 (K / s))
      (K ^ 2 / σ ^ 3 * gaussianPDFReal 0 1 (K / σ)) σ := by
  have hσ_sq_ne : σ ^ 2 ≠ 0 := pow_ne_zero 2 hσ
  have hσ_cube_ne : σ ^ 3 ≠ 0 := pow_ne_zero 3 hσ
  have h_inner : HasDerivAt (fun s : ℝ => K / s) (-K / σ ^ 2) σ :=
    hasDerivAt_K_div_sigma hσ
  have h_pdf : HasDerivAt (fun y : ℝ => gaussianPDFReal 0 1 y)
      (-(K / σ) * gaussianPDFReal 0 1 (K / σ)) (K / σ) :=
    gaussianPDFReal_std_hasDerivAt (K / σ)
  have h_comp := h_pdf.comp σ h_inner
  -- h_comp : HasDerivAt (φ ∘ (·/·)) ((-(K/σ)·φ(K/σ)) · (-K/σ²)) σ.
  convert h_comp using 1
  · rfl
  · field_simp

open ProbabilityTheory MeasureTheory in
/-- **Eq. 8 — second σ-derivative of `σ·φ(K/σ)`.**  Identifying
    `A(σ) := σ·φ(K/σ) = ∫_K^∞ x·φ_σ(x) dx`, its first σ-derivative is
    `A'(σ) = φ(K/σ) · (1 + K²/σ²)`, and the σ-derivative of *that*
    function — i.e. `A''(σ)` — equals
        `A''(σ) = (K⁴ − K²·σ²) / σ⁵ · φ(K/σ)`.
    Direct chained `HasDerivAt`. -/
private theorem gaussianTailMean_σ_secondDeriv {K σ : ℝ} (hσ : 0 < σ) :
    HasDerivAt
      (fun s : ℝ => gaussianPDFReal 0 1 (K / s) * (1 + K ^ 2 / s ^ 2))
      ((K ^ 4 - K ^ 2 * σ ^ 2) / σ ^ 5 * gaussianPDFReal 0 1 (K / σ)) σ := by
  have hσ_ne : σ ≠ 0 := hσ.ne'
  -- σ-derivative of φ(K/σ).
  have h_pdf : HasDerivAt (fun s : ℝ => gaussianPDFReal 0 1 (K / s))
      (K ^ 2 / σ ^ 3 * gaussianPDFReal 0 1 (K / σ)) σ :=
    gaussianPDF_K_div_sigma_hasDerivAt hσ_ne
  -- σ-derivative of (K/σ)² is -2K²/σ³.
  have h_Kdivσ : HasDerivAt (fun s : ℝ => K / s) (-K / σ ^ 2) σ :=
    hasDerivAt_K_div_sigma hσ_ne
  have h_K2_div_s2 : HasDerivAt (fun s : ℝ => K ^ 2 / s ^ 2)
      (-2 * K ^ 2 / σ ^ 3) σ := by
    -- (K/s) · (K/s) = K²/s², differentiate via product rule.
    have h_prod := h_Kdivσ.mul h_Kdivσ
    have h_fun_eq :
        ((fun s : ℝ => K / s) * fun s : ℝ => K / s) =
        (fun s : ℝ => K ^ 2 / s ^ 2) := by
      funext s
      show K / s * (K / s) = K ^ 2 / s ^ 2
      rw [← sq, div_pow]
    rw [h_fun_eq] at h_prod
    convert h_prod using 1
    field_simp
    ring
  -- σ-derivative of (1 + K²/σ²) is -2K²/σ³.
  have h_one_plus : HasDerivAt (fun s : ℝ => 1 + K ^ 2 / s ^ 2)
      (-2 * K ^ 2 / σ ^ 3) σ := h_K2_div_s2.const_add 1
  -- Product rule.
  have h_prod := h_pdf.mul h_one_plus
  convert h_prod using 1
  field_simp
  ring

open ProbabilityTheory MeasureTheory in
/-- **Eq. 8 — second σ-derivative of `1 − Φ(K/σ)`.**  Identifying
    `B(σ) := 1 − Φ(K/σ) = ∫_K^∞ φ_σ(x) dx`, its first σ-derivative is
    `B'(σ) = (K/σ²) · φ(K/σ)`, and the σ-derivative of *that* — i.e.
    `B''(σ)` — equals
        `B''(σ) = (K³ − 2·K·σ²) / σ⁵ · φ(K/σ)`. -/
private theorem gaussianTailProb_σ_secondDeriv {K σ : ℝ} (hσ : 0 < σ) :
    HasDerivAt
      (fun s : ℝ => K / s ^ 2 * gaussianPDFReal 0 1 (K / s))
      ((K ^ 3 - 2 * K * σ ^ 2) / σ ^ 5 * gaussianPDFReal 0 1 (K / σ)) σ := by
  have hσ_ne : σ ≠ 0 := hσ.ne'
  have h_pdf : HasDerivAt (fun s : ℝ => gaussianPDFReal 0 1 (K / s))
      (K ^ 2 / σ ^ 3 * gaussianPDFReal 0 1 (K / σ)) σ :=
    gaussianPDF_K_div_sigma_hasDerivAt hσ_ne
  have h_Kdivσ : HasDerivAt (fun s : ℝ => K / s) (-K / σ ^ 2) σ :=
    hasDerivAt_K_div_sigma hσ_ne
  have h_id : HasDerivAt (fun s : ℝ => s) 1 σ := hasDerivAt_id σ
  -- σ-derivative of K/σ² is −2K/σ³, via (K/σ)/σ.
  have h_K_div_σ_sq : HasDerivAt (fun s : ℝ => K / s ^ 2) (-2 * K / σ ^ 3) σ := by
    have h_div := h_Kdivσ.div h_id hσ_ne
    have h_fun_eq :
        ((fun s : ℝ => K / s) / fun s : ℝ => s) =
        (fun s : ℝ => K / s ^ 2) := by
      funext s
      show K / s / s = K / s ^ 2
      rw [div_div, sq]
    rw [h_fun_eq] at h_div
    convert h_div using 1
    field_simp
    ring
  -- Product rule for K/σ² · φ(K/σ).
  have h_prod := h_K_div_σ_sq.mul h_pdf
  convert h_prod using 1
  field_simp
  ring

open ProbabilityTheory MeasureTheory in
/-- **Eq. 8 — full σ-sensitivity (paper-faithful, in φ-form).**  Combining
    `gaussianTailMean_σ_secondDeriv` and `gaussianTailProb_σ_secondDeriv`
    via subtraction:
        `A''(σ) − B''(σ) = ((K−1)·K³ − (K−2)·K·σ²) / σ⁵ · φ(K/σ)`,
    where `A'(σ) := φ(K/σ)·(1 + K²/σ²)` is the first σ-derivative of
    `∫_K^∞ x · φ_σ(x) dx = σ·φ(K/σ)`, and `B'(σ) := (K/σ²)·φ(K/σ)`
    is the first σ-derivative of `∫_K^∞ φ_σ(x) dx = 1 − Φ(K/σ)`.

    Equivalent paper form via `φ(K/σ) = e^(−K²/(2σ²))/√(2π)`:
    see `gaussianEq8_sigmaSensitivity_eq`. -/
theorem gaussianEq8_sigmaSensitivity_eq_phi {K σ : ℝ} (hσ : 0 < σ) :
    HasDerivAt
      (fun s : ℝ =>
        gaussianPDFReal 0 1 (K / s) * (1 + K ^ 2 / s ^ 2)
          - K / s ^ 2 * gaussianPDFReal 0 1 (K / s))
      (((K - 1) * K ^ 3 - (K - 2) * K * σ ^ 2) / σ ^ 5
        * gaussianPDFReal 0 1 (K / σ)) σ := by
  have hA := gaussianTailMean_σ_secondDeriv (K := K) hσ
  have hB := gaussianTailProb_σ_secondDeriv (K := K) hσ
  have h_diff := hA.sub hB
  convert h_diff using 1
  ring

open ProbabilityTheory MeasureTheory in
/-- **Eq. 8 (paper verbatim form).**  The closed form for the σ-sensitivity
    of the Gaussian truncated-mean / truncated-probability difference is
        `((K−1)·K³ − (K−2)·K·σ²) / σ⁵ · e^(−K²/(2σ²)) / √(2π)`,
    obtained by unfolding `φ(K/σ) = (1/√(2π)) · e^(−K²/(2σ²))` in
    `gaussianEq8_sigmaSensitivity_eq_phi`.

    Positivity for `K > 0`, `σ > 0`: at `σ = 1` the numerator equals the
    polynomial `K⁴ − K³ − K² + 2K = K · ((K−1)²·(K+1) + 1) > 0`
    (`gaussian_eq8_polynomial_pos`).  General `σ` follows by the same
    factorisation up to `σ²` scaling. -/
theorem gaussianEq8_sigmaSensitivity_eq {K σ : ℝ} (hσ : 0 < σ) :
    HasDerivAt
      (fun s : ℝ =>
        gaussianPDFReal 0 1 (K / s) * (1 + K ^ 2 / s ^ 2)
          - K / s ^ 2 * gaussianPDFReal 0 1 (K / s))
      (Real.exp (-K ^ 2 / (2 * σ ^ 2))
        * ((K - 1) * K ^ 3 - (K - 2) * K * σ ^ 2)
        / (Real.sqrt (2 * Real.pi) * σ ^ 5)) σ := by
  have h := gaussianEq8_sigmaSensitivity_eq_phi (K := K) hσ
  convert h using 1
  -- Show the two derivative values agree by unfolding `φ`.
  have h_phi_eq : gaussianPDFReal 0 1 (K / σ)
      = 1 / Real.sqrt (2 * Real.pi) * Real.exp (-((K / σ) ^ 2) / 2) := by
    simp [gaussianPDFReal, NNReal.coe_one]
  rw [h_phi_eq]
  have h_exp_arg : -((K / σ) ^ 2) / 2 = -K ^ 2 / (2 * σ ^ 2) := by
    field_simp
  rw [h_exp_arg]
  have hπ_pos : 0 < Real.sqrt (2 * Real.pi) :=
    Real.sqrt_pos.mpr (by positivity)
  have hσ5_ne : σ ^ 5 ≠ 0 := pow_ne_zero 5 hσ.ne'
  have hπ_ne : Real.sqrt (2 * Real.pi) ≠ 0 := hπ_pos.ne'
  field_simp


end TailOptionPricing
