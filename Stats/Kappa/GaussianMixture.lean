module

/-
  Taleb's κ-metric for pre-asymptotic fat-tailedness.
    "How Much Data Do You Need?  A Pre-asymptotic Metric for Fat-tailedness"
    arXiv:1802.05495v3 (Nov 2018).

  ## Stats.Kappa.GaussianMixture — mixture kurtosis (Eq. 17) and P-class linkage.

  For a two-component equal-weight mixture of Gaussians
  `½·N(μ₁, σ₁²) + ½·N(μ₂, σ₂²)`, the (Pearson) kurtosis admits a
  closed form (paper Eq. 17), with leptokurtosis threshold
      `|μ₁−μ₂| ≤ ⁴√6 · √|σ₁²−σ₂²|`.

  Also re-exposes the P-class linkage between the κ-stable
  invariance hypothesis and `Stats.Theorem1.survival_isRegularlyVarying`.

  See `Stats/Kappa.lean` for the umbrella module.
-/
public import Stats.Kappa.Basic

@[expose] public section

open Real Set Filter Topology

namespace TailOptionPricing

/-! ## Gaussian mixture kurtosis (paper Eq. 17).

    For a two-component equal-weight mixture of Gaussians
    `½·N(μ₁, σ₁²) + ½·N(μ₂, σ₂²)`, the (Pearson) kurtosis admits a
    closed form (paper Eq. 17):
        Kurt = 3 − 2 · ((μ₁−μ₂)^4 − 6(σ₁²−σ₂²)²) / ((μ₁−μ₂)² + 2(σ₁²+σ₂²))².
    The mixture is leptokurtic (`Kurt ≥ 3`) when the *means* are not
    too far apart compared to the spread of the variances — the
    region where the variance contrast dominates the mean separation
    — giving the threshold `|μ₁−μ₂| ≤ ⁴√6 · √|σ₁²−σ₂²|`. -/

/-- **Gaussian-mixture kurtosis (paper Eq. 17).**  Closed-form Pearson
    kurtosis of an equal-weight mixture `½·N(μ₁, σ₁²) + ½·N(μ₂, σ₂²)`. -/
noncomputable def gaussianMixtureKurtosis (μ₁ μ₂ σ₁ σ₂ : ℝ) : ℝ :=
  3 - 2 * ((μ₁ - μ₂) ^ 4 - 6 * (σ₁ ^ 2 - σ₂ ^ 2) ^ 2) /
        ((μ₁ - μ₂) ^ 2 + 2 * (σ₁ ^ 2 + σ₂ ^ 2)) ^ 2

/-- **Leptokurtosis threshold — polynomial form.**  Given a
    non-degenerate denominator (at least one of `μ₁ ≠ μ₂` or `σ_i ≠ 0`),
    the mixture is leptokurtic iff the mean-separation `(μ₁−μ₂)^4` is
    bounded by `6·(σ₁²−σ₂²)²`. -/
theorem gaussianMixtureKurtosis_ge_three_iff_poly
    {μ₁ μ₂ σ₁ σ₂ : ℝ}
    (h_pos : 0 < (μ₁ - μ₂) ^ 2 + 2 * (σ₁ ^ 2 + σ₂ ^ 2)) :
    3 ≤ gaussianMixtureKurtosis μ₁ μ₂ σ₁ σ₂ ↔
    (μ₁ - μ₂) ^ 4 ≤ 6 * (σ₁ ^ 2 - σ₂ ^ 2) ^ 2 := by
  unfold gaussianMixtureKurtosis
  have hY_sq_pos : 0 < ((μ₁ - μ₂) ^ 2 + 2 * (σ₁ ^ 2 + σ₂ ^ 2)) ^ 2 := by
    positivity
  constructor
  · intro h
    have h1 : 2 * ((μ₁ - μ₂) ^ 4 - 6 * (σ₁ ^ 2 - σ₂ ^ 2) ^ 2) /
              ((μ₁ - μ₂) ^ 2 + 2 * (σ₁ ^ 2 + σ₂ ^ 2)) ^ 2 ≤ 0 := by linarith
    rw [div_le_iff₀ hY_sq_pos, zero_mul] at h1
    linarith
  · intro h
    have h1 : 2 * ((μ₁ - μ₂) ^ 4 - 6 * (σ₁ ^ 2 - σ₂ ^ 2) ^ 2) ≤ 0 := by linarith
    have h2 : 2 * ((μ₁ - μ₂) ^ 4 - 6 * (σ₁ ^ 2 - σ₂ ^ 2) ^ 2) /
              ((μ₁ - μ₂) ^ 2 + 2 * (σ₁ ^ 2 + σ₂ ^ 2)) ^ 2 ≤ 0 := by
      rw [div_le_iff₀ hY_sq_pos, zero_mul]; linarith
    linarith

/-- **Leptokurtosis threshold (paper Eq. 17 corollary).**  The mixture
    is leptokurtic iff
        `|μ₁ − μ₂| ≤ ⁴√6 · √|σ₁² − σ₂²|`.
    Equivalent to the polynomial form via two squarings (both sides
    non-negative). -/
theorem gaussianMixtureKurtosis_ge_three_iff
    {μ₁ μ₂ σ₁ σ₂ : ℝ}
    (h_pos : 0 < (μ₁ - μ₂) ^ 2 + 2 * (σ₁ ^ 2 + σ₂ ^ 2)) :
    3 ≤ gaussianMixtureKurtosis μ₁ μ₂ σ₁ σ₂ ↔
    |μ₁ - μ₂| ≤ (6 : ℝ) ^ ((1 : ℝ) / 4) * Real.sqrt |σ₁ ^ 2 - σ₂ ^ 2| := by
  rw [gaussianMixtureKurtosis_ge_three_iff_poly h_pos]
  -- Rephrase using nonneg `d := |μ₁-μ₂|` and `s := |σ₁²-σ₂²|`.
  set d := |μ₁ - μ₂| with hd_def
  set s := |σ₁ ^ 2 - σ₂ ^ 2| with hs_def
  have hd_nn : 0 ≤ d := abs_nonneg _
  have hs_nn : 0 ≤ s := abs_nonneg _
  have h_six_nn : (0 : ℝ) ≤ 6 := by norm_num
  have h_six14_nn : 0 ≤ (6 : ℝ) ^ ((1 : ℝ) / 4) := Real.rpow_nonneg h_six_nn _
  have h_sqrt_nn : 0 ≤ Real.sqrt s := Real.sqrt_nonneg _
  have h_rhs_nn : 0 ≤ (6 : ℝ) ^ ((1 : ℝ) / 4) * Real.sqrt s :=
    mul_nonneg h_six14_nn h_sqrt_nn
  -- Convert `(μ-μ)^4` and `(σ²-σ²)²` to `d^4` and `s²`.
  have hd4_eq : (μ₁ - μ₂) ^ 4 = d ^ 4 := by
    rw [hd_def, show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_mul, sq_abs]
  have hs2_eq : (σ₁ ^ 2 - σ₂ ^ 2) ^ 2 = s ^ 2 := by rw [hs_def, sq_abs]
  rw [hd4_eq, hs2_eq]
  -- Helper: `(6^(1/4))^2 = √6` and `(√6)^2 = 6`.
  have h_six14_sq : ((6 : ℝ) ^ ((1 : ℝ) / 4)) ^ 2 = Real.sqrt 6 := by
    rw [show ((6 : ℝ) ^ ((1 : ℝ) / 4)) ^ 2
        = ((6 : ℝ) ^ ((1 : ℝ) / 4)) ^ ((2 : ℕ) : ℝ) from
          (Real.rpow_natCast _ 2).symm,
        ← Real.rpow_mul h_six_nn]
    rw [Real.sqrt_eq_rpow]
    norm_num
  have h_sqrt_six_sq : (Real.sqrt 6) ^ 2 = 6 := Real.sq_sqrt h_six_nn
  have h_sqrt_s_sq : (Real.sqrt s) ^ 2 = s := Real.sq_sqrt hs_nn
  -- Goal becomes: `d^4 ≤ 6 * s^2 ↔ d ≤ 6^(1/4) * √s`.
  constructor
  · -- Forward: square-root the inequality twice.
    intro h_poly
    -- Step 1: `d² ≤ √6 · s`.
    have h_step1 : d ^ 2 ≤ Real.sqrt 6 * s := by
      have h_rhs_pos : 0 ≤ Real.sqrt 6 * s :=
        mul_nonneg (Real.sqrt_nonneg _) hs_nn
      have h_sq_chain : (d ^ 2) ^ 2 ≤ (Real.sqrt 6 * s) ^ 2 := by
        rw [mul_pow, h_sqrt_six_sq]
        nlinarith [h_poly]
      exact (pow_le_pow_iff_left₀ (sq_nonneg d) h_rhs_pos two_ne_zero).mp
        h_sq_chain
    -- Step 2: `d ≤ 6^(1/4) · √s`.
    have h_sq_chain2 :
        d ^ 2 ≤ ((6 : ℝ) ^ ((1 : ℝ) / 4) * Real.sqrt s) ^ 2 := by
      rw [mul_pow, h_six14_sq, h_sqrt_s_sq]
      exact h_step1
    exact (pow_le_pow_iff_left₀ hd_nn h_rhs_nn two_ne_zero).mp h_sq_chain2
  · -- Backward: square the inequality twice.
    intro h_root
    -- Step 1: `d² ≤ √6 · s`.
    have h_step1 : d ^ 2 ≤ Real.sqrt 6 * s := by
      have h := pow_le_pow_left₀ hd_nn h_root 2
      rw [mul_pow, h_six14_sq, h_sqrt_s_sq] at h
      exact h
    -- Step 2: `d^4 ≤ 6 · s^2`.
    have h := pow_le_pow_left₀ (sq_nonneg d) h_step1 2
    have h_lhs : (d ^ 2) ^ 2 = d ^ 4 := by ring
    rw [h_lhs, mul_pow, h_sqrt_six_sq] at h
    exact h

/-! ## P-class linkage: Pareto survival and regular variation.

    The κ-stable invariance (`kappa_stable_invariance`) assumes the
    MAD has scaling form `M(n) = c · n^(1/ᾱ)`.  This scaling is the
    *signature* of the P-class — distributions whose survival function
    is regularly varying.  The bridge to the regular-variation
    framework of `Stats.RegularVariation` is via `Stats.Theorem1`'s
    `survival_isRegularlyVarying`:

      *Pareto survival `s ↦ (l/s)^α` is regularly varying with index `-α`.*

    Combined with `IsRegularlyVarying` (paper Eq. 1 of 1908.02347, our
    `Stats.Theorem1` formalisation), this gives a *first-principles*
    characterisation of when a tail distribution falls in the P-class
    underlying the stable κ-scaling: the strong-Pareto family is the
    canonical P-class representative.  The κ-metric on its MAD then
    saturates at `2 − α` (≡ `2 − ᾱ` for `α < 2`) per
    `kappa_stable_invariance`. -/

/-- **P-class linkage (κ → regular variation).**  The Pareto survival
    `s ↦ (l/s)^α` is regularly varying with index `−α` — this is the
    P-class membership criterion used implicitly by
    `kappa_stable_invariance`'s hypothesis on the MAD scaling.

    Re-exposes `Stats.Theorem1.survival_isRegularlyVarying` in the
    κ-metric namespace, for use by downstream consumers reasoning
    about stable-basin κ. -/
theorem paretoSurvival_isRegularlyVarying {l α : ℝ} (hl : 0 < l) :
    IsRegularlyVarying (survival l α) (-α) :=
  survival_isRegularlyVarying hl

end TailOptionPricing
