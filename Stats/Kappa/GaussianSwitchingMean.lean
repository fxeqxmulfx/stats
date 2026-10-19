module

/-
  Taleb's κ-metric for pre-asymptotic fat-tailedness.
    "How Much Data Do You Need?  A Pre-asymptotic Metric for Fat-tailedness"
    arXiv:1802.05495v3 (Nov 2018).

  ## Stats.Kappa.GaussianSwitchingMean — equal-variance Gaussian
  switching-mean κ₁ closed form (paper Section IV-D, Eq. 18).

  For an equal-weight Gaussian mixture
      `½·N(μ₁, σ²) + ½·N(μ₂, σ²)`
  with common variance `σ²` and mean separation `d := μ₁ − μ₂`, the
  κ-metric at the `(n₀, n) = (1, 2)` baseline admits the closed form
  (paper Eq. 18, verbatim from the LaTeX source):

    κ₁ = log(4) /
         ( log(π) − 2·log( (√π·d·e^(d²/(4σ²))·erf(d/(2σ)) + 2σ·e^(d²/(4σ²)) + 2σ) /
                           (d·e^(d²/(4σ²))·erf(d/(2√2·σ)) + 2·√(2/π)·σ·e^(d²/(8σ²))) ) )
         + 2.

  Note: the last exponent in the denominator (`d²/(8σ²)`) differs from
  the other three (`d²/(4σ²)`).  This is paper Eq. 18 verbatim from the
  arXiv LaTeX source `kappa-n-final.tex` line 819 (audit 2026-05-13
  pass 4: confirmed via LaTeX source after an earlier mis-read of the
  small PDF image suggested the formula was buggy — it is not).

  Following the same definitional convention as
  `Stats.Kappa.LognormalCumulants`, we take the MAD ratio as
  definitional (the underlying MAD integrals against the mixture
  density would require further measure-theoretic plumbing).  We define
  the numerator and denominator as primitive expressions, build an MAD
  oracle whose `M(2)/M(1) = N/(D·√π)` ratio realises Eq. 18, and verify
  the κ identity algebraically.  A purely algebraic sign criterion for
  the paper's "negative κ" regime (`κ₁ < 0`) is also delivered.

  See `Stats/Kappa.lean` for the umbrella module.
-/
public import Stats.BlackScholes.Erfc
public import Stats.Kappa.Basic

@[expose] public section

open Real Set Filter Topology

namespace TailOptionPricing

/-! ## Eq. 18 ingredients.

    `Real.erf` is provided by `Stats.BlackScholes.Erfc` as a wrapper
    around `stdNormalCdf` (Mathlib `v4.29.0` has no native `Real.erf`).
    No algebraic properties of `erf` are used in the κ identity below
    — its symbolic role in both `Num` and `Den` is what matters. -/

/-- **Eq. 18 numerator** (paper Section IV-D).  The closed-form
    expression appearing as the *top* of the log-ratio in
    `gaussianSwitchingMean_kappa1`.  Verbatim from arXiv LaTeX source. -/
noncomputable def gaussianSwitchingMeanNum (σ d : ℝ) : ℝ :=
  Real.sqrt Real.pi * d * Real.exp (d ^ 2 / (4 * σ ^ 2)) *
      Real.erf (d / (2 * σ)) +
    2 * Real.sqrt (σ ^ 2) * Real.exp (d ^ 2 / (4 * σ ^ 2)) + 2 * σ

/-- **Eq. 18 denominator** (paper Section IV-D).  The closed-form
    expression appearing as the *bottom* of the log-ratio in
    `gaussianSwitchingMean_kappa1`.  Verbatim from arXiv LaTeX source.
    Note: the last term has exponent `d²/(8σ²)`, distinct from the
    `d²/(4σ²)` elsewhere — paper Eq. 18 verbatim, not a typo. -/
noncomputable def gaussianSwitchingMeanDen (σ d : ℝ) : ℝ :=
  d * Real.exp (d ^ 2 / (4 * σ ^ 2)) *
      Real.erf (d / (2 * Real.sqrt 2 * σ)) +
    2 * Real.sqrt (2 / Real.pi) * σ * Real.exp (d ^ 2 / (8 * σ ^ 2))

/-- **MAD oracle for the equal-variance Gaussian switching-mean mixture**
    (definitional, paper Eq. 18 calibration).  Values:
        M(1) = √π · `gaussianSwitchingMeanDen σ d`,
        M(2) = `gaussianSwitchingMeanNum σ d`,
    chosen so that `M(2) / M(1) = N / (D · √π)`, which feeds through the
    bare-form κ identity (paper Definition 1) to yield Eq. 18.
    Outside `{1, 2}` the oracle is `0` (only the `1/2` ratio enters
    Eq. 18). -/
noncomputable def gaussianSwitchingMeanMAD (σ d : ℝ) : ℕ → ℝ
  | 1 => Real.sqrt Real.pi * gaussianSwitchingMeanDen σ d
  | 2 => gaussianSwitchingMeanNum σ d
  | _ => 0

/-- **Switching-mean κ₁ closed form** (paper Eq. 18, verbatim).  For an
    equal-variance Gaussian mixture with mean separation `d = μ₁ − μ₂`,
        κ₁ := 2 + log(4) / (log(π) − 2·log(`Num σ d` / `Den σ d`)). -/
noncomputable def gaussianSwitchingMeanKappa1 (σ d : ℝ) : ℝ :=
  2 + Real.log 4 /
    (Real.log Real.pi - 2 * Real.log
      (gaussianSwitchingMeanNum σ d / gaussianSwitchingMeanDen σ d))

/-! ## Closed-form κ₁ identity. -/

/-- **Switching-mean κ₁ (paper Eq. 18, verbatim).**  Under positivity of
    the Eq. 18 numerator and denominator and a non-degeneracy condition
    (`N² ≠ π · D²`, equivalent to `log(π) − 2·log(N/D) ≠ 0`), the
    abstract κ-metric evaluated on `gaussianSwitchingMeanMAD σ d` at the
    `(1, 2)` baseline equals the paper's closed form
        `2 + log(4) / (log(π) − 2·log(N/D))`.

    The MAD oracle is calibrated so that `M(2)/M(1) = N/(D·√π)`; the
    bare-form κ identity gives
        `κ = 2 − log(2) / log(N/(D·√π))
           = 2 − log(2) / (log(N/D) − (1/2)·log(π))
           = 2 + log(4) / (log(π) − 2·log(N/D))`. -/
theorem gaussianSwitchingMean_kappa1 {σ d : ℝ}
    (hN : 0 < gaussianSwitchingMeanNum σ d)
    (hD : 0 < gaussianSwitchingMeanDen σ d)
    (hND_sq : gaussianSwitchingMeanNum σ d ^ 2
        ≠ Real.pi * gaussianSwitchingMeanDen σ d ^ 2) :
    kappa (gaussianSwitchingMeanMAD σ d) 1 2 = gaussianSwitchingMeanKappa1 σ d := by
  set N := gaussianSwitchingMeanNum σ d with hN_def
  set D := gaussianSwitchingMeanDen σ d with hD_def
  have hπ_pos : 0 < Real.pi := Real.pi_pos
  have h_sqrtπ_pos : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr hπ_pos
  have h_sqrtπ_ne : Real.sqrt Real.pi ≠ 0 := h_sqrtπ_pos.ne'
  have hM1_pos : 0 < Real.sqrt Real.pi * D := mul_pos h_sqrtπ_pos hD
  -- Non-degeneracy: log(π) − 2 log(N/D) ≠ 0.
  have h_denom_ne : Real.log Real.pi - 2 * Real.log (N / D) ≠ 0 := by
    intro h
    have h_log_NsqD : 2 * Real.log (N / D) = Real.log Real.pi := by linarith
    have h_log_sq : Real.log ((N / D) ^ 2) = Real.log Real.pi := by
      rw [Real.log_pow]; push_cast; linarith
    have h_ND_pos : 0 < N / D := div_pos hN hD
    have h_NDsq_pos : 0 < (N / D) ^ 2 := pow_pos h_ND_pos 2
    have h_eq : (N / D) ^ 2 = Real.pi :=
      Real.log_injOn_pos (Set.mem_Ioi.mpr h_NDsq_pos) (Set.mem_Ioi.mpr hπ_pos) h_log_sq
    apply hND_sq
    have hND_sq_eq : N ^ 2 = (N / D) ^ 2 * D ^ 2 := by field_simp
    rw [hND_sq_eq, h_eq]
  unfold kappa gaussianSwitchingMeanKappa1
  show 2 - (Real.log ((2 : ℕ) : ℝ) - Real.log ((1 : ℕ) : ℝ)) /
        (Real.log (gaussianSwitchingMeanMAD σ d 2) -
          Real.log (gaussianSwitchingMeanMAD σ d 1))
      = 2 + Real.log 4 /
            (Real.log Real.pi - 2 * Real.log (N / D))
  have hM1 : gaussianSwitchingMeanMAD σ d 1 = Real.sqrt Real.pi * D := rfl
  have hM2 : gaussianSwitchingMeanMAD σ d 2 = N := rfl
  rw [hM1, hM2]
  rw [Real.log_mul h_sqrtπ_ne hD.ne', Real.log_sqrt hπ_pos.le]
  push_cast
  rw [Real.log_one, sub_zero, Real.log_div hN.ne' hD.ne']
  have h_log4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    push_cast; ring
  rw [h_log4]
  set a := Real.log N - Real.log D - Real.log Real.pi / 2 with ha_def
  have h_lhs_denom : Real.log N - (Real.log Real.pi / 2 + Real.log D) = a := by
    rw [ha_def]; ring
  have h_rhs_denom :
      Real.log Real.pi - 2 * (Real.log N - Real.log D) = -2 * a := by
    rw [ha_def]; ring
  have h_a_ne : a ≠ 0 := by
    intro h
    apply h_denom_ne
    rw [Real.log_div hN.ne' hD.ne']
    rw [ha_def] at h
    linarith
  rw [h_lhs_denom, h_rhs_denom]
  field_simp
  ring

/-! ## Sign criterion for the negative-κ regime. -/

/-- **Negative-κ sign criterion** (paper Section IV-D, post-Eq. 18).
    The paper's "negative κ" regime — where the mixture's
    leptokurtic→platykurtic crossover flips the κ-metric below zero —
    translates, via the Eq. 18 closed form, to the algebraic condition

        `π · D² < N²`   and   `N² < 2π · D²`

    on the Eq. 18 numerator and denominator.  Under positivity of both,
    `κ₁ < 0` holds iff `√π < N/D < √(2π)`; equivalently,
    `π < (N/D)² < 2π`. -/
theorem gaussianSwitchingMean_kappa_neg_iff {σ d : ℝ}
    (hN : 0 < gaussianSwitchingMeanNum σ d)
    (hD : 0 < gaussianSwitchingMeanDen σ d) :
    gaussianSwitchingMeanKappa1 σ d < 0 ↔
    Real.pi * gaussianSwitchingMeanDen σ d ^ 2 <
        gaussianSwitchingMeanNum σ d ^ 2 ∧
    gaussianSwitchingMeanNum σ d ^ 2 <
        2 * Real.pi * gaussianSwitchingMeanDen σ d ^ 2 := by
  set N := gaussianSwitchingMeanNum σ d with hN_def
  set D := gaussianSwitchingMeanDen σ d with hD_def
  have hπ_pos : 0 < Real.pi := Real.pi_pos
  have hπ_lt_2π : Real.pi < 2 * Real.pi := by linarith
  have h_ND_pos : 0 < N / D := div_pos hN hD
  have h_NDsq_pos : 0 < (N / D) ^ 2 := pow_pos h_ND_pos 2
  have hD_sq_pos : 0 < D ^ 2 := pow_pos hD 2
  have h_log4_pos : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have h_log_ND_sq : Real.log ((N / D) ^ 2) = 2 * Real.log (N / D) := by
    rw [Real.log_pow]; push_cast; ring
  have h_NDsq_eq : (N / D) ^ 2 = N ^ 2 / D ^ 2 := by field_simp
  unfold gaussianSwitchingMeanKappa1
  set t := Real.log Real.pi - 2 * Real.log (N / D) with ht_def
  constructor
  · intro h_neg
    have h_ratio_lt : Real.log 4 / t < -2 := by linarith
    have ht_ne : t ≠ 0 := by
      intro h
      rw [h, div_zero] at h_ratio_lt
      linarith
    have ht_neg : t < 0 := by
      rcases lt_trichotomy t 0 with h | h | h
      · exact h
      · exact absurd h ht_ne
      · have : 0 < Real.log 4 / t := div_pos h_log4_pos h
        linarith
    have h_logπ_lt : Real.log Real.pi < Real.log ((N / D) ^ 2) := by
      rw [h_log_ND_sq]; linarith
    have h_π_lt_NDsq : Real.pi < (N / D) ^ 2 :=
      (Real.log_lt_log_iff hπ_pos h_NDsq_pos).mp h_logπ_lt
    have h_πD_lt_N : Real.pi * D ^ 2 < N ^ 2 := by
      have h := mul_lt_mul_of_pos_right h_π_lt_NDsq hD_sq_pos
      rwa [h_NDsq_eq, div_mul_cancel₀ _ hD_sq_pos.ne'] at h
    refine ⟨h_πD_lt_N, ?_⟩
    have h_log4_gt : -2 * t < Real.log 4 := by
      rw [div_lt_iff_of_neg ht_neg] at h_ratio_lt
      linarith
    have h_log_NDpow4 : Real.log ((N / D) ^ 4) = 4 * Real.log (N / D) := by
      rw [Real.log_pow]; push_cast; ring
    have h_NDpow4_pos : 0 < (N / D) ^ 4 := pow_pos h_ND_pos 4
    have h_4πsq_pos : 0 < 4 * Real.pi ^ 2 := by positivity
    have h_log_4πsq : Real.log (4 * Real.pi ^ 2)
        = Real.log 4 + 2 * Real.log Real.pi := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      push_cast; ring
    have h_log_step : Real.log ((N / D) ^ 4) < Real.log (4 * Real.pi ^ 2) := by
      rw [h_log_NDpow4, h_log_4πsq]; linarith
    have h_NDpow4_lt : (N / D) ^ 4 < 4 * Real.pi ^ 2 :=
      (Real.log_lt_log_iff h_NDpow4_pos h_4πsq_pos).mp h_log_step
    have h_2π_pos : 0 < 2 * Real.pi := by linarith
    have h_NDsq_lt_2π : (N / D) ^ 2 < 2 * Real.pi := by
      nlinarith [h_NDsq_pos, h_2π_pos, h_NDpow4_lt, sq_nonneg ((N / D) ^ 2 - 2 * Real.pi)]
    have h_step := mul_lt_mul_of_pos_right h_NDsq_lt_2π hD_sq_pos
    rw [h_NDsq_eq, div_mul_cancel₀ _ hD_sq_pos.ne'] at h_step
    linarith
  · rintro ⟨h_πD_lt_N, h_N_lt_2πD⟩
    have h_π_lt_NDsq : Real.pi < (N / D) ^ 2 := by
      rw [h_NDsq_eq, lt_div_iff₀ hD_sq_pos]; linarith
    have h_NDsq_lt_2π : (N / D) ^ 2 < 2 * Real.pi := by
      rw [h_NDsq_eq, div_lt_iff₀ hD_sq_pos]; linarith
    have h_logπ_lt : Real.log Real.pi < Real.log ((N / D) ^ 2) :=
      (Real.log_lt_log_iff hπ_pos h_NDsq_pos).mpr h_π_lt_NDsq
    have ht_neg : t < 0 := by
      rw [ht_def, h_log_ND_sq] at *
      linarith
    have h_NDpow4_pos : 0 < (N / D) ^ 4 := pow_pos h_ND_pos 4
    have h_2π_pos : 0 < 2 * Real.pi := by linarith
    have h_NDpow4_lt : (N / D) ^ 4 < 4 * Real.pi ^ 2 := by
      nlinarith [h_NDsq_pos, h_2π_pos, h_NDsq_lt_2π, sq_nonneg ((N / D) ^ 2 - 2 * Real.pi)]
    have h_log_NDpow4 : Real.log ((N / D) ^ 4) = 4 * Real.log (N / D) := by
      rw [Real.log_pow]; push_cast; ring
    have h_log_4πsq : Real.log (4 * Real.pi ^ 2)
        = Real.log 4 + 2 * Real.log Real.pi := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      push_cast; ring
    have h_4πsq_pos : 0 < 4 * Real.pi ^ 2 := by positivity
    have h_log_step : Real.log ((N / D) ^ 4) < Real.log (4 * Real.pi ^ 2) :=
      (Real.log_lt_log_iff h_NDpow4_pos h_4πsq_pos).mpr h_NDpow4_lt
    rw [h_log_NDpow4, h_log_4πsq] at h_log_step
    have h_log4_gt : -2 * t < Real.log 4 := by linarith
    have h_ratio_lt : Real.log 4 / t < -2 := by
      rw [div_lt_iff_of_neg ht_neg]; linarith
    linarith

end TailOptionPricing
