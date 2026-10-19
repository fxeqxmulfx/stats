module

/-
  Error function `Real.erf` and complementary error function `erfc`, and
  their connections to `stdNormalCdf`.  Used to state the paper's Eq. (10)
  lower bound `α ≥ log((1/2)·erfc(...))` in the same notation as the paper,
  and the Section IV-D switching-mean κ₁ closed form (Eq. 18) consumed by
  `Stats.Kappa.GaussianSwitchingMean`.

  Both `Real.erf` and `erfc` are defined here as wrappers around
  `stdNormalCdf`, consistent with the standard integral forms
      `erf(x)  = (2/√π) ∫_0^x exp(−t²) dt`,
      `erfc(x) = (2/√π) ∫_x^∞ exp(−t²) dt`;
  the integral forms are not formalised here.  Mathlib at `v4.29.0` has
  no `Real.erf`, so this file fills that gap (compatible with a future
  Mathlib upgrade — Mathlib's `Real.erf`, if added, would simply
  supersede this definition).
-/
public import Stats.BlackScholes.CallPrice

@[expose] public section

open Set MeasureTheory Filter Topology
open scoped NNReal

namespace Real

/-- **Error function** (functional definition).  `Real.erf x` is the
    standardised central probability of a `𝒩(0, 1)` variable:
        `Real.erf x = 2 · Φ(x · √2) − 1`,
    matching the standard integral form
        `erf(x) = (2/√π) ∫_0^x exp(−t²) dt`
    via the change of variables `t = u/√2`.  Defined here as a wrapper
    around `TailOptionPricing.stdNormalCdf`; the integral form is left
    to future Mathlib infrastructure. -/
noncomputable def erf (x : ℝ) : ℝ :=
  2 * TailOptionPricing.stdNormalCdf (x * Real.sqrt 2) - 1

end Real

namespace TailOptionPricing

/-- **Complementary error function** (functional definition).  `erfc(x)` is
    the standard normal tail rescaled and translated:
        `erfc(x) = 2 · (1 − Φ(x · √2))`.
    The integral form `erfc(x) = (2/√π) ∫_x^∞ exp(−t²) dt` follows by the
    change of variables `t = u/√2`. -/
noncomputable def erfc (x : ℝ) : ℝ := 2 * (1 - stdNormalCdf (x * Real.sqrt 2))

/-- **Complementarity identity**: `Real.erf x + erfc x = 1`. -/
theorem erf_add_erfc (x : ℝ) : Real.erf x + erfc x = 1 := by
  unfold Real.erf erfc
  ring

/-- **Standard normal tail in `erfc` form.**  `1 − Φ(c) = (1/2) · erfc(c/√2)`. -/
theorem one_sub_stdNormalCdf_eq_half_erfc (c : ℝ) :
    1 - stdNormalCdf c = (1/2) * erfc (c / Real.sqrt 2) := by
  unfold erfc
  have h_sqrt_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have h_sqrt_ne : Real.sqrt 2 ≠ 0 := h_sqrt_pos.ne'
  rw [div_mul_cancel₀ c h_sqrt_ne]
  ring

open ProbabilityTheory MeasureTheory in
/-- **Risk-neutral lognormal survival in `erfc` form.**  Specialising
    `survivalLN_eq_one_sub_stdNormalCdf` and rewriting via `erfc`:
        `survivalLN S₀ μ v K = (1/2) · erfc((log(K/S₀) − μ)/(√v · √2))`.
    Direct restatement of the paper's `(1/2) erfc(d₂*/√2)` notation. -/
theorem survivalLN_eq_half_erfc {S₀ μ s : ℝ} {v : ℝ≥0}
    (hS₀ : 0 < S₀) (hv : v ≠ 0) (hs : 0 < s) :
    survivalLN S₀ μ v s =
    (1/2) * erfc ((Real.log (s / S₀) - μ) / (Real.sqrt (v : ℝ) * Real.sqrt 2)) := by
  rw [survivalLN_eq_one_sub_stdNormalCdf hS₀ hv hs,
      one_sub_stdNormalCdf_eq_half_erfc]
  congr 2
  rw [div_div]

open ProbabilityTheory MeasureTheory in
/-- **Eq. (10), paper-style `erfc` form.**  Combining the lognormal BS-tail
    dominance theorem with the `erfc` rewrite:
        `α ≥ log((1/2) · erfc((log(K₁/S₀) − μ) / (√v · √2))) / log(l/K₁)`. -/
theorem alpha_lower_bound_erfc
    {l α S₀ μ K₁ a : ℝ} {v : ℝ≥0}
    (hα : 1 < α) (hl : 0 < l) (hK₁ : l < K₁)
    (hS₀ : 0 < S₀) (hv : v ≠ 0) (ha_pos : 0 < a) (ha_lt : a < K₁)
    (h_match : (∫ s in Set.Ioi K₁, survivalLN S₀ μ v s) = callPrice l α K₁)
    (h_butterfly : ∀ᶠ ΔK in 𝓝[>] (0:ℝ),
        callPrice l α (K₁ + ΔK) +
          (∫ s in Set.Ioi (K₁ - ΔK), survivalLN S₀ μ v s)
          ≥ 2 * callPrice l α K₁) :
    Real.log ((1/2) *
        erfc ((Real.log (K₁ / S₀) - μ) /
          (Real.sqrt (v : ℝ) * Real.sqrt 2))) /
      Real.log (l / K₁) ≤ α := by
  have h := BSC_lognormal_tail_dominates_at_match
    hα hl hK₁ hS₀ hv ha_pos ha_lt h_match h_butterfly
  rw [survivalLN_eq_half_erfc hS₀ hv (hl.trans hK₁)] at h
  exact alpha_lower_bound hl hK₁ h

end TailOptionPricing
