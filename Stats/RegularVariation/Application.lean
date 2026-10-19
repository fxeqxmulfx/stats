module

/-
  Karamata's theory of regular variation — application to Theorem 1.

  Closes the gap in `survivalLogReturn_not_regularlyVarying_slow`
  (the `h_subexp` hypothesis is now derivable from "L slowly varying"
  given measurability or monotonicity), turning Theorem 1 into a direct
  corollary.
-/
public import Stats.RegularVariation.Karamata

@[expose] public section

open Real Set Filter Topology Asymptotics

namespace TailOptionPricing

/-- **Theorem 1, full slowly-varying form (monotone case).**  For any
    monotone (on `[T₀, ∞)`), eventually positive, slowly varying `L` and
    any `α > 0, s₀ > 0`, the survival of `r_l = log(S/s₀)` under
    `bF(s) = L(s)·s^(−α)` is *not* regularly varying with any real index.

    This is `survivalLogReturn_not_regularlyVarying_slow` with the Karamata
    bound discharged via `log_isLittleO_log_of_monotone`. -/
theorem survivalLogReturn_not_regularlyVarying_full_of_monotone
    {L : ℝ → ℝ} {α s₀ : ℝ}
    (hα : 0 < α) (hs₀ : 0 < s₀)
    (hL : IsSlowlyVarying L)
    (hL_pos : ∀ᶠ s in atTop, 0 < L s)
    (hL_mono : ∃ T₀ > 0, MonotoneOn L (Set.Ici T₀)) (ρ : ℝ) :
    ¬ IsRegularlyVarying
      (fun x => L (s₀ * Real.exp x) * (s₀ * Real.exp x) ^ (-α)) ρ :=
  survivalLogReturn_not_regularlyVarying_slow hα hs₀ hL_pos
    (hL.subexp_along_exp_grid_of_monotone hL_pos hL_mono hs₀) ρ

/-- **Theorem 1, full slowly-varying form (measurable case).**  For any
    measurable, eventually positive, slowly varying `L` and any
    `α > 0, s₀ > 0`, the survival of `r_l = log(S/s₀)` under
    `bF(s) = L(s)·s^(−α)` is *not* regularly varying with any real index.

    This is `survivalLogReturn_not_regularlyVarying_slow` with the Karamata
    bound discharged via `log_isLittleO_log` (measurable Korevaar UCT). -/
theorem survivalLogReturn_not_regularlyVarying_full
    {L : ℝ → ℝ} {α s₀ : ℝ}
    (hα : 0 < α) (hs₀ : 0 < s₀)
    (hL : IsSlowlyVarying L)
    (hL_pos : ∀ᶠ s in atTop, 0 < L s)
    (hL_meas : Measurable L) (ρ : ℝ) :
    ¬ IsRegularlyVarying
      (fun x => L (s₀ * Real.exp x) * (s₀ * Real.exp x) ^ (-α)) ρ :=
  survivalLogReturn_not_regularlyVarying_slow hα hs₀ hL_pos
    (hL.subexp_along_exp_grid hL_pos hL_meas hs₀) ρ

end TailOptionPricing
