/-
  Karamata's theory of regular variation — definitions.

  Defines `IsSlowlyVarying` and connects it to `IsRegularlyVarying _ 0`.
-/
import Stats.Theorem1

open Real Set Filter Topology Asymptotics

namespace TailOptionPricing

/-- A function `L : ℝ → ℝ` is *slowly varying at infinity* iff for every
    `x > 0`, `L(t·x)/L(t) → 1` as `t → ∞`. -/
def IsSlowlyVarying (L : ℝ → ℝ) : Prop :=
  ∀ x : ℝ, 0 < x → Tendsto (fun t => L (t * x) / L t) atTop (𝓝 1)

/-- Slowly varying ⇔ regularly varying with index `0`. -/
theorem isSlowlyVarying_iff_isRegularlyVarying_zero {L : ℝ → ℝ} :
    IsSlowlyVarying L ↔ IsRegularlyVarying L 0 := by
  unfold IsSlowlyVarying IsRegularlyVarying
  simp [Real.rpow_zero]

end TailOptionPricing
