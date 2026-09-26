/-
  Multivariate regular variation (MRV) via projections.

  ## Stats.RegularVariation.Multivariate

  For a random vector `X : Ω → Fin d → ℝ`, we say `X` is multivariate
  regularly varying with index `α` and spectral function `σ` if every
  linear projection `v · X` (for unit-vector `v`) is scalar regularly
  varying with the same index `-α`, with limiting ratio `σ v`.

  This is the Resnick-style projection formulation — it is equivalent
  to the spectral-measure formulation but easier to reason about for
  finite-dimensional purposes (`κ`-invariance across directions, etc.).

  Uses `Fin d → ℝ` with an explicit inner product (no
  `EuclideanSpace`/`InnerProductSpace` dependency).
-/
import Stats.Theorem1
import Mathlib.Analysis.InnerProductSpace.Basic
-- The Mathlib import isn't strictly needed (we don't use InnerProductSpace),
-- but it gives us `Real.sqrt` and related infrastructure.  If it fails,
-- replace with `import Mathlib.Analysis.SpecialFunctions.Pow.Real`.

open Real Set MeasureTheory Filter Topology

namespace TailOptionPricing

variable {d : ℕ}

/-- **Euclidean inner product on `Fin d → ℝ`.**
`⟨v, x⟩ := ∑ i, v i * x i`. -/
noncomputable def euclidInner (v x : Fin d → ℝ) : ℝ :=
  ∑ i, v i * x i

/-- **Euclidean norm on `Fin d → ℝ`.**
`‖x‖ := √(⟨x, x⟩)`. -/
noncomputable def euclidNorm (x : Fin d → ℝ) : ℝ :=
  Real.sqrt (euclidInner x x)

@[simp]
lemma euclidInner_symm (v x : Fin d → ℝ) :
    euclidInner v x = euclidInner x v := by
  unfold euclidInner
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

lemma euclidInner_self_nonneg (x : Fin d → ℝ) :
    0 ≤ euclidInner x x := by
  unfold euclidInner
  exact Finset.sum_nonneg (fun i _ => mul_self_nonneg _)

lemma euclidNorm_nonneg (x : Fin d → ℝ) :
    0 ≤ euclidNorm x :=
  Real.sqrt_nonneg _

@[simp]
lemma euclidNorm_zero : euclidNorm (0 : Fin d → ℝ) = 0 := by
  unfold euclidNorm euclidInner
  simp

lemma euclidInner_add_right (v x y : Fin d → ℝ) :
    euclidInner v (x + y) = euclidInner v x + euclidInner v y := by
  unfold euclidInner
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp [mul_add]

lemma euclidInner_smul_right (v x : Fin d → ℝ) (c : ℝ) :
    euclidInner v (c • x) = c * euclidInner v x := by
  unfold euclidInner
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp [Pi.smul_apply, smul_eq_mul]
  ring

/-- **Multivariate regular variation (projection / Resnick form).**
`X : Ω → Fin d → ℝ` is multivariate regularly varying with index `α`
and spectral function `σ : (Fin d → ℝ) → ℝ` iff, for every unit vector
`v ∈ Fin d → ℝ`, the scalar projection survival
`t ↦ μ.real {ω | t < ⟨v, X ω⟩}` is (i) regularly varying with index
`-α`, and (ii) has the asymptotic ratio `σ v`:
`μ.real {ω | t < ⟨v, X ω⟩} / t^(-α) → σ v` as `t → ∞`. -/
def IsMultivariateRegularlyVarying
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → Fin d → ℝ) (α : ℝ) (σ : (Fin d → ℝ) → ℝ) : Prop :=
  ∀ v : Fin d → ℝ, euclidNorm v = 1 →
    IsRegularlyVarying (fun t : ℝ => μ.real {ω | t < euclidInner v (X ω)}) (-α)
    ∧ Tendsto (fun t : ℝ =>
        μ.real {ω | t < euclidInner v (X ω)} / t ^ (-α))
        atTop (𝓝 (σ v))

end TailOptionPricing
