module

/-
  Taleb's κ-metric for pre-asymptotic fat-tailedness.
    "How Much Data Do You Need?  A Pre-asymptotic Metric for Fat-tailedness"
    arXiv:1802.05495v3 (Nov 2018).

  ## Stats.Kappa.LognormalMeasure — Lognormal as a probability measure.

  Mathlib provides `gaussianReal` but no `lognormalReal`.  This module
  fills the gap:

      `lognormalReal μ v := (gaussianReal μ v).map Real.exp`,

  i.e. the push-forward of the Gaussian (location μ, variance v) under
  the exponential map.  If `Z ∼ 𝒩(0, 1)`, then
      `exp(μ + √v · Z) ∼ lognormalReal μ v`.

  Theorems delivered (todo5.md Phase B.1–B.4):

  * `lognormalReal` — paper definition.
  * `instIsProbabilityMeasureLognormalReal` — probability instance.
  * `lognormalReal_Ioi_zero_eq_one` — supported on `(0, ∞)`.
  * `lognormalReal_real_Ioi` — tail formula via `stdNormalCdf`:
      `(lognormalReal μ v).real (Ioi x) = 1 − Φ((log x − μ)/√v)` for `x > 0`.

  Prerequisite for `Stats.Kappa.Lognormal.Loulakis` (todo5.md Phase C).
-/
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Stats.BlackScholes.StdNormal

@[expose] public section

open MeasureTheory ProbabilityTheory Real Set
open scoped NNReal

namespace TailOptionPricing.LognormalMeasure

/-- **Lognormal distribution on `ℝ`.**  Push-forward of `gaussianReal μ v`
    under `Real.exp`.  If `Y ∼ 𝒩(μ, v)`, then `exp(Y) ∼ lognormalReal μ v`. -/
noncomputable def lognormalReal (μ : ℝ) (v : ℝ≥0) : Measure ℝ :=
  (gaussianReal μ v).map Real.exp

/-- `Real.exp` is measurable (needed for `Measure.map` of probability measures
    to be a probability measure). -/
private lemma measurable_exp : Measurable (Real.exp) := Real.continuous_exp.measurable

/-- **`lognormalReal` is a probability measure.**  Standard fact:
    a push-forward of a probability measure under a measurable map
    is a probability measure (when the map is `AEMeasurable`). -/
instance instIsProbabilityMeasureLognormalReal (μ : ℝ) (v : ℝ≥0) :
    IsProbabilityMeasure (lognormalReal μ v) := by
  unfold lognormalReal
  exact (Measure.isProbabilityMeasure_map_iff measurable_exp.aemeasurable).mpr inferInstance

/-- **`lognormalReal` is supported on `(0, ∞)`.**  Since `Real.exp y > 0`
    for all `y ∈ ℝ`, the push-forward has full mass on `Ioi 0`. -/
theorem lognormalReal_Ioi_zero_eq_one (μ : ℝ) (v : ℝ≥0) :
    (lognormalReal μ v).real (Set.Ioi (0 : ℝ)) = 1 := by
  unfold lognormalReal
  -- Push-forward: ((gauss).map exp).real (Ioi 0) = (gauss).real (exp ⁻¹' Ioi 0).
  rw [Measure.real, Measure.map_apply measurable_exp measurableSet_Ioi]
  -- exp ⁻¹' Ioi 0 = univ since exp y > 0 for all y.
  have h_preimage : Real.exp ⁻¹' Set.Ioi (0 : ℝ) = Set.univ := by
    ext y
    simp [Real.exp_pos]
  rw [h_preimage, measure_univ]
  simp

/-- **Lognormal tail formula** via standard normal CDF.  For `v ≠ 0` and `x > 0`,
        `ℙ(X > x) = 1 − Φ((log x − μ) / √v)`,
    where `X ∼ lognormalReal μ v` and `Φ = stdNormalCdf`. -/
theorem lognormalReal_real_Ioi {μ : ℝ} {v : ℝ≥0} (hv : v ≠ 0)
    {x : ℝ} (hx : 0 < x) :
    (lognormalReal μ v).real (Set.Ioi x)
      = 1 - stdNormalCdf ((Real.log x - μ) / Real.sqrt (v : ℝ)) := by
  unfold lognormalReal
  -- Push-forward: ((gauss).map exp).real (Ioi x) = (gauss).real (exp ⁻¹' Ioi x).
  rw [Measure.real, Measure.map_apply measurable_exp measurableSet_Ioi]
  -- exp ⁻¹' Ioi x = Ioi (log x) since exp is strictly increasing and exp y > x ↔ y > log x.
  have h_preimage : Real.exp ⁻¹' Set.Ioi x = Set.Ioi (Real.log x) := by
    ext y
    simp only [Set.mem_preimage, Set.mem_Ioi]
    constructor
    · intro h
      have := Real.log_lt_log hx h
      rwa [Real.log_exp] at this
    · intro h
      have := Real.exp_lt_exp.mpr h
      rwa [Real.exp_log hx] at this
  rw [h_preimage]
  -- Now: ((gaussianReal μ v) (Ioi (log x))).toReal = 1 − Φ((log x − μ)/√v).
  show ((gaussianReal μ v) (Set.Ioi (Real.log x))).toReal = _
  rw [show ((gaussianReal μ v) (Set.Ioi (Real.log x))).toReal
      = (gaussianReal μ v).real (Set.Ioi (Real.log x)) from rfl]
  rw [gaussianReal_real_Ioi_eq hv (Real.log x)]
  rw [← one_sub_stdNormalCdf]

end TailOptionPricing.LognormalMeasure
