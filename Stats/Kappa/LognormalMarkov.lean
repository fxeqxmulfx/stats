module

/-
  Taleb's κ-metric for pre-asymptotic fat-tailedness.
    "How Much Data Do You Need?  A Pre-asymptotic Metric for Fat-tailedness"
    arXiv:1802.05495v3 (Nov 2018).

  ## Stats.Kappa.LognormalMarkov — Hölder/Markov upper bound on lognormal tail.

  For `Y ~ lognormalReal μ v` and `γ ≥ 0`, the moment formula
      `𝔼[Y^γ] = exp(γ·μ + γ²·v/2)`
  combined with Markov gives
      `ℙ(Y > t) ≤ t^{-γ} · exp(γ·μ + γ²·v/2)` for `t > 0`.

  This is the key Hölder-style bound in the Loulakis subexponentiality
  argument (paper "Lognormal Sums" appendix).  With `μ = -v/2` (so
  `𝔼Y = 1`), it specialises to
      `ℙ(Y > t) ≤ t^{-γ} · exp(γ(γ−1)·v/2)`,
  whose exponent `γ(γ−1)/2` is *negative* for `γ ∈ (0, 1)` — i.e. the
  bound *improves* as `v = σ² → ∞`.  This is the mechanism by which
  the Loulakis inclusion-exclusion second-order term vanishes
  asymptotically.

  Proof: pull the lognormal tail back to a Gaussian half-line via
  `lognormalReal_real_Ioi` (Phase B.4), then apply the Chernoff bound
  `measure_ge_le_exp_mul_mgf` with Mathlib's
  `integrable_exp_mul_gaussianReal` + `mgf_id_gaussianReal`.
-/
public import Stats.Kappa.LognormalMeasure
public import Mathlib.Probability.Moments.Basic

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

namespace TailOptionPricing.LognormalMarkov

/-! ### Gaussian Chernoff specialisation. -/

/-- **Gaussian Chernoff** (specialised to the standard Gaussian on a half-line).
    For `Z ~ gaussianReal μ v` and `γ ≥ 0`,
        `ℙ(Z ≥ ε) ≤ exp(−γ·ε + γ·μ + v·γ²/2)`.
    Direct application of Mathlib's `measure_ge_le_exp_mul_mgf` with
    `mgf_id_gaussianReal` substituted in. -/
theorem gaussianReal_real_Ici_le (μ : ℝ) (v : ℝ≥0)
    (ε : ℝ) {γ : ℝ} (hγ : 0 ≤ γ) :
    (gaussianReal μ v).real {x | ε ≤ x}
      ≤ Real.exp (-γ * ε + γ * μ + (v : ℝ) * γ ^ 2 / 2) := by
  -- `measure_ge_le_exp_mul_mgf : μ.real {ε ≤ X ω} ≤ exp(-γ ε) · mgf X μ γ`.
  -- Specialise to `X = id`, `μ = gaussianReal μ v`.
  have h_int : Integrable (fun x => Real.exp (γ * x)) (gaussianReal μ v) :=
    integrable_exp_mul_gaussianReal γ
  have h_chernoff := measure_ge_le_exp_mul_mgf (X := id) (μ := gaussianReal μ v)
    ε hγ h_int
  -- Plug in `mgf id`.
  have h_mgf : mgf id (gaussianReal μ v) γ
      = Real.exp (μ * γ + (v : ℝ) * γ ^ 2 / 2) := by
    rw [mgf_id_gaussianReal]
  rw [h_mgf] at h_chernoff
  have h_set_eq : {ω | ε ≤ id ω} = {x : ℝ | ε ≤ x} := by ext; simp
  rw [h_set_eq] at h_chernoff
  -- Combine exponents.
  have h_exp :
      Real.exp (-γ * ε) * Real.exp (μ * γ + (v : ℝ) * γ ^ 2 / 2)
        = Real.exp (-γ * ε + γ * μ + (v : ℝ) * γ ^ 2 / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  linarith [h_chernoff, h_exp ▸ le_refl (Real.exp _)]

/-! ### Lognormal tail bound. -/

/-- **Hölder/Markov bound on the lognormal tail.**  For
    `Y ~ lognormalReal μ v` (push-forward of `gaussianReal μ v` under
    `Real.exp`), `t > 0`, and `γ ≥ 0`,
        `ℙ(Y > t) ≤ t^{-γ} · exp(γ·μ + v·γ²/2)`.

    Useful corollary in Loulakis form: with `μ = -v/2` (i.e. `𝔼Y = 1`),
    the exponent becomes `γ(γ−1)v/2`, *negative* for `γ ∈ (0, 1)`, so the
    bound *decays* as `v → ∞`. -/
theorem lognormalReal_real_Ioi_le {μ : ℝ} {v : ℝ≥0}
    {t : ℝ} (ht : 0 < t) {γ : ℝ} (hγ : 0 ≤ γ) :
    (TailOptionPricing.LognormalMeasure.lognormalReal μ v).real (Set.Ioi t)
      ≤ t ^ (-γ) * Real.exp (γ * μ + (v : ℝ) * γ ^ 2 / 2) := by
  -- Push back to gaussian half-line via `Real.exp` preimage.
  unfold TailOptionPricing.LognormalMeasure.lognormalReal
  rw [Measure.real, Measure.map_apply Real.continuous_exp.measurable measurableSet_Ioi]
  have h_preimage : Real.exp ⁻¹' Set.Ioi t = Set.Ioi (Real.log t) := by
    ext y
    simp only [Set.mem_preimage, Set.mem_Ioi]
    constructor
    · intro h
      have := Real.log_lt_log ht h
      rwa [Real.log_exp] at this
    · intro h
      have := Real.exp_lt_exp.mpr h
      rwa [Real.exp_log ht] at this
  rw [h_preimage]
  -- `(gauss).real (Ioi (log t)) ≤ (gauss).real (Ici (log t))` (Ioi ⊆ Ici).
  have h_sub : (gaussianReal μ v) (Set.Ioi (Real.log t))
      ≤ (gaussianReal μ v) {x : ℝ | Real.log t ≤ x} := by
    apply measure_mono
    intro x hx
    simp only [Set.mem_ofPred_eq]
    exact le_of_lt hx
  -- Apply Chernoff at ε = log t.
  have h_chern := gaussianReal_real_Ici_le μ v (Real.log t) hγ
  -- `t^(-γ) = exp(-γ · log t)` for t > 0.
  have ht_log : Real.exp (-γ * Real.log t) = t ^ (-γ) := by
    rw [show (-γ : ℝ) * Real.log t = (-γ) * Real.log t from rfl,
        show (-γ : ℝ) * Real.log t = Real.log (t ^ (-γ)) from by
          rw [Real.log_rpow ht (-γ)]]
    exact Real.exp_log (Real.rpow_pos_of_pos ht (-γ))
  -- Combine the exponent and reorder.
  calc ((gaussianReal μ v) (Set.Ioi (Real.log t))).toReal
      ≤ ((gaussianReal μ v) {x | Real.log t ≤ x}).toReal := by
        exact ENNReal.toReal_mono (measure_ne_top _ _) h_sub
    _ = (gaussianReal μ v).real {x | Real.log t ≤ x} := rfl
    _ ≤ Real.exp (-γ * Real.log t + γ * μ + (v : ℝ) * γ ^ 2 / 2) := h_chern
    _ = Real.exp (-γ * Real.log t) *
          Real.exp (γ * μ + (v : ℝ) * γ ^ 2 / 2) := by
        rw [← Real.exp_add]; congr 1; ring
    _ = t ^ (-γ) * Real.exp (γ * μ + (v : ℝ) * γ ^ 2 / 2) := by
        rw [ht_log]

end TailOptionPricing.LognormalMarkov
