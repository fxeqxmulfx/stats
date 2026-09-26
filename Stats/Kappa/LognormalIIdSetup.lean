/-
  Taleb's κ-metric for pre-asymptotic fat-tailedness.
    "How Much Data Do You Need?  A Pre-asymptotic Metric for Fat-tailedness"
    arXiv:1802.05495v3 (Nov 2018).

  ## Stats.Kappa.LognormalIIdSetup — n-fold iid lognormal construction.

  Sets up the n-fold iid lognormal family used by the Loulakis liminf
  argument (todo6.md Phase 6.1).  Single fixed product space
      `(Ω_n, μ_n) := (Fin n → ℝ,  Measure.pi (fun _ => gaussianReal 0 1))`,
  with σ-parametrised iid family
      `X σ i ω := Y σ (ω i) = exp(σ · ω_i − σ²/2)`.

  Then `X σ i` are iid lognormal `lognormalReal (−σ²/2) σ²` for each σ.

  This file delivers:

  * `Ωspace n : Type` = `Fin n → ℝ`.
  * `μn n : Measure (Ωspace n)` = `Measure.pi (fun _ => gaussianReal 0 1)`.
  * `Xσ σ i : Ωspace n → ℝ`, `Xσ σ i ω := Y σ (ω i)`.
  * Measurability, iIndepFun, IdentDistrib structure.
  * Non-negativity, integrability, partial-sum mean `n`.
-/
import Stats.Kappa.LognormalAsymptotic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Independence.Basic

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal

namespace TailOptionPricing.LognormalIIdSetup

open TailOptionPricing.LognormalAsymptotic (Y Y_pos Y_nonneg integral_Y_eq_one)

/-! ### Sample space and measure. -/

/-- **n-fold sample space** `Ωspace n := Fin n → ℝ`. -/
abbrev Ωspace (n : ℕ) : Type := Fin n → ℝ

/-- **n-fold product of `gaussianReal 0 1`**. -/
noncomputable def μn (n : ℕ) : Measure (Ωspace n) :=
  Measure.pi (fun _ : Fin n => gaussianReal 0 1)

instance (n : ℕ) : IsProbabilityMeasure (μn n) := by
  unfold μn; infer_instance

/-! ### iid family. -/

/-- **i-th iid `Y σ`-copy** under the n-fold product.  `Xσ σ i ω := Y σ (ω i)`. -/
noncomputable def Xσ (σ : ℝ) {n : ℕ} (i : Fin n) (ω : Ωspace n) : ℝ :=
  Y σ (ω i)

theorem Xσ_pos (σ : ℝ) {n : ℕ} (i : Fin n) (ω : Ωspace n) : 0 < Xσ σ i ω :=
  Y_pos σ _

theorem Xσ_nonneg (σ : ℝ) {n : ℕ} (i : Fin n) (ω : Ωspace n) : 0 ≤ Xσ σ i ω :=
  (Xσ_pos σ i ω).le

theorem measurable_Xσ (σ : ℝ) {n : ℕ} (i : Fin n) : Measurable (Xσ σ i) := by
  unfold Xσ Y
  exact (Real.continuous_exp.measurable.comp
    ((measurable_const.mul (measurable_pi_apply i)).sub measurable_const))

/-! ### iIndepFun structure. -/

/-- **iid independence** of the `Xσ σ i` family. -/
theorem iIndepFun_Xσ (σ : ℝ) (n : ℕ) :
    iIndepFun (fun i : Fin n => Xσ σ i) (μn n) := by
  unfold μn Xσ
  exact iIndepFun_pi (fun _ => (Real.continuous_exp.measurable.comp
    ((measurable_const.mul measurable_id).sub measurable_const)).aemeasurable)

/-! ### IdentDistrib with the single-Y-on-(ℝ, gauss 0 1) representative. -/

/-- **Each `Xσ σ i` is identically distributed with the underlying `Y σ`** (on
    the standard Gaussian sample space `(ℝ, gaussianReal 0 1)`). -/
theorem identDistrib_Xσ (σ : ℝ) {n : ℕ} (i : Fin n) :
    IdentDistrib (Xσ σ i) (Y σ) (μn n) (gaussianReal 0 1) := by
  have h_meas_Y : Measurable (Y σ) := by
    unfold Y; fun_prop
  have h_meas_X : Measurable (Xσ σ i) := measurable_Xσ σ i
  refine ⟨h_meas_X.aemeasurable, h_meas_Y.aemeasurable, ?_⟩
  -- Pushforward equality via `measurePreserving_eval`.
  -- `Xσ σ i = Y σ ∘ eval i`, so `(μn).map (Xσ σ i) = ((μn).map (eval i)).map (Y σ)
  --   = (gaussianReal 0 1).map (Y σ)`.
  have h_xeq : Xσ σ i = (Y σ) ∘ (Function.eval i : Ωspace n → ℝ) := rfl
  rw [h_xeq, ← Measure.map_map h_meas_Y (measurable_pi_apply i)]
  congr 1
  exact (measurePreserving_eval i (μ := fun _ : Fin n => gaussianReal 0 1)).map_eq

/-! ### Sum of iid lognormals: integrability + mean. -/

/-- **Integrability of `Xσ σ i`** under `μn n`. -/
theorem integrable_Xσ (σ : ℝ) {n : ℕ} (i : Fin n) :
    Integrable (Xσ σ i) (μn n) := by
  have hY_int : Integrable (Y σ) (gaussianReal 0 1) := by
    unfold Y
    have h_factor : (fun ω => Real.exp (σ * ω - σ^2 / 2))
        = (fun ω => Real.exp (-(σ^2/2)) * Real.exp (σ * ω)) := by
      funext ω; rw [← Real.exp_add]; congr 1; ring
    rw [h_factor]
    exact (integrable_exp_mul_gaussianReal σ).const_mul _
  exact ((identDistrib_Xσ σ i).integrable_iff).mpr hY_int

/-- **Integrability of the partial sum** `S_n σ ω := ∑ i, Xσ σ i ω` under `μn n`. -/
theorem integrable_sum_Xσ (σ : ℝ) (n : ℕ) :
    Integrable (fun ω => ∑ i, Xσ σ i ω) (μn n) :=
  integrable_finset_sum _ (fun i _ => integrable_Xσ σ i)

/-- **Mean of `Xσ σ i` under `μn n` is 1.**  By `IdentDistrib` with `Y σ`,
    whose mean is 1 (from [`LognormalAsymptotic.integral_Y_eq_one`](Stats/Kappa/LognormalAsymptotic.lean)). -/
theorem integral_Xσ_eq_one (σ : ℝ) {n : ℕ} (i : Fin n) :
    (∫ ω, Xσ σ i ω ∂(μn n)) = 1 := by
  rw [(identDistrib_Xσ σ i).integral_eq, integral_Y_eq_one σ]

/-- **Mean of the partial sum is `n`**. -/
theorem integral_sum_Xσ_eq (σ : ℝ) (n : ℕ) :
    (∫ ω, ∑ i, Xσ σ i ω ∂(μn n)) = (n : ℝ) := by
  rw [integral_finset_sum _ (fun i _ => integrable_Xσ σ i)]
  simp [integral_Xσ_eq_one σ]

end TailOptionPricing.LognormalIIdSetup
