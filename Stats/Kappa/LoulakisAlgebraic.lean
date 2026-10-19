module

/-
  Taleb's κ-metric for pre-asymptotic fat-tailedness.
    "How Much Data Do You Need?  A Pre-asymptotic Metric for Fat-tailedness"
    arXiv:1802.05495v3 (Nov 2018).

  ## Stats.Kappa.LoulakisAlgebraic — Loulakis algebraic lower bound on `M(n)`.

  Combines the four pieces:

  * **B.6 layer cake** ([MadLayerCake](Stats/Kappa/MadLayerCake.lean)):
    `𝔼|S_n − n·m| = 2 · ∫_{t > 0} ℙ(S_n > n·m + t) dt` when `𝔼[S_n] = n·m`.
  * **C.2 sum ≥ max** ([SumMaxBound](Stats/Kappa/SumMaxBound.lean)):
    `ℙ(S_n > u) ≥ ℙ(max Y_i > u)` for nonneg `Y`.
  * **C.1 inclusion-exclusion** ([MaxIIdBound](Stats/Kappa/MaxIIdBound.lean)):
    `ℙ(max Y_i > u) ≥ n·ℙ(Y₀ > u) − C(n,2)·ℙ(Y₀ > u)²` for iid `Y`.

  Yields the **algebraic Loulakis lower bound** (paper "Lognormal Sums"
  Loulakis remark, generalised to any nonneg iid family with mean `m`):

      `M(n; iid_Y) ≥ 2n · A(n) − 2·C(n,2) · B(n)`

  where
      `A(n) := ∫_{t > 0} ℙ(Y₀ > n·m + t) dt`,
      `B(n) := ∫_{t > 0} ℙ(Y₀ > n·m + t)² dt`.

  This is purely algebraic — no σ→∞ limit yet.  The σ→∞ analysis
  (combining with Hölder/[LognormalMarkov](Stats/Kappa/LognormalMarkov.lean)
  to get `liminf σ→∞ M(n)/M(1) ≥ n` for the lognormal) is the
  remaining piece, deferred to a focused asymptotic-analysis session.
-/
public import Stats.Kappa.MaxIIdBound
public import Stats.Kappa.SumMaxBound
public import Stats.Kappa.MadLayerCake
public import Stats.Kappa.IIdTriangle
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace TailOptionPricing.LoulakisAlgebraic

variable {Ω : Type*} {m_meas : MeasurableSpace Ω} {μ : Measure Ω}
variable {Ω' : Type*} {m'_meas : MeasurableSpace Ω'} {ν : Measure Ω'}

/-! ### The Loulakis algebraic bound.

For an iid nonneg family `X : Fin n → Ω → ℝ` with common law `Y₀ : Ω' → ℝ`
and `𝔼[Y₀] = m` (per-summand mean), the partial-sum MAD admits the
inclusion-exclusion lower bound

    `M(n) = 𝔼|S_n − n·m| ≥ 2n · A − 2·C(n,2) · B`,

where `A := ∫_{t > 0} ℙ(Y₀ > n·m + t) dt` and
`B := ∫_{t > 0} ℙ(Y₀ > n·m + t)² dt`.

The proof chains:

1.  `M(n) = 2 · ∫_{t > 0} ℙ(S_n > n·m + t) dt`  (layer cake, B.6).
2.  Pointwise:  `ℙ(S_n > u) ≥ ℙ(max X_i > u)` for nonneg X (C.2).
3.  Pointwise:  `ℙ(max X_i > u) ≥ n·ℙ(Y₀ > u) − C(n,2)·ℙ(Y₀ > u)²` (C.1).
4.  Integrate, linearity. -/

/-- **Loulakis algebraic lower bound on `M(n)`.**  For an iid nonneg
    family `X : Fin n → Ω → ℝ` with common law `Y₀ : Ω' → ℝ`,
    with an integrable sum whose mean is `n*m`,

        `𝔼_μ |S_n − n·m|
           ≥ 2n · ∫_{t > 0} ℙ_ν(Y₀ > n·m + t) dt
             − 2·C(n,2) · ∫_{t > 0} ℙ_ν(Y₀ > n·m + t)² dt`.

    Hypotheses bundle the iid structure, sum integrability, non-negativity,
    measurability, the sum-mean condition and the needed tail-integral
    convergence. Separate unused assumptions on the representative's
    mean and integrability are removed. Combined with the lognormal
    Hölder bound ([LognormalMarkov](Stats/Kappa/LognormalMarkov.lean))
    and the σ→∞ asymptotic of `M(1; σ)`, this yields
    `liminf_{σ → ∞} M(n; σ)/M(1; σ) ≥ n` (paper Loulakis result). -/
theorem M_n_lower_bound
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {n : ℕ} {Y₀ : Ω' → ℝ} {X : Fin n → Ω → ℝ}
    (h_meas_Y : Measurable Y₀)
    (h_meas : ∀ i, Measurable (X i))
    (h_indep : iIndepFun X μ)
    (h_id : ∀ i, IdentDistrib (X i) Y₀ μ ν)
    (h_nonneg : ∀ i ω, 0 ≤ X i ω)
    {m : ℝ}
    (h_S_int : Integrable (fun ω => ∑ i, X i ω) μ)
    (h_S_mean : (∫ ω, ∑ i, X i ω ∂μ) = (n : ℝ) * m)
    (h_pmax_int : MeasureTheory.IntegrableOn
      (fun t => ν.real {ω' | Y₀ ω' > (n : ℝ) * m + t}) (Set.Ioi (0 : ℝ)))
    (h_pmax_sq_int : MeasureTheory.IntegrableOn
      (fun t => (ν.real {ω' | Y₀ ω' > (n : ℝ) * m + t}) ^ 2)
      (Set.Ioi (0 : ℝ)))
    (h_psum_int : MeasureTheory.IntegrableOn
      (fun t => μ.real {ω | (∑ i, X i ω) > (n : ℝ) * m + t}) (Set.Ioi (0 : ℝ))) :
    (2 : ℝ) * (
        ((n : ℝ) * ∫ t in Set.Ioi (0 : ℝ), ν.real {ω' | Y₀ ω' > (n : ℝ) * m + t})
        - ((n.choose 2 : ℝ) *
            ∫ t in Set.Ioi (0 : ℝ), (ν.real {ω' | Y₀ ω' > (n : ℝ) * m + t}) ^ 2))
      ≤ ∫ ω, |(∑ i, X i ω) - (n : ℝ) * m| ∂μ := by
  -- Step 1: Layer cake — express MAD as 2 · ∫ tail.
  rw [TailOptionPricing.MadLayerCake.mad_eq_two_tail_integral h_S_int ((n : ℝ) * m) h_S_mean]
  -- Goal: 2n · A − 2 C(n,2) · B ≤ 2 · ∫_{t > 0} ℙ(S_n > nm + t) dt
  -- Step 2 & 3: Pointwise on (t > 0),
  --   ℙ(S_n > nm + t) ≥ ℙ(max X_i > nm + t) ≥ n · ℙ_ν(Y₀ > nm + t) − C(n,2) · ℙ_ν(Y₀ > nm + t)²
  -- Hence ∫_{t > 0} ℙ(S_n > nm + t) ≥ ∫_{t > 0} (n · p − C(n,2) · p²)  where p := ℙ_ν(Y₀ > ...).
  have h_pointwise : ∀ t > (0 : ℝ),
      (n : ℝ) * ν.real {ω' | Y₀ ω' > (n : ℝ) * m + t}
        - (n.choose 2 : ℝ) * (ν.real {ω' | Y₀ ω' > (n : ℝ) * m + t}) ^ 2
      ≤ μ.real {ω | (∑ i, X i ω) > (n : ℝ) * m + t} := by
    intro t _
    set u : ℝ := (n : ℝ) * m + t with hu_def
    -- Combine C.1 and C.2.
    have h_C1 := TailOptionPricing.MaxIIdBound.prob_max_iid_ge
      (μ := μ) (ν := ν) (Y := Y₀) (X := X) h_meas_Y h_meas h_indep h_id u
    have h_C2 := TailOptionPricing.SumMaxBound.prob_sum_ge_prob_max
      (μ := μ) (X := X) h_nonneg u
    linarith
  -- Step 4: Integrate the pointwise inequality.
  have h_int_lhs :
      ∫ t in Set.Ioi (0 : ℝ),
        ((n : ℝ) * ν.real {ω' | Y₀ ω' > (n : ℝ) * m + t}
          - (n.choose 2 : ℝ) *
              (ν.real {ω' | Y₀ ω' > (n : ℝ) * m + t}) ^ 2)
      ≤ ∫ t in Set.Ioi (0 : ℝ),
          μ.real {ω | (∑ i, X i ω) > (n : ℝ) * m + t} := by
    apply MeasureTheory.setIntegral_mono_on
    · -- integrability of LHS: linear combo of integrable pieces.
      exact (h_pmax_int.const_mul (n : ℝ)).sub
        (h_pmax_sq_int.const_mul (n.choose 2 : ℝ))
    · -- integrability of RHS: assumed as `h_psum_int`.
      exact h_psum_int
    · exact measurableSet_Ioi
    · intros t ht
      exact h_pointwise t ht
  -- Combine with the layer cake of M(n).
  -- Goal: 2n · ∫ A − 2C(n,2) · ∫ B ≤ 2 · ∫ ℙ(S_n > nm + t) dt.
  -- After integrating, LHS = ∫ (n·p − C(n,2)·p²) dt (linear).
  have h_lhs_eq :
      ∫ t in Set.Ioi (0 : ℝ),
        ((n : ℝ) * ν.real {ω' | Y₀ ω' > (n : ℝ) * m + t}
          - (n.choose 2 : ℝ) *
              (ν.real {ω' | Y₀ ω' > (n : ℝ) * m + t}) ^ 2)
      = ((n : ℝ) * ∫ t in Set.Ioi (0 : ℝ),
            ν.real {ω' | Y₀ ω' > (n : ℝ) * m + t})
        - ((n.choose 2 : ℝ) * ∫ t in Set.Ioi (0 : ℝ),
            (ν.real {ω' | Y₀ ω' > (n : ℝ) * m + t}) ^ 2) := by
    rw [integral_sub (h_pmax_int.const_mul _) (h_pmax_sq_int.const_mul _),
        integral_const_mul, integral_const_mul]
  rw [h_lhs_eq] at h_int_lhs
  -- Multiply by 2: 2 · (n · ∫A − C(n,2) · ∫B) ≤ 2 · ∫D — matches goal directly.
  exact mul_le_mul_of_nonneg_left h_int_lhs (by norm_num : (0:ℝ) ≤ 2)

end TailOptionPricing.LoulakisAlgebraic
