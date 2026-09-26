/-
  Taleb's κ-metric for pre-asymptotic fat-tailedness.
    "How Much Data Do You Need?  A Pre-asymptotic Metric for Fat-tailedness"
    arXiv:1802.05495v3 (Nov 2018).

  ## Stats.Kappa.Cumulant — General cumulant infrastructure (todo3.md C.4).

  Cumulants of a real random variable `X` w.r.t. a measure `μ`, defined
  as derivatives of the cumulant generating function `cgf X μ t := log
  (mgf X μ t)` at `t = 0`.  Mathlib has `cgf` and its first two
  derivatives; this module wraps them as the cumulant API used by the
  paper:

      K_i(X) := iteratedDeriv i (cgf X μ) 0.

  Theorems delivered (todo3.md C.4):

  * `cumulant` — paper definition.
  * `cumulant_zero` — `K_0 = 0`.
  * `cumulant_one_eq_mean` — `K_1 = μ[X]` (under integrability).
  * `cumulant_two_eq_variance` — `K_2 = Var[X; μ]`.
  * `cumulant_iid_sum` — `K_i(Σ_N X_i) = N · K_i(Y)` for iid sums of
    `IdentDistrib (X i) Y`.
  * `cumulantSkewness`, `cumulantKurtosis` — paper-standard cumulant
    ratios.

  Moment-cumulant linkage `μ_3 = K_3` and `μ_4 = K_4 + 3 K_2²` is
  axiomatised here pending Faà di Bruno machinery for `iteratedDeriv`
  of `log ∘ mgf` at orders ≥ 3 (todo3.md C.4.discharge.moments).

  See `Stats/Kappa.lean` for the umbrella module.
-/
import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.Probability.IdentDistrib

namespace TailOptionPricing

open MeasureTheory ProbabilityTheory Filter Real Set
open scoped Topology

variable {Ω : Type*} {m : MeasurableSpace Ω} {X : Ω → ℝ} {μ : Measure Ω}

/-! ## Cumulant definition and basic identities. -/

/-- **`n`-th cumulant** of a real random variable `X` w.r.t. a measure
    `μ`: the `n`-th derivative of the cumulant generating function
    `cgf X μ = log ∘ mgf X μ` at `t = 0`.  Returns `0` outside the
    domain of definition of `cgf`. -/
noncomputable def cumulant (n : ℕ) (X : Ω → ℝ) (μ : Measure Ω) : ℝ :=
  iteratedDeriv n (cgf X μ) 0

@[simp]
lemma cumulant_zero_index : cumulant 0 X μ = cgf X μ 0 := by
  simp [cumulant, iteratedDeriv_zero]

/-- **`K_0 = 0`** for a probability measure: `cgf X μ 0 = log (mgf X μ 0) = log 1 = 0`. -/
theorem cumulant_zero [IsProbabilityMeasure μ] : cumulant 0 X μ = 0 := by
  simp [cumulant_zero_index, cgf]

/-- **`K_1 = μ[X]`** (first cumulant = mean) under integrability at 0. -/
theorem cumulant_one_eq_mean [IsProbabilityMeasure μ]
    (h : 0 ∈ interior (integrableExpSet X μ)) :
    cumulant 1 X μ = μ[X] := by
  rw [cumulant, iteratedDeriv_one, deriv_cgf_zero h]
  simp

/-- **`K_2 = Var[X; μ]`** (second cumulant = variance) under integrability at 0. -/
theorem cumulant_two_eq_variance [IsProbabilityMeasure μ]
    (h : 0 ∈ interior (integrableExpSet X μ)) :
    cumulant 2 X μ = Var[X; μ] := by
  rw [cumulant, iteratedDeriv_two_cgf h]
  have hmgf0 : mgf X μ 0 = 1 := mgf_zero
  have hμ_univ : μ.real Set.univ = 1 := by simp
  rw [hmgf0, deriv_cgf_zero h, hμ_univ]
  -- Goal: μ[X²·exp(0·X)] / 1 - (μ[X] / 1)² = Var[X; μ]
  have hexp_zero : (fun ω => X ω ^ 2 * Real.exp (0 * X ω)) = fun ω => X ω ^ 2 := by
    funext ω; rw [zero_mul, Real.exp_zero, mul_one]
  rw [hexp_zero, div_one, div_one]
  -- Goal: μ[X²] - (μ[X])² = Var[X; μ]
  have hμ_int : Integrable X μ :=
    (memLp_of_mem_interior_integrableExpSet h (p := 1)).integrable (by norm_num)
  have hX_sq_int : Integrable (fun ω => X ω ^ 2) μ := by
    have h_norm_pow : Integrable (fun ω => ‖X ω‖ ^ 2) μ :=
      (memLp_of_mem_interior_integrableExpSet h (p := 2)).integrable_norm_pow (by norm_num)
    have h_eq : (fun ω => ‖X ω‖ ^ 2) = (fun ω => X ω ^ 2) := by
      funext ω; rw [Real.norm_eq_abs, sq_abs]
    rwa [h_eq] at h_norm_pow
  rw [variance_eq_integral hμ_int.aemeasurable]
  have h_eq : ∀ ω : Ω, (X ω - μ[X]) ^ 2 = X ω ^ 2 - 2 * μ[X] * X ω + μ[X] ^ 2 := by
    intro ω; ring
  rw [show (fun ω : Ω => (X ω - μ[X]) ^ 2) =
      (fun ω => X ω ^ 2 - 2 * μ[X] * X ω + μ[X] ^ 2) from funext h_eq]
  have h1 : Integrable (fun ω => X ω ^ 2 - 2 * μ[X] * X ω) μ :=
    hX_sq_int.sub (hμ_int.const_mul (2 * μ[X]))
  rw [integral_add h1 (integrable_const _)]
  rw [integral_sub hX_sq_int (hμ_int.const_mul (2 * μ[X]))]
  rw [integral_const_mul, integral_const]
  rw [hμ_univ, one_smul]
  ring

/-! ## Skewness and kurtosis (cumulant ratios). -/

/-- **Cumulant skewness**: `Skew(X) := K_3(X) / K_2(X)^(3/2)`. -/
noncomputable def cumulantSkewness (X : Ω → ℝ) (μ : Measure Ω) : ℝ :=
  cumulant 3 X μ / cumulant 2 X μ ^ ((3 : ℝ) / 2)

/-- **Cumulant kurtosis**: `Kurt(X) := 3 + K_4(X) / K_2(X)^2`. -/
noncomputable def cumulantKurtosis (X : Ω → ℝ) (μ : Measure Ω) : ℝ :=
  3 + cumulant 4 X μ / cumulant 2 X μ ^ 2

/-! ## Cumulant of an iid sum.

For iid `X_i ~ Y` indexed by `Fin N`, the cgf of the sum equals
`N · cgf Y` on the integrability interior of `Y`:
    `cgf (Σ X_i) μ t = Σ_i cgf (X_i) μ t       [iIndepFun.cgf_sum]
                     = Σ_i cgf Y μ t             [IdentDistrib]
                     = N · cgf Y μ t`,
locally around `t = 0`.  Differentiating `n` times at `0` via
`iteratedDeriv_const_mul_field` and using `Filter.EventuallyEq.iteratedDeriv_eq`
yields `K_n(Σ X_i) = N · K_n(Y)`.

Discharging the integrability bookkeeping under `IdentDistrib` plus the
`iIndepFun` pre-requisite for `cgf_sum` is straightforward but
multi-step.  Axiomatised here as
`cgf_iid_sum_eq_const_mul_eventuallyEq`; the cumulant identity follows. -/

/-- **cgf identity on a nbhd of 0 for an iid family.**  Captures
    `cgf (Σ X_i) μ =ᶠ[𝓝 0] (N : ℝ) · cgf Y μ`.  Proved via
    `IdentDistrib.comp` transport of `exp(t · ·)` integrability,
    `iIndepFun.cgf_sum₀`, and `mgf_congr_of_identDistrib`. -/
private lemma cgf_iid_sum_eq_const_mul_eventuallyEq {N : ℕ} {Y : Ω → ℝ} {X : Fin N → Ω → ℝ}
    [IsProbabilityMeasure μ]
    (h_indep : iIndepFun X μ)
    (h_id : ∀ i, IdentDistrib (X i) Y μ μ)
    (h_int : 0 ∈ interior (integrableExpSet Y μ)) :
    cgf (∑ i, X i) μ =ᶠ[𝓝 0] fun t => (N : ℝ) * cgf Y μ t := by
  filter_upwards [isOpen_interior.mem_nhds h_int] with t ht
  -- Transport integrability of `exp(t · ·)` from `Y` to each `X i`.
  have hY_int : Integrable (fun ω => Real.exp (t * Y ω)) μ :=
    interior_subset (s := integrableExpSet Y μ) ht
  have h_int_t : ∀ i ∈ (Finset.univ : Finset (Fin N)),
      Integrable (fun ω => Real.exp (t * X i ω)) μ := by
    intro i _
    have h_comp : IdentDistrib ((fun y => Real.exp (t * y)) ∘ X i)
        ((fun y => Real.exp (t * y)) ∘ Y) μ μ :=
      (h_id i).comp (measurable_const_mul t).exp
    exact h_comp.integrable_iff.mpr hY_int
  -- cgf of sum = sum of cgfs (under `iIndepFun.cgf_sum₀`).
  have h_meas : ∀ i, AEMeasurable (X i) μ := fun i => (h_id i).aemeasurable_fst
  have h_cgf_sum := h_indep.cgf_sum₀ h_meas h_int_t
  -- Each cgf (X i) μ t = cgf Y μ t by IdentDistrib.
  have h_cgf_eq : ∀ i, cgf (X i) μ t = cgf Y μ t := by
    intro i
    simp [cgf, mgf_congr_of_identDistrib (X i) Y (h_id i) t]
  rw [h_cgf_sum]
  simp_rw [h_cgf_eq]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **Cumulant of an iid sum** (paper Eq. 1 etc.).  For `X_i ~ Y` iid,
        `K_n(Σ_{i<N} X_i) = N · K_n(Y)`. -/
theorem cumulant_iid_sum {N : ℕ} {Y : Ω → ℝ} {X : Fin N → Ω → ℝ}
    [IsProbabilityMeasure μ]
    (h_indep : iIndepFun X μ)
    (h_id : ∀ i, IdentDistrib (X i) Y μ μ)
    (h_int : 0 ∈ interior (integrableExpSet Y μ))
    (n : ℕ) :
    cumulant n (∑ i, X i) μ = (N : ℝ) * cumulant n Y μ := by
  have h_ev := cgf_iid_sum_eq_const_mul_eventuallyEq h_indep h_id h_int
  rw [cumulant, h_ev.iteratedDeriv_eq n]
  -- Now: iteratedDeriv n (fun t => N · cgf Y μ t) 0 = N · iteratedDeriv n (cgf Y μ) 0
  rw [iteratedDeriv_const_mul_field (N : ℝ) (cgf Y μ)]
  rfl

/-! ## Moment-cumulant linkage.

The paper's skewness and kurtosis formulas in terms of cumulants
(`Skew = K_3 / K_2^(3/2)`, `Kurt = 3 + K_4 / K_2²`) match the standard
ratios in terms of central moments (`Skew = μ_3 / σ³`, `Kurt = μ_4 / σ⁴`)
via the identities
    `μ_3 = K_3`,
    `μ_4 = K_4 + 3 K_2²`,
where `μ_k := centralMoment X k μ` is the `k`-th central moment.

Discharging these requires computing `iteratedDeriv 3` and
`iteratedDeriv 4` of `log ∘ mgf X` at `0` via Faà di Bruno / Bell
polynomials.  Mathlib v4.29.1 has only `iteratedDeriv_two_cgf`; orders
`3, 4` would each be ~150 lines of derivative manipulation.

Axiomatised here pending the Faà di Bruno expansion (todo3.md
C.4.discharge.moments). -/

/-- Integrability of `X^k` from interior of `integrableExpSet` (requires
    `IsFiniteMeasure` for `MemLp.integrable_norm_pow`). -/
private lemma integrable_pow_of_mem_interior_integrableExpSet
    [IsFiniteMeasure μ]
    (h : 0 ∈ interior (integrableExpSet X μ)) (k : ℕ) (hk : k ≠ 0) :
    Integrable (fun ω => X ω ^ k) μ := by
  have hX_int : Integrable X μ :=
    (memLp_of_mem_interior_integrableExpSet h (p := 1)).integrable (by norm_num)
  have h_pow : Integrable (fun ω => ‖X ω‖ ^ k) μ :=
    (memLp_of_mem_interior_integrableExpSet h (p := k)).integrable_norm_pow hk
  have h_eq : (fun ω => ‖X ω‖ ^ k) = (fun ω => ‖X ω ^ k‖) := by
    funext ω; rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_pow]
  rw [h_eq] at h_pow
  exact (integrable_norm_iff (hX_int.aestronglyMeasurable.pow k)).mp h_pow

/-- **Third central moment expansion**: `μ_3 = E[X³] − 3·E[X²]·E[X] + 2·E[X]³`. -/
private lemma centralMoment_three_expand [IsProbabilityMeasure μ]
    (h : 0 ∈ interior (integrableExpSet X μ)) :
    centralMoment X 3 μ =
      μ[fun ω => X ω ^ 3] - 3 * μ[fun ω => X ω ^ 2] * μ[X] + 2 * μ[X] ^ 3 := by
  have hμ_univ : μ.real Set.univ = 1 := by simp
  have hX_int : Integrable X μ :=
    (memLp_of_mem_interior_integrableExpSet h (p := 1)).integrable (by norm_num)
  have hX2_int := integrable_pow_of_mem_interior_integrableExpSet h 2 (by norm_num)
  have hX3_int := integrable_pow_of_mem_interior_integrableExpSet h 3 (by norm_num)
  unfold centralMoment
  -- Define the integrand explicitly to avoid pattern-matching pain.
  set f : Ω → ℝ := fun ω => X ω ^ 3 with hf_def
  set g2 : Ω → ℝ := fun ω => -(3 * μ[X]) * X ω ^ 2 with hg2_def
  set g1 : Ω → ℝ := fun ω => (3 * μ[X] ^ 2) * X ω with hg1_def
  set g0 : Ω → ℝ := fun _ => -(μ[X] ^ 3) with hg0_def
  -- Pointwise: (X - μ[X])^3 = f + g2 + g1 + g0.
  have h_eq_fun : ((X - fun _ : Ω => μ[X]) ^ 3 : Ω → ℝ) =
      fun ω => f ω + g2 ω + g1 ω + g0 ω := by
    funext ω
    simp only [Pi.sub_apply, Pi.pow_apply, hf_def, hg2_def, hg1_def, hg0_def]
    ring
  rw [h_eq_fun]
  have hf_int : Integrable f μ := hX3_int
  have hg2_int : Integrable g2 μ := hX2_int.const_mul _
  have hg1_int : Integrable g1 μ := hX_int.const_mul _
  have hg0_int : Integrable g0 μ := integrable_const _
  -- Compute the integral by splitting via Pi-add chain.
  have h_int_eq :
      ∫ ω, f ω + g2 ω + g1 ω + g0 ω ∂μ =
        ∫ ω, f ω ∂μ + ∫ ω, g2 ω ∂μ + ∫ ω, g1 ω ∂μ + ∫ ω, g0 ω ∂μ := by
    have h1 : Integrable (fun ω => f ω + g2 ω) μ := hf_int.add hg2_int
    have h12 : Integrable (fun ω => f ω + g2 ω + g1 ω) μ := h1.add hg1_int
    rw [show (fun ω => f ω + g2 ω + g1 ω + g0 ω) =
        (fun ω => (fun ω' => f ω' + g2 ω' + g1 ω') ω + g0 ω) from rfl]
    rw [integral_add h12 hg0_int]
    rw [show (fun ω' => f ω' + g2 ω' + g1 ω') =
        (fun ω => (fun ω' => f ω' + g2 ω') ω + g1 ω) from rfl]
    rw [integral_add h1 hg1_int]
    rw [show (fun ω' => f ω' + g2 ω') =
        (fun ω => f ω + g2 ω) from rfl]
    rw [integral_add hf_int hg2_int]
  rw [h_int_eq]
  simp only [hg2_def, hg1_def, hg0_def, hf_def]
  rw [integral_const_mul, integral_const_mul, integral_const]
  rw [hμ_univ, one_smul]
  ring

/-- **Third cumulant expansion**: `K_3 = E[X³] − 3·E[X²]·E[X] + 2·E[X]³`.

    Direct computation of `iteratedDeriv 3 (cgf X μ) 0` via:
    1. `iteratedDeriv 3 cgf = deriv (iteratedDeriv 2 cgf)`.
    2. `iteratedDeriv 2 cgf v = μ[X²·exp(v·X)] / mgf v - (deriv cgf v)²` on nbhd of 0.
    3. Differentiation of `A/B - C²` using `HasDerivAt.div`, `HasDerivAt.pow`,
       and `hasDerivAt_integral_pow_mul_exp_real`. -/
private lemma cumulant_three_expand [IsProbabilityMeasure μ]
    (h : 0 ∈ interior (integrableExpSet X μ)) :
    cumulant 3 X μ = μ[fun ω => X ω ^ 3]
      - 3 * μ[fun ω => X ω ^ 2] * μ[X] + 2 * μ[X] ^ 3 := by
  -- Step 1: iteratedDeriv 3 = deriv (iteratedDeriv 2).
  rw [cumulant, show (3 : ℕ) = 2 + 1 from rfl, iteratedDeriv_succ]
  -- Step 2: on the integrability interior, iteratedDeriv 2 cgf matches Mathlib's formula.
  have h_mem : ∀ᶠ y in 𝓝 (0 : ℝ), y ∈ interior (integrableExpSet X μ) :=
    isOpen_interior.eventually_mem h
  have h_eq : iteratedDeriv 2 (cgf X μ) =ᶠ[𝓝 0]
      fun v => μ[fun ω => X ω ^ 2 * Real.exp (v * X ω)] / mgf X μ v -
                 deriv (cgf X μ) v ^ 2 := by
    filter_upwards [h_mem] with v hv using iteratedDeriv_two_cgf hv
  rw [h_eq.deriv_eq]
  -- Step 3: HasDerivAt for the constituent functions.
  -- A(v) := μ[X² · exp(v · X)], A'(0) = μ[X³], A(0) = μ[X²].
  have hA_d : HasDerivAt (fun v => μ[fun ω => X ω ^ 2 * Real.exp (v * X ω)])
      μ[fun ω => X ω ^ 3] 0 := by
    have := hasDerivAt_integral_pow_mul_exp_real h 2
    convert this using 1
    refine integral_congr_ae (.of_forall fun ω => ?_)
    simp
  have hA_val : (fun v => μ[fun ω => X ω ^ 2 * Real.exp (v * X ω)]) 0
      = μ[fun ω => X ω ^ 2] := by
    refine integral_congr_ae (.of_forall fun ω => ?_)
    simp
  -- B(v) := mgf v, B'(0) = μ[X], B(0) = 1.
  have hB_d : HasDerivAt (mgf X μ) μ[X] 0 := by
    have := hasDerivAt_mgf h
    convert this using 1
    refine integral_congr_ae (.of_forall fun ω => ?_)
    simp
  have hB_val : mgf X μ 0 = 1 := mgf_zero
  have hB_ne : mgf X μ 0 ≠ 0 := by rw [hB_val]; exact one_ne_zero
  -- C(v) := deriv (cgf X μ) v. C(0) = μ[X], C'(0) = iteratedDeriv 2 cgf 0 = K_2.
  have hC_an : AnalyticAt ℝ (cgf X μ) 0 := analyticAt_cgf h
  have hC_an_d : AnalyticAt ℝ (deriv (cgf X μ)) 0 := hC_an.deriv
  have hC_diff : DifferentiableAt ℝ (deriv (cgf X μ)) 0 := hC_an_d.differentiableAt
  have hC_d : HasDerivAt (deriv (cgf X μ)) (deriv (deriv (cgf X μ)) 0) 0 :=
    hC_diff.hasDerivAt
  -- Express deriv (deriv cgf) 0 = iteratedDeriv 2 cgf 0 = K_2.
  have h_dd_eq : deriv (deriv (cgf X μ)) 0 = iteratedDeriv 2 (cgf X μ) 0 := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  have hC_val : deriv (cgf X μ) 0 = μ[X] := by
    rw [deriv_cgf_zero h]; simp
  -- K_2 value via cumulant_two_eq_variance's expansion (here directly from iteratedDeriv_two_cgf).
  have hK2_form : iteratedDeriv 2 (cgf X μ) 0
      = μ[fun ω => X ω ^ 2] - μ[X] ^ 2 := by
    rw [iteratedDeriv_two_cgf h, hB_val, deriv_cgf_zero h]
    have : (fun ω => X ω ^ 2 * Real.exp (0 * X ω)) = (fun ω => X ω ^ 2) := by
      funext ω; rw [zero_mul, Real.exp_zero, mul_one]
    rw [this]
    rw [show μ.real Set.univ = 1 from by simp]
    ring
  -- Apply HasDerivAt to compute the derivative of A/B - C^2 at 0.
  -- A/B has derivative (A' B - A B') / B² at 0.
  have hAB_d : HasDerivAt
      (fun v => μ[fun ω => X ω ^ 2 * Real.exp (v * X ω)] / mgf X μ v)
      ((μ[fun ω => X ω ^ 3] * mgf X μ 0 - μ[fun ω => X ω ^ 2] * μ[X]) / mgf X μ 0 ^ 2) 0 := by
    have h := hA_d.div hB_d hB_ne
    simp only [zero_mul, Real.exp_zero, mul_one] at h
    exact h
  -- C² has derivative 2 · C · C' at 0.
  have hCsq_d : HasDerivAt (fun v => deriv (cgf X μ) v ^ 2)
      (2 * deriv (cgf X μ) 0 ^ 1 * deriv (deriv (cgf X μ)) 0) 0 := by
    have := hC_d.pow 2
    convert this using 1
  -- A/B - C² has derivative (A/B)' - (C²)' at 0.
  have hF_d : HasDerivAt
      (fun v => μ[fun ω => X ω ^ 2 * Real.exp (v * X ω)] / mgf X μ v -
                  deriv (cgf X μ) v ^ 2)
      ((μ[fun ω => X ω ^ 3] * mgf X μ 0 - μ[fun ω => X ω ^ 2] * μ[X]) / mgf X μ 0 ^ 2 -
        (2 * deriv (cgf X μ) 0 ^ 1 * deriv (deriv (cgf X μ)) 0)) 0 :=
    hAB_d.sub hCsq_d
  rw [hF_d.deriv]
  -- Plug in known values and simplify.
  rw [hB_val, hC_val, h_dd_eq, hK2_form]
  ring

/-- **Third central moment equals third cumulant** (paper Eq. 1 etc.).
    `μ_3 = K_3`.  Discharged via direct derivative computation of
    `iteratedDeriv 3 (cgf X μ) 0` and polynomial expansion of
    `centralMoment X 3 μ`. -/
theorem cumulant_three_eq_centralMoment_three
    [IsProbabilityMeasure μ] (h : 0 ∈ interior (integrableExpSet X μ)) :
    cumulant 3 X μ = centralMoment X 3 μ := by
  rw [cumulant_three_expand h, centralMoment_three_expand h]

/-- **Fourth central moment expansion**:
        `μ_4 = E[X⁴] − 4·E[X³]·E[X] + 6·E[X²]·E[X]² − 3·E[X]⁴`. -/
private lemma centralMoment_four_expand [IsProbabilityMeasure μ]
    (h : 0 ∈ interior (integrableExpSet X μ)) :
    centralMoment X 4 μ =
      μ[fun ω => X ω ^ 4] - 4 * μ[fun ω => X ω ^ 3] * μ[X]
        + 6 * μ[fun ω => X ω ^ 2] * μ[X] ^ 2 - 3 * μ[X] ^ 4 := by
  have hμ_univ : μ.real Set.univ = 1 := by simp
  have hX_int : Integrable X μ :=
    (memLp_of_mem_interior_integrableExpSet h (p := 1)).integrable (by norm_num)
  have hX2_int := integrable_pow_of_mem_interior_integrableExpSet h 2 (by norm_num)
  have hX3_int := integrable_pow_of_mem_interior_integrableExpSet h 3 (by norm_num)
  have hX4_int := integrable_pow_of_mem_interior_integrableExpSet h 4 (by norm_num)
  unfold centralMoment
  set f : Ω → ℝ := fun ω => X ω ^ 4 with hf_def
  set g3 : Ω → ℝ := fun ω => -(4 * μ[X]) * X ω ^ 3 with hg3_def
  set g2 : Ω → ℝ := fun ω => (6 * μ[X] ^ 2) * X ω ^ 2 with hg2_def
  set g1 : Ω → ℝ := fun ω => -(4 * μ[X] ^ 3) * X ω with hg1_def
  set g0 : Ω → ℝ := fun _ => μ[X] ^ 4 with hg0_def
  have h_eq_fun : ((X - fun _ : Ω => μ[X]) ^ 4 : Ω → ℝ) =
      fun ω => f ω + g3 ω + g2 ω + g1 ω + g0 ω := by
    funext ω
    simp only [Pi.sub_apply, Pi.pow_apply, hf_def, hg3_def, hg2_def, hg1_def, hg0_def]
    ring
  rw [h_eq_fun]
  have hf_int : Integrable f μ := hX4_int
  have hg3_int : Integrable g3 μ := hX3_int.const_mul _
  have hg2_int : Integrable g2 μ := hX2_int.const_mul _
  have hg1_int : Integrable g1 μ := hX_int.const_mul _
  have hg0_int : Integrable g0 μ := integrable_const _
  have h_int_eq :
      ∫ ω, f ω + g3 ω + g2 ω + g1 ω + g0 ω ∂μ =
        ∫ ω, f ω ∂μ + ∫ ω, g3 ω ∂μ + ∫ ω, g2 ω ∂μ + ∫ ω, g1 ω ∂μ + ∫ ω, g0 ω ∂μ := by
    have h1 : Integrable (fun ω => f ω + g3 ω) μ := hf_int.add hg3_int
    have h12 : Integrable (fun ω => f ω + g3 ω + g2 ω) μ := h1.add hg2_int
    have h123 : Integrable (fun ω => f ω + g3 ω + g2 ω + g1 ω) μ := h12.add hg1_int
    rw [show (fun ω => f ω + g3 ω + g2 ω + g1 ω + g0 ω) =
        (fun ω => (fun ω' => f ω' + g3 ω' + g2 ω' + g1 ω') ω + g0 ω) from rfl]
    rw [integral_add h123 hg0_int]
    rw [show (fun ω' => f ω' + g3 ω' + g2 ω' + g1 ω') =
        (fun ω => (fun ω' => f ω' + g3 ω' + g2 ω') ω + g1 ω) from rfl]
    rw [integral_add h12 hg1_int]
    rw [show (fun ω' => f ω' + g3 ω' + g2 ω') =
        (fun ω => (fun ω' => f ω' + g3 ω') ω + g2 ω) from rfl]
    rw [integral_add h1 hg2_int]
    rw [show (fun ω' => f ω' + g3 ω') = (fun ω => f ω + g3 ω) from rfl]
    rw [integral_add hf_int hg3_int]
  rw [h_int_eq]
  simp only [hg3_def, hg2_def, hg1_def, hg0_def, hf_def]
  rw [integral_const_mul, integral_const_mul, integral_const_mul, integral_const]
  rw [hμ_univ, one_smul]
  ring

/-- **Explicit form for `iteratedDeriv 3 (cgf X μ)`** at any point `v` in
    the interior of `integrableExpSet X μ`.  Direct extension of
    Mathlib's `iteratedDeriv_two_cgf` formula via the chain rule. -/
private lemma iteratedDeriv_three_cgf [IsProbabilityMeasure μ] {v : ℝ}
    (h : v ∈ interior (integrableExpSet X μ)) :
    iteratedDeriv 3 (cgf X μ) v =
      (μ[fun ω => X ω ^ 3 * Real.exp (v * X ω)] * mgf X μ v -
        μ[fun ω => X ω ^ 2 * Real.exp (v * X ω)] *
          μ[fun ω => X ω * Real.exp (v * X ω)]) / mgf X μ v ^ 2 -
      2 * deriv (cgf X μ) v * iteratedDeriv 2 (cgf X μ) v := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, iteratedDeriv_succ]
  have h_mem : ∀ᶠ y in 𝓝 v, y ∈ interior (integrableExpSet X μ) :=
    isOpen_interior.eventually_mem h
  have h_eq : iteratedDeriv 2 (cgf X μ) =ᶠ[𝓝 v]
      fun u => μ[fun ω => X ω ^ 2 * Real.exp (u * X ω)] / mgf X μ u -
                 deriv (cgf X μ) u ^ 2 := by
    filter_upwards [h_mem] with u hu using iteratedDeriv_two_cgf hu
  rw [h_eq.deriv_eq]
  -- HasDerivAt for the constituent functions at v.
  have hA_d : HasDerivAt (fun u => μ[fun ω => X ω ^ 2 * Real.exp (u * X ω)])
      μ[fun ω => X ω ^ 3 * Real.exp (v * X ω)] v :=
    hasDerivAt_integral_pow_mul_exp_real h 2
  have hB_d : HasDerivAt (mgf X μ) μ[fun ω => X ω * Real.exp (v * X ω)] v :=
    hasDerivAt_mgf h
  have hv_int : v ∈ integrableExpSet X μ := interior_subset h
  have hB_pos : 0 < mgf X μ v := mgf_pos hv_int
  have hB_ne : mgf X μ v ≠ 0 := hB_pos.ne'
  -- C(u) := deriv (cgf X μ) u at u near v. Differentiable from AnalyticAt.
  have hC_an_d : AnalyticAt ℝ (deriv (cgf X μ)) v := (analyticAt_cgf h).deriv
  have hC_d : HasDerivAt (deriv (cgf X μ)) (deriv (deriv (cgf X μ)) v) v :=
    hC_an_d.differentiableAt.hasDerivAt
  have h_dd_eq : deriv (deriv (cgf X μ)) v = iteratedDeriv 2 (cgf X μ) v := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  -- A/B has derivative (A' B - A B') / B² at v.
  have hAB_d : HasDerivAt
      (fun u => μ[fun ω => X ω ^ 2 * Real.exp (u * X ω)] / mgf X μ u)
      ((μ[fun ω => X ω ^ 3 * Real.exp (v * X ω)] * mgf X μ v -
        μ[fun ω => X ω ^ 2 * Real.exp (v * X ω)] *
          μ[fun ω => X ω * Real.exp (v * X ω)]) / mgf X μ v ^ 2) v :=
    hA_d.div hB_d hB_ne
  have hCsq_d : HasDerivAt (fun u => deriv (cgf X μ) u ^ 2)
      (2 * deriv (cgf X μ) v ^ 1 * deriv (deriv (cgf X μ)) v) v := by
    have := hC_d.pow 2
    convert this using 1
  have hF_d : HasDerivAt
      (fun u => μ[fun ω => X ω ^ 2 * Real.exp (u * X ω)] / mgf X μ u -
                  deriv (cgf X μ) u ^ 2)
      ((μ[fun ω => X ω ^ 3 * Real.exp (v * X ω)] * mgf X μ v -
        μ[fun ω => X ω ^ 2 * Real.exp (v * X ω)] *
          μ[fun ω => X ω * Real.exp (v * X ω)]) / mgf X μ v ^ 2 -
        (2 * deriv (cgf X μ) v ^ 1 * deriv (deriv (cgf X μ)) v)) v :=
    hAB_d.sub hCsq_d
  rw [hF_d.deriv]
  rw [h_dd_eq]
  ring

/-- **Fourth cumulant expansion**:
        `K_4 = E[X⁴] − 4·E[X³]·E[X] − 3·E[X²]² + 12·E[X²]·E[X]² − 6·E[X]⁴`.

    Direct computation of `iteratedDeriv 4 (cgf X μ) 0` via:
    1. `iteratedDeriv 4 cgf = deriv (iteratedDeriv 3 cgf)`.
    2. `iteratedDeriv 3 cgf v = (A B − C D)/B² − 2 E G` on a nbhd of 0
       (from `iteratedDeriv_three_cgf` above), with
       `A = μ[X³·exp(v·)], B = mgf, C = μ[X²·exp(v·)], D = μ[X·exp(v·)],
        E = (cgf)', G = (cgf)''`.
    3. Quotient + product rule.  At `v = 0`: `B = 1`, `B' = μ[X]`,
       `E = μ[X]`, `E' = G = K_2`, `G' = K_3`. -/
private lemma cumulant_four_expand [IsProbabilityMeasure μ]
    (h : 0 ∈ interior (integrableExpSet X μ)) :
    cumulant 4 X μ =
      μ[fun ω => X ω ^ 4]
      - 4 * μ[fun ω => X ω ^ 3] * μ[X]
      - 3 * μ[fun ω => X ω ^ 2] ^ 2
      + 12 * μ[fun ω => X ω ^ 2] * μ[X] ^ 2
      - 6 * μ[X] ^ 4 := by
  -- Step 1: iteratedDeriv 4 = deriv (iteratedDeriv 3).
  -- (Done in a local `have` to avoid `rw` rewriting `^4` exponents in the RHS.)
  have h_unfold : iteratedDeriv 4 (cgf X μ) 0
      = deriv (iteratedDeriv 3 (cgf X μ)) 0 := by
    rw [show (4 : ℕ) = 3 + 1 from rfl, iteratedDeriv_succ]
  rw [cumulant, h_unfold]
  -- Step 2: on a neighbourhood of 0, iteratedDeriv 3 cgf matches the closed form.
  have h_mem : ∀ᶠ y in 𝓝 (0 : ℝ), y ∈ interior (integrableExpSet X μ) :=
    isOpen_interior.eventually_mem h
  have h_eq : iteratedDeriv 3 (cgf X μ) =ᶠ[𝓝 0]
      fun v => (μ[fun ω => X ω ^ 3 * Real.exp (v * X ω)] * mgf X μ v -
                 μ[fun ω => X ω ^ 2 * Real.exp (v * X ω)] *
                   μ[fun ω => X ω * Real.exp (v * X ω)]) / mgf X μ v ^ 2 -
                 2 * deriv (cgf X μ) v * iteratedDeriv 2 (cgf X μ) v := by
    filter_upwards [h_mem] with v hv using iteratedDeriv_three_cgf hv
  rw [h_eq.deriv_eq]
  -- Step 3: HasDerivAt for each component at v = 0.
  -- A(v) = μ[X³ · exp(v·X)]; A(0) = μ[X³], A'(0) = μ[X⁴].
  have hA_d : HasDerivAt (fun v => μ[fun ω => X ω ^ 3 * Real.exp (v * X ω)])
      μ[fun ω => X ω ^ 4] 0 := by
    have := hasDerivAt_integral_pow_mul_exp_real h 3
    convert this using 1
    refine integral_congr_ae (.of_forall fun ω => ?_)
    simp
  have hA0 : (fun v => μ[fun ω => X ω ^ 3 * Real.exp (v * X ω)]) 0
      = μ[fun ω => X ω ^ 3] := by
    refine integral_congr_ae (.of_forall fun ω => ?_)
    simp
  -- B(v) = mgf X μ v; B(0) = 1, B'(0) = μ[X].
  have hB_d : HasDerivAt (mgf X μ) μ[X] 0 := by
    have := hasDerivAt_mgf h
    convert this using 1
    refine integral_congr_ae (.of_forall fun ω => ?_)
    simp
  have hB0 : mgf X μ 0 = 1 := mgf_zero
  have hB0_ne : mgf X μ 0 ≠ 0 := by rw [hB0]; exact one_ne_zero
  have hBsq0_ne : mgf X μ 0 ^ 2 ≠ 0 := pow_ne_zero _ hB0_ne
  -- C(v) = μ[X² · exp(v·X)]; C(0) = μ[X²], C'(0) = μ[X³].
  have hC_d : HasDerivAt (fun v => μ[fun ω => X ω ^ 2 * Real.exp (v * X ω)])
      μ[fun ω => X ω ^ 3] 0 := by
    have := hasDerivAt_integral_pow_mul_exp_real h 2
    convert this using 1
    refine integral_congr_ae (.of_forall fun ω => ?_)
    simp
  have hC0 : (fun v => μ[fun ω => X ω ^ 2 * Real.exp (v * X ω)]) 0
      = μ[fun ω => X ω ^ 2] := by
    refine integral_congr_ae (.of_forall fun ω => ?_)
    simp
  -- D(v) = μ[X · exp(v·X)]; D(0) = μ[X], D'(0) = μ[X²].
  have hD_d : HasDerivAt (fun v => μ[fun ω => X ω * Real.exp (v * X ω)])
      μ[fun ω => X ω ^ 2] 0 := by
    have h_aux := hasDerivAt_integral_pow_mul_exp_real h 1
    simp only [pow_one, zero_mul, Real.exp_zero, mul_one,
               show (1 + 1 : ℕ) = 2 from rfl] at h_aux
    exact h_aux
  have hD0 : (fun v => μ[fun ω => X ω * Real.exp (v * X ω)]) 0
      = μ[X] := by
    refine integral_congr_ae (.of_forall fun ω => ?_)
    simp
  -- E(v) = deriv (cgf X μ) v; E(0) = μ[X], E'(0) = iteratedDeriv 2 cgf 0.
  have hE_an : AnalyticAt ℝ (deriv (cgf X μ)) 0 := (analyticAt_cgf h).deriv
  have hE_d : HasDerivAt (deriv (cgf X μ)) (deriv (deriv (cgf X μ)) 0) 0 :=
    hE_an.differentiableAt.hasDerivAt
  have hE0 : deriv (cgf X μ) 0 = μ[X] := by rw [deriv_cgf_zero h]; simp
  have h_dd_eq : deriv (deriv (cgf X μ)) 0 = iteratedDeriv 2 (cgf X μ) 0 := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  -- G(v) = iteratedDeriv 2 cgf v; G(0) = K_2, G'(0) = iteratedDeriv 3 cgf 0 = K_3.
  have hG_an : AnalyticAt ℝ (iteratedDeriv 2 (cgf X μ)) 0 := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
    exact (analyticAt_cgf h).deriv.deriv
  have hG_d : HasDerivAt (iteratedDeriv 2 (cgf X μ))
      (deriv (iteratedDeriv 2 (cgf X μ)) 0) 0 :=
    hG_an.differentiableAt.hasDerivAt
  -- K_2 closed form.
  have hK2 : iteratedDeriv 2 (cgf X μ) 0 = μ[fun ω => X ω ^ 2] - μ[X] ^ 2 := by
    rw [iteratedDeriv_two_cgf h, hB0, deriv_cgf_zero h]
    have hfun : (fun ω => X ω ^ 2 * Real.exp (0 * X ω)) = (fun ω => X ω ^ 2) := by
      funext ω; rw [zero_mul, Real.exp_zero, mul_one]
    rw [hfun, show μ.real Set.univ = 1 from by simp]; ring
  -- K_3 closed form (via existing `cumulant_three_expand`).
  have hK3 : deriv (iteratedDeriv 2 (cgf X μ)) 0
      = μ[fun ω => X ω ^ 3] - 3 * μ[fun ω => X ω ^ 2] * μ[X] + 2 * μ[X] ^ 3 := by
    have h3 := cumulant_three_expand h
    rw [cumulant, show (3 : ℕ) = 2 + 1 from rfl, iteratedDeriv_succ] at h3
    exact h3
  -- Step 4: build HasDerivAt for `(A·B - C·D) / B^2` and `2·E·G`, then subtract.
  -- A·B: derivative at 0 is A'(0)·B(0) + A(0)·B'(0) = μ[X⁴]·1 + μ[X³]·μ[X].
  have hAB_d : HasDerivAt
      (fun v => μ[fun ω => X ω ^ 3 * Real.exp (v * X ω)] * mgf X μ v)
      (μ[fun ω => X ω ^ 4] * mgf X μ 0 +
         μ[fun ω => X ω ^ 3] * μ[X]) 0 := by
    have h := hA_d.mul hB_d
    simp only [zero_mul, Real.exp_zero, mul_one] at h
    convert h using 1
  -- C·D: derivative at 0 is μ[X³]·μ[X] + μ[X²]·μ[X²] = μ[X³]·μ[X] + μ[X²]².
  have hCD_d : HasDerivAt
      (fun v => μ[fun ω => X ω ^ 2 * Real.exp (v * X ω)] *
                  μ[fun ω => X ω * Real.exp (v * X ω)])
      (μ[fun ω => X ω ^ 3] * μ[X] + μ[fun ω => X ω ^ 2] ^ 2) 0 := by
    have h := hC_d.mul hD_d
    simp only [zero_mul, Real.exp_zero, mul_one] at h
    convert h using 2; ring
  -- N := A·B - C·D; N(0) = μ[X³]·1 - μ[X²]·μ[X], N'(0) = μ[X⁴] - μ[X²]².
  have hN_d : HasDerivAt
      (fun v => μ[fun ω => X ω ^ 3 * Real.exp (v * X ω)] * mgf X μ v -
                  μ[fun ω => X ω ^ 2 * Real.exp (v * X ω)] *
                    μ[fun ω => X ω * Real.exp (v * X ω)])
      (μ[fun ω => X ω ^ 4] * mgf X μ 0 + μ[fun ω => X ω ^ 3] * μ[X] -
         (μ[fun ω => X ω ^ 3] * μ[X] + μ[fun ω => X ω ^ 2] ^ 2)) 0 :=
    hAB_d.sub hCD_d
  -- M := B^2; M(0) = 1, M'(0) = 2·B(0)·B'(0) = 2·μ[X].
  have hBsq_d : HasDerivAt (fun v => mgf X μ v ^ 2)
      (2 * mgf X μ 0 ^ 1 * μ[X]) 0 := by
    have := hB_d.pow 2
    convert this using 1
  -- N/M at 0.  (Quotient rule.)
  have hNM_d : HasDerivAt
      (fun v => (μ[fun ω => X ω ^ 3 * Real.exp (v * X ω)] * mgf X μ v -
                   μ[fun ω => X ω ^ 2 * Real.exp (v * X ω)] *
                     μ[fun ω => X ω * Real.exp (v * X ω)]) / mgf X μ v ^ 2)
      (((μ[fun ω => X ω ^ 4] * mgf X μ 0 + μ[fun ω => X ω ^ 3] * μ[X] -
            (μ[fun ω => X ω ^ 3] * μ[X] + μ[fun ω => X ω ^ 2] ^ 2)) * mgf X μ 0 ^ 2 -
         (μ[fun ω => X ω ^ 3] * mgf X μ 0 -
            μ[fun ω => X ω ^ 2] * μ[X]) *
              (2 * mgf X μ 0 ^ 1 * μ[X])) / (mgf X μ 0 ^ 2) ^ 2) 0 := by
    have h := hN_d.div hBsq_d hBsq0_ne
    -- `simp` reduces `exp(0 · X) = 1` and `X · 1 = X` inside the integrand
    -- to bring the auto-computed `N(0) = A(0)·B(0) − C(0)·D(0)` value into
    -- nice form `μ[X³] · mgf X μ 0 − μ[X²] · μ[X]`.
    simp only [zero_mul, Real.exp_zero, mul_one] at h
    convert h using 2
  -- E·G: derivative at 0 is E'(0)·G(0) + E(0)·G'(0) = K_2² + μ[X]·K_3.
  have hEG_d : HasDerivAt (fun v => deriv (cgf X μ) v * iteratedDeriv 2 (cgf X μ) v)
      (deriv (deriv (cgf X μ)) 0 * iteratedDeriv 2 (cgf X μ) 0 +
         deriv (cgf X μ) 0 * deriv (iteratedDeriv 2 (cgf X μ)) 0) 0 :=
    hE_d.mul hG_d
  -- 2 · E · G: scale by 2.
  have h2EG_d : HasDerivAt (fun v => 2 * (deriv (cgf X μ) v * iteratedDeriv 2 (cgf X μ) v))
      (2 * (deriv (deriv (cgf X μ)) 0 * iteratedDeriv 2 (cgf X μ) 0 +
              deriv (cgf X μ) 0 * deriv (iteratedDeriv 2 (cgf X μ)) 0)) 0 :=
    hEG_d.const_mul 2
  -- Reshape `2 * deriv cgf v * iteratedDeriv 2 cgf v` to match.
  have h2EG_d' : HasDerivAt (fun v => 2 * deriv (cgf X μ) v * iteratedDeriv 2 (cgf X μ) v)
      (2 * (deriv (deriv (cgf X μ)) 0 * iteratedDeriv 2 (cgf X μ) 0 +
              deriv (cgf X μ) 0 * deriv (iteratedDeriv 2 (cgf X μ)) 0)) 0 := by
    have h_eq_fun :
        (fun v => 2 * deriv (cgf X μ) v * iteratedDeriv 2 (cgf X μ) v) =
        (fun v => 2 * (deriv (cgf X μ) v * iteratedDeriv 2 (cgf X μ) v)) := by
      funext v; ring
    rw [h_eq_fun]; exact h2EG_d
  -- Final: F = (N/M) - 2 E G.  Explicit pointwise function shape so the
  -- subsequent `rw [hF_d.deriv]` finds the goal's `deriv (fun v => …)` form.
  have hF_d : HasDerivAt
      (fun v => (μ[fun ω => X ω ^ 3 * Real.exp (v * X ω)] * mgf X μ v -
                   μ[fun ω => X ω ^ 2 * Real.exp (v * X ω)] *
                     μ[fun ω => X ω * Real.exp (v * X ω)]) / mgf X μ v ^ 2 -
                2 * deriv (cgf X μ) v * iteratedDeriv 2 (cgf X μ) v)
      (((μ[fun ω => X ω ^ 4] * mgf X μ 0 + μ[fun ω => X ω ^ 3] * μ[X] -
            (μ[fun ω => X ω ^ 3] * μ[X] + μ[fun ω => X ω ^ 2] ^ 2)) * mgf X μ 0 ^ 2 -
         (μ[fun ω => X ω ^ 3] * mgf X μ 0 -
            μ[fun ω => X ω ^ 2] * μ[X]) *
              (2 * mgf X μ 0 ^ 1 * μ[X])) / (mgf X μ 0 ^ 2) ^ 2 -
       2 *
         (deriv (deriv (cgf X μ)) 0 * iteratedDeriv 2 (cgf X μ) 0 +
            deriv (cgf X μ) 0 * deriv (iteratedDeriv 2 (cgf X μ)) 0)) 0 :=
    hNM_d.sub h2EG_d'
  rw [hF_d.deriv]
  -- Substitute the K_2 and K_3 closed forms.
  rw [hB0, hE0, h_dd_eq, hK2, hK3]
  ring

/-- **Fourth central moment equals fourth cumulant plus `3 K_2²`**
    (paper Eq. 1 etc.).  `μ_4 = K_4 + 3 K_2²`.

    Discharged via direct derivative computation `cumulant_four_expand`
    (closed form for `K_4`) + `centralMoment_four_expand` (closed form
    for `μ_4`) + `cumulant_two_eq_variance` (relating `K_2` to variance);
    the resulting polynomial identity in `μ[X]`, `μ[X²]`, `μ[X³]`, `μ[X⁴]`
    closes by `ring`. -/
theorem centralMoment_four_eq_cumulant_four_plus
    [IsProbabilityMeasure μ] (h : 0 ∈ interior (integrableExpSet X μ)) :
    centralMoment X 4 μ = cumulant 4 X μ + 3 * cumulant 2 X μ ^ 2 := by
  rw [centralMoment_four_expand h, cumulant_four_expand h,
      cumulant_two_eq_variance h]
  -- Expand `Var[X; μ]` to its integral form for the final `ring`.
  have hX_int : Integrable X μ :=
    (memLp_of_mem_interior_integrableExpSet h (p := 1)).integrable (by norm_num)
  have hX2_int := integrable_pow_of_mem_interior_integrableExpSet h 2 (by norm_num)
  have hμ_univ : μ.real Set.univ = 1 := by simp
  -- `Var[X; μ] = μ[X²] - μ[X]²`.
  have hvar : Var[X; μ] = μ[fun ω => X ω ^ 2] - μ[X] ^ 2 := by
    rw [variance_eq_integral hX_int.aemeasurable]
    have h_eq : ∀ ω : Ω, (X ω - μ[X]) ^ 2 = X ω ^ 2 - 2 * μ[X] * X ω + μ[X] ^ 2 := by
      intro ω; ring
    rw [show (fun ω : Ω => (X ω - μ[X]) ^ 2) =
        (fun ω => X ω ^ 2 - 2 * μ[X] * X ω + μ[X] ^ 2) from funext h_eq]
    have h1 : Integrable (fun ω => X ω ^ 2 - 2 * μ[X] * X ω) μ :=
      hX2_int.sub (hX_int.const_mul (2 * μ[X]))
    rw [integral_add h1 (integrable_const _)]
    rw [integral_sub hX2_int (hX_int.const_mul (2 * μ[X]))]
    rw [integral_const_mul, integral_const, hμ_univ, one_smul]
    ring
  rw [hvar]; ring

/-- **Cumulant skewness ↔ central-moment skewness**:
    `Skew = K_3 / K_2^(3/2) = μ_3 / σ³`. -/
theorem cumulantSkewness_eq_centralMoment_ratio
    [IsProbabilityMeasure μ] (h : 0 ∈ interior (integrableExpSet X μ)) :
    cumulantSkewness X μ = centralMoment X 3 μ / Var[X; μ] ^ ((3 : ℝ) / 2) := by
  unfold cumulantSkewness
  rw [cumulant_three_eq_centralMoment_three h, cumulant_two_eq_variance h]

/-- **Cumulant kurtosis ↔ central-moment kurtosis**:
    `Kurt = 3 + K_4 / K_2² = μ_4 / σ⁴` (raw kurtosis form: `μ_4 / Var²`). -/
theorem cumulantKurtosis_eq_centralMoment_ratio
    [IsProbabilityMeasure μ] (h : 0 ∈ interior (integrableExpSet X μ))
    (hVar : Var[X; μ] ≠ 0) :
    cumulantKurtosis X μ = centralMoment X 4 μ / Var[X; μ] ^ 2 := by
  unfold cumulantKurtosis
  rw [centralMoment_four_eq_cumulant_four_plus h, cumulant_two_eq_variance h]
  field_simp
  ring
