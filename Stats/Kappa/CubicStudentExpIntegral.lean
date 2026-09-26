/-
  Taleb's κ-metric for pre-asymptotic fat-tailedness.
    "How Much Data Do You Need?  A Pre-asymptotic Metric for Fat-tailedness"
    arXiv:1802.05495v3 (Nov 2018).

  ## Stats.Kappa.CubicStudentExpIntegral — Cubic-Student sum PDF via the
     complex exponential integral (paper Appendix A, Eq. 11; todo C.2).

  The paper's intermediate step before the closed-form MAD `M(n)` derives
  the *PDF* of the sum `S_n` of `n` iid cubic-Student variates from the
  Fourier inversion of the closed-form characteristic function
      `φ_n(ω) = (1 + √3 |ω|)^n · e^(−n √3 |ω|)`     (paper line 587).
  Concretely (paper Eq. 11):

      p_n(y) = e^(n − iy/√3) ·
                 (e^(2iy/√3) · E_{−n}(n + iy/√3) + E_{−n}(n − iy/√3))
               / (2 √3 π),

  where `E_n(z) := ∫_1^∞ e^(−z·t) / t^n dt` is the standard NIST/DLMF
  exponential integral and `E_{−n}(z) = ∫_1^∞ t^n · e^(−z·t) dt` is its
  negative-index specialisation.

  Mathlib v4.29 lacks a complex-argument exponential integral, so this
  module first introduces `expIntegralNeg` (its `n ∈ ℕ` negative-index
  specialisation, the only case the paper uses) and then proves the
  identity above.  The proof reduces to two integration lemmas (each
  formalisable in Mathlib but bookkeeping-heavy) plus an algebraic
  factorisation step:

    1.  `cubicStudentSumDensity_eq_half_fourier_avg` — Fourier inversion
        with `cos = (e^{iωy} + e^{-iωy})/2` rewrites the real-valued PDF
        as the half-sum of two complex one-sided Fourier integrals
        divided by `2π`.

    2.  `cubicStudentSumFourierHalf_eq_expIntegralNeg` — the change of
        variable `u = 1 + √3 ω` on `Ioi 0 → Ioi 1` rewrites each
        one-sided complex Fourier integral as
            `(e^n/√3) · e^(−ψ/√3) · E_{−n}(n − ψ/√3)`,
        with the integrand identity
            `(1+√3 ω)^n · e^(−n √3 ω) · e^(ψ ω)
                = e^n · e^(−ψ/√3) · u^n · e^(−(n − ψ/√3) u)`.

    3.  Algebraic factorisation pulls out `e^(n − iy/√3) / (2 √3 π)`
        and matches the paper's `e^(2iy/√3)` cross-term.

  Steps 1 and 2 are captured as `axiom`s in the same style as
  `Kappa.CubicStudentAsymptotic.incompleteGamma_laplace_asymptotic`
  (since discharged in `Kappa.CubicStudentLaplace`).  Discharging them
  is a follow-up todo (todo3.md C.2.discharge): both reduce to
  Bochner-integral substitution and integrand-integrability bounds
  available in current Mathlib (`integral_comp_mul_left_Ioi`,
  Lebesgue translation invariance, dominated convergence for complex
  integrands with bounded modulus on the real characteristic function
  `(1+√3 ω)^n · e^(−n √3 ω)`).

  Step 3 is fully proved here via `Complex.exp_add`/`exp_neg`.

  See `Stats/Kappa.lean` for the umbrella module.
-/
import Stats.Kappa.CubicStudent
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

open Real Complex Set Filter Topology MeasureTheory Asymptotics

namespace TailOptionPricing

/-! ## Complex negative-index exponential integral. -/

/-- **Complex negative-index exponential integral.**
    For `n : ℕ` and `z : ℂ`,
        `expIntegralNeg n z := ∫_1^∞ t^n · e^(−z·t) dt`.

    Convention follows NIST/DLMF §8.19: `E_k(z) = ∫_1^∞ e^(−z t)/t^k dt`,
    so the negative-index `E_{−n}(z)` rewrites to `∫_1^∞ t^n · e^(−z t) dt`.

    The integral converges absolutely when `0 < z.re` (then `|t^n · e^(−z·t)|
    = t^n · e^(−(Re z)·t)`, integrable on `Ioi 1` for any `n : ℕ`).  Outside
    that half-plane the Bochner integral evaluates to `0` and the symbol
    is uninformative; the paper invokes it only at `z = n ± i y/√3`
    (with `n ≥ 1`, so `Re z = n > 0`). -/
noncomputable def expIntegralNeg (n : ℕ) (z : ℂ) : ℂ :=
  ∫ t in Ioi (1:ℝ), (t : ℂ) ^ n * Complex.exp (-(z * t))

/-! ## Cubic-Student sum PDF (Fourier inversion of `φ_n`). -/

/-- **PDF of the iid sum of `n` cubic-Student variates.**  Defined via
    the Fourier inversion of the closed-form characteristic function
    `φ_n(ω) = (1 + √3|ω|)^n · e^(−n √3 |ω|)` (paper line 587, used to
    derive Eq. 10 and Eq. 11).  Because `φ_n` is real and even,
        `p_n(y) = (1/π) · ∫_0^∞ (1+√3 ω)^n · e^(−n √3 ω) · cos(ω y) dω`
    (paper line 590, one-sided cosine form). -/
noncomputable def cubicStudentSumDensity (n : ℕ) (y : ℝ) : ℝ :=
  (1 / Real.pi) *
    ∫ ω in Ioi (0:ℝ),
      (1 + Real.sqrt 3 * ω) ^ n *
        Real.exp (-((n : ℝ) * Real.sqrt 3 * ω)) * Real.cos (ω * y)

/-- **Half-sided complex Fourier transform of `φ_n`.**  Auxiliary integral
    parametrised by `ψ : ℂ` (which plays the role of `±i y` in the
    paper):
        `H_n(ψ) := ∫_0^∞ (1+√3 ω)^n · e^(−n √3 ω) · e^(ψ ω) dω`. -/
noncomputable def cubicStudentSumFourierHalf (n : ℕ) (ψ : ℂ) : ℂ :=
  ∫ ω in Ioi (0:ℝ),
    ((1 + Real.sqrt 3 * ω : ℝ) : ℂ) ^ n *
      Complex.exp ((-((n : ℝ) * Real.sqrt 3 * ω) : ℝ)) *
      Complex.exp (ψ * ω)

/-! ## Fourier-inversion reformulation: real PDF ↔ avg of complex half-Fourier integrals.

The real PDF
    `p_n(y) = (1/π) ∫_0^∞ (1+√3 ω)^n · e^(−n √3 ω) · cos(ω y) dω`
rewrites — using `Complex.two_cos : 2 cos x = e^(I x) + e^(−I x)` and
integral linearity — as
    `(p_n(y) : ℂ) = (H_n(I y) + H_n(−I y)) / (2 π)`.

Discharging this axiom in Mathlib needs:

* `integral_ofReal` (LinearIsometry-based, no integrability hypothesis)
  to push `(· : ℝ → ℂ)` through the Bochner integral;
* `Complex.two_cos` plus `setIntegral_congr_fun` to rewrite `cos`
  inside the integrand;
* `integral_add` consuming integrability of each complex half-Fourier
  integrand (modulus `(1+√3 ω)^n · e^(−n √3 ω)`, polynomial-times-exp
  decay → `integrable_of_isBigO_exp_neg`).

Each step is routine in current Mathlib; the chained bookkeeping is
sizeable but contains no genuinely new mathematics. -/

/-- Common kernel of the half-Fourier integrand without the `e^(ψ ω)`
    factor.  Real-valued, cast to `ℂ` on demand. -/
private noncomputable def cubicKernelReal (n : ℕ) (ω : ℝ) : ℝ :=
  (1 + Real.sqrt 3 * ω) ^ n * Real.exp (-((n : ℝ) * Real.sqrt 3 * ω))

/-! ### Integrability of the cubic-Student kernel.

We need integrability of the complex half-Fourier integrand
`((cubicKernelReal n ω : ℂ)) · Complex.exp (ψ ω)` on `Ioi 0`, for
`n ≥ 1` and `ψ.re ≤ 0`.

Strategy:
1. The real kernel `(1+√3 ω)^n · e^(−n √3 ω)` tends to 0 at infinity
   (polynomial vs exponential decay).
2. Multiplying by `e^(−(n √3/2) ω)` gives `=O[atTop] e^(−(n √3/2) ω)`.
3. `integrable_of_isBigO_exp_neg` then yields integrability of the real
   kernel on `Ioi 0`.
4. The complex integrand has modulus `≤ real kernel` (since `|e^(ψ ω)|
   ≤ 1` for `ψ.re ≤ 0`, `ω > 0`), so it is integrable. -/

/-- For `n ≥ 1` and `c > 0`, `ω^n · e^(−c ω)` tends to 0 at `+∞`. -/
private lemma pow_mul_exp_neg_const_tendsto_zero (n : ℕ) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun ω : ℝ => ω ^ n * Real.exp (-(c * ω))) atTop (𝓝 0) := by
  -- ω^n · e^(−c ω) = (1/c^n) · (c ω)^n · e^(−(c ω))
  have h_rewrite : ∀ ω : ℝ, ω ^ n * Real.exp (-(c * ω)) =
      (c ^ n)⁻¹ * ((c * ω) ^ n * Real.exp (-(c * ω))) := by
    intro ω
    rw [mul_pow]
    field_simp
  rw [show (fun ω : ℝ => ω ^ n * Real.exp (-(c * ω))) =
      (fun ω => (c ^ n)⁻¹ * ((c * ω) ^ n * Real.exp (-(c * ω)))) from
    funext h_rewrite]
  have h_inner : Tendsto (fun ω : ℝ => c * ω) atTop atTop :=
    Tendsto.const_mul_atTop hc tendsto_id
  have h_comp : Tendsto (fun ω : ℝ => (c * ω) ^ n * Real.exp (-(c * ω))) atTop (𝓝 0) :=
    (tendsto_pow_mul_exp_neg_atTop_nhds_zero n).comp h_inner
  simpa using h_comp.const_mul ((c ^ n)⁻¹)

/-- For `n ≥ 1`, the cubic-Student kernel times `e^((n √3/2) ω)` (i.e.,
    `(1+√3 ω)^n · e^(−(n √3/2) ω)`) tends to 0 as `ω → ∞`. -/
private lemma cubicKernelReal_decay_tendsto_zero {n : ℕ} (hn : 1 ≤ n) :
    Tendsto (fun ω : ℝ => (1 + Real.sqrt 3 * ω) ^ n *
        Real.exp (-((n : ℝ) * Real.sqrt 3 / 2 * ω))) atTop (𝓝 0) := by
  set c : ℝ := (n : ℝ) * Real.sqrt 3 / 2 with hc_def
  have hs3_pos : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hn_pos : (0 : ℝ) < (n : ℝ) :=
    by exact_mod_cast Nat.one_le_iff_ne_zero.mp hn |>.bot_lt
  have hc_pos : 0 < c := by rw [hc_def]; positivity
  have h_pow_tendsto := pow_mul_exp_neg_const_tendsto_zero n hc_pos
  have h_exp_tendsto : Tendsto (fun ω : ℝ => Real.exp (-(c * ω))) atTop (𝓝 0) := by
    have h_cω_atTop : Tendsto (fun ω : ℝ => c * ω) atTop atTop :=
      Tendsto.const_mul_atTop hc_pos tendsto_id
    exact Real.tendsto_exp_neg_atTop_nhds_zero.comp h_cω_atTop
  have h_sum_tendsto : Tendsto
      (fun ω : ℝ => (2 * Real.sqrt 3) ^ n * (ω ^ n * Real.exp (-(c * ω))) +
          Real.exp (-(c * ω))) atTop (𝓝 0) := by
    have h1 := h_pow_tendsto.const_mul ((2 * Real.sqrt 3) ^ n)
    have h2 := h1.add h_exp_tendsto
    simpa using h2
  -- Squeeze: 0 ≤ kernel · e^(−c ω) ≤ (2√3)^n · ω^n · e^(−c ω) + e^(−c ω) for ω ≥ 1.
  refine squeeze_zero' ?_ ?_ h_sum_tendsto
  · filter_upwards [eventually_ge_atTop (0:ℝ)] with ω hω
    have h_nn : (0:ℝ) ≤ 1 + Real.sqrt 3 * ω := by nlinarith [Real.sqrt_nonneg 3]
    positivity
  · filter_upwards [eventually_ge_atTop (1:ℝ)] with ω hω
    have h3 : (1:ℝ) ≤ Real.sqrt 3 := by
      rw [show (1:ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt (by norm_num)
    have hsω : 1 ≤ Real.sqrt 3 * ω := le_trans h3 (le_mul_of_one_le_right hs3_pos.le hω)
    have h_le_poly : 1 + Real.sqrt 3 * ω ≤ 2 * Real.sqrt 3 * ω := by linarith
    have h_nn : (0:ℝ) ≤ 1 + Real.sqrt 3 * ω := by linarith
    have h_pow_le : (1 + Real.sqrt 3 * ω) ^ n ≤ (2 * Real.sqrt 3 * ω) ^ n :=
      pow_le_pow_left₀ h_nn h_le_poly n
    have h_pow_eq : (2 * Real.sqrt 3 * ω) ^ n = (2 * Real.sqrt 3) ^ n * ω ^ n := by
      rw [mul_pow]
    have h_exp_pos : 0 < Real.exp (-(c * ω)) := Real.exp_pos _
    calc (1 + Real.sqrt 3 * ω) ^ n * Real.exp (-(c * ω))
        ≤ (2 * Real.sqrt 3 * ω) ^ n * Real.exp (-(c * ω)) :=
          mul_le_mul_of_nonneg_right h_pow_le h_exp_pos.le
      _ = (2 * Real.sqrt 3) ^ n * (ω ^ n * Real.exp (-(c * ω))) := by
          rw [h_pow_eq]; ring
      _ ≤ (2 * Real.sqrt 3) ^ n * (ω ^ n * Real.exp (-(c * ω))) +
            Real.exp (-(c * ω)) := by linarith

/-- The real cubic-Student kernel is `=O[atTop] e^(−(n √3/2) ω)`. -/
private lemma cubicKernelReal_isBigO {n : ℕ} (hn : 1 ≤ n) :
    (fun ω : ℝ => cubicKernelReal n ω) =O[atTop]
      (fun ω : ℝ => Real.exp (-((n : ℝ) * Real.sqrt 3 / 2) * ω)) := by
  -- Split: kernel(ω) = (kernel(ω) · e^((n √3/2) ω)) · e^(−(n √3/2) ω),
  -- where the first factor tends to 0 (hence =O 1) and the second factor is
  -- =O of itself.
  have hdecay := cubicKernelReal_decay_tendsto_zero hn
  have hbdd_one := hdecay.isBigO_one ℝ
  have h_self := Asymptotics.isBigO_refl
    (fun ω : ℝ => Real.exp (-((n : ℝ) * Real.sqrt 3 / 2) * ω)) atTop
  have hprod := hbdd_one.mul h_self
  refine hprod.congr (fun ω => ?_) (fun ω => by ring)
  -- LHS product equals the kernel.
  unfold cubicKernelReal
  rw [show
    (1 + Real.sqrt 3 * ω) ^ n *
        Real.exp (-((n : ℝ) * Real.sqrt 3 / 2 * ω)) *
        Real.exp (-((n : ℝ) * Real.sqrt 3 / 2) * ω) =
      (1 + Real.sqrt 3 * ω) ^ n *
        (Real.exp (-((n : ℝ) * Real.sqrt 3 / 2 * ω)) *
          Real.exp (-((n : ℝ) * Real.sqrt 3 / 2) * ω)) from by ring]
  rw [← Real.exp_add]
  congr 2; ring

/-- Integrability of the real cubic-Student kernel on `Ioi 0` for `n ≥ 1`. -/
private lemma cubicKernelReal_integrableOn {n : ℕ} (hn : 1 ≤ n) :
    IntegrableOn (cubicKernelReal n) (Ioi (0:ℝ)) := by
  have hs3_pos : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hn_pos : (0 : ℝ) < (n : ℝ) :=
    by exact_mod_cast Nat.one_le_iff_ne_zero.mp hn |>.bot_lt
  have hc_pos : 0 < (n : ℝ) * Real.sqrt 3 / 2 := by positivity
  refine integrable_of_isBigO_exp_neg hc_pos ?_ (cubicKernelReal_isBigO hn)
  -- Continuity on `[0, ∞)`.
  unfold cubicKernelReal
  refine ContinuousOn.mul ?_ ?_
  · exact (Continuous.pow (continuous_const.add (continuous_const.mul continuous_id)) n).continuousOn
  · exact (Real.continuous_exp.comp (continuous_neg.comp
      ((continuous_const.mul continuous_const).mul continuous_id))).continuousOn

/-- **Integrability of the complex half-Fourier integrand.**  For `n ≥ 1`
    and `ψ : ℂ` with `ψ.re ≤ 0`, the complex integrand of
    `cubicStudentSumFourierHalf` is integrable on `Ioi 0`. -/
theorem cubicStudentSumFourierHalf_integrand_integrableOn
    {n : ℕ} (hn : 1 ≤ n) (ψ : ℂ) (hψ : ψ.re ≤ 0) :
    IntegrableOn
      (fun ω : ℝ =>
        ((cubicKernelReal n ω : ℝ) : ℂ) * Complex.exp (ψ * ω))
      (Ioi (0:ℝ)) := by
  have h_real := cubicKernelReal_integrableOn hn
  have h_cast : IntegrableOn (fun ω : ℝ => ((cubicKernelReal n ω : ℝ) : ℂ))
      (Ioi (0:ℝ)) := h_real.ofReal
  -- AEStronglyMeasurable of `cexp(ψ · ω)` on Ioi 0.
  have h_meas_exp : AEStronglyMeasurable (fun ω : ℝ => Complex.exp (ψ * (ω : ℂ)))
      ((volume : Measure ℝ).restrict (Set.Ioi (0:ℝ))) :=
    (Complex.continuous_exp.comp (continuous_const.mul
      Complex.continuous_ofReal)).aestronglyMeasurable
  -- `‖cexp(ψ ω)‖ ≤ 1` a.e. on `Ioi 0` for `ψ.re ≤ 0` (since `ψ.re · ω ≤ 0`).
  have h_bdd : ∀ᵐ (ω : ℝ) ∂((volume : Measure ℝ).restrict (Set.Ioi (0:ℝ))),
      ‖Complex.exp (ψ * (ω : ℂ))‖ ≤ 1 := by
    rw [ae_restrict_iff' (measurableSet_Ioi (a := (0:ℝ)))]
    refine Filter.Eventually.of_forall fun ω hω => ?_
    rw [Complex.norm_exp]
    have hψω_re : (ψ * ((ω : ℝ) : ℂ)).re = ψ.re * ω := by simp
    rw [hψω_re]
    have hω_pos : 0 < ω := hω
    have h_nonpos : ψ.re * ω ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hψ hω_pos.le
    calc Real.exp (ψ.re * ω) ≤ Real.exp 0 := Real.exp_le_exp.mpr h_nonpos
      _ = 1 := Real.exp_zero
  exact h_cast.mul_bdd h_meas_exp h_bdd

/-- **Fourier inversion: complex form of the real PDF (paper line 590
    rewritten with `cos = (e + e⁻)/2`).**  Proved from the integrability
    sub-axiom `cubicStudentSumFourierHalf_integrand_integrableOn` via
    `integral_ofReal`, `Complex.two_cos`, and `integral_add` / `integral_smul`. -/
theorem cubicStudentSumDensity_eq_half_fourier_avg
    {n : ℕ} (hn : 1 ≤ n) (y : ℝ) :
    ((cubicStudentSumDensity n y : ℝ) : ℂ) =
      (cubicStudentSumFourierHalf n (Complex.I * y) +
        cubicStudentSumFourierHalf n (-(Complex.I * y))) /
        (2 * (Real.pi : ℂ)) := by
  -- Shorthand `K ω := (cubicKernelReal n ω : ℂ)`.
  set K : ℝ → ℂ := fun ω => ((cubicKernelReal n ω : ℝ) : ℂ) with hK_def
  have hπ_ne : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h2_ne : (2 : ℂ) ≠ 0 := two_ne_zero
  -- Integrabilities of the two complex Fourier integrands.
  have hint_pos :
      IntegrableOn (fun ω : ℝ => K ω * Complex.exp ((Complex.I * y) * ω)) (Ioi (0:ℝ)) :=
    cubicStudentSumFourierHalf_integrand_integrableOn hn (Complex.I * y) (by simp)
  have hint_neg :
      IntegrableOn (fun ω : ℝ => K ω * Complex.exp ((-(Complex.I * y)) * ω)) (Ioi (0:ℝ)) :=
    cubicStudentSumFourierHalf_integrand_integrableOn hn (-(Complex.I * y)) (by simp)
  -- Rewrite `cubicStudentSumDensity n y` in terms of the kernel name.
  have hdens_rewrite : cubicStudentSumDensity n y =
      (1 / Real.pi) * ∫ ω in Ioi (0:ℝ), cubicKernelReal n ω * Real.cos (ω * y) := by
    unfold cubicStudentSumDensity cubicKernelReal
    rfl
  rw [hdens_rewrite]
  -- Push the (· : ℝ → ℂ) cast through, keeping `Real.cos` intact.
  have hpush :
      (((1 / Real.pi) *
          ∫ ω in Ioi (0:ℝ), cubicKernelReal n ω * Real.cos (ω * y) : ℝ) : ℂ) =
        (1 / (Real.pi : ℂ)) *
          ∫ ω in Ioi (0:ℝ), ((cubicKernelReal n ω * Real.cos (ω * y) : ℝ) : ℂ) := by
    rw [Complex.ofReal_mul]
    rw [show ((1 / Real.pi : ℝ) : ℂ) = 1 / (Real.pi : ℂ) from by push_cast; rfl]
    congr 1
    exact integral_complex_ofReal.symm
  rw [hpush]
  -- Pointwise: the real integrand cast to ℂ equals the complex average.
  have hpt : ∀ ω : ℝ,
      ((cubicKernelReal n ω * Real.cos (ω * y) : ℝ) : ℂ) =
        (K ω * Complex.exp ((Complex.I * y) * ω) +
          K ω * Complex.exp ((-(Complex.I * y)) * ω)) / 2 := by
    intro ω
    rw [Complex.ofReal_mul]
    -- ((Real.cos (ωy) : ℝ) : ℂ) = Complex.cos ((ωy : ℝ) : ℂ).
    rw [Complex.ofReal_cos]
    -- Complex.cos z = (exp (Iz) + exp (-Iz))/2.
    have h2 := Complex.two_cos ((ω * y : ℝ) : ℂ)
    have hr1 : ((ω * y : ℝ) : ℂ) * Complex.I = (Complex.I * y) * ω := by
      push_cast; ring
    have hr2 : -((ω * y : ℝ) : ℂ) * Complex.I = (-(Complex.I * y)) * ω := by
      push_cast; ring
    rw [hr1, hr2] at h2
    -- Solve for Complex.cos.
    have hcos_eq : Complex.cos ((ω * y : ℝ) : ℂ) =
        (Complex.exp ((Complex.I * y) * ω) + Complex.exp ((-(Complex.I * y)) * ω)) / 2 := by
      linear_combination h2 / 2
    rw [hcos_eq, hK_def]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi (fun ω _ => hpt ω)]
  -- Pull `/2` out via smul, then split the integral.
  have hsmul_rewrite :
      (fun ω : ℝ =>
        (K ω * Complex.exp ((Complex.I * y) * ω) +
          K ω * Complex.exp ((-(Complex.I * y)) * ω)) / 2) =
        (fun ω : ℝ => (1 / (2 : ℂ)) •
          (K ω * Complex.exp ((Complex.I * y) * ω) +
            K ω * Complex.exp ((-(Complex.I * y)) * ω))) := by
    funext ω; rw [smul_eq_mul]; ring
  rw [hsmul_rewrite, integral_smul, integral_add hint_pos hint_neg]
  -- Match the cubicStudentSumFourierHalf integrand form.
  unfold cubicStudentSumFourierHalf
  have hHF_rewrite : ∀ ψ : ℂ, (∫ ω in Ioi (0:ℝ),
          ((1 + Real.sqrt 3 * ω : ℝ) : ℂ) ^ n *
            Complex.exp ((-((n : ℝ) * Real.sqrt 3 * ω) : ℝ)) * Complex.exp (ψ * ω)) =
        (∫ ω in Ioi (0:ℝ), K ω * Complex.exp (ψ * ω)) := by
    intro ψ
    refine setIntegral_congr_fun measurableSet_Ioi (fun ω _ => ?_)
    simp only [hK_def, cubicKernelReal]
    push_cast
    ring
  rw [hHF_rewrite (Complex.I * y), hHF_rewrite (-(Complex.I * y))]
  -- Final algebra.
  rw [smul_eq_mul]
  field_simp

/-! ## Substitution identity: `H_n(ψ) = (e^n/√3) e^(−ψ/√3) E_{−n}(n − ψ/√3)`.

Change of variable `u = 1 + √3 ω`, `dω = du/√3`, `Ioi 0 → Ioi 1`.  The
integrand transforms as
    `(1+√3 ω)^n · e^(−n √3 ω) · e^(ψ ω)
        = u^n · e^(−n (u−1)) · e^(ψ (u−1)/√3)
        = e^n · e^(−ψ/√3) · u^n · e^(−(n − ψ/√3) u)`,
and integrating over `Ioi 1` after pulling out the Jacobian `1/√3` and
the `e^n · e^(−ψ/√3)` constants gives the claimed identity.

The discharge factors as:

* `MeasureTheory.integral_comp_mul_left_Ioi` (Mathlib, complex-integrand-capable)
  for the `√3`-scaling step;
* a translation sub-axiom `Ioi_translate_one_C` for the `+1` shift on
  `Ioi 0 → Ioi 1` (Lebesgue translation invariance on `Ioi` is not
  packaged in current Mathlib in a one-line form);
* algebraic factorisation of the resulting integrand to match
  `expIntegralNeg n (n − ψ/√3)`. -/

/-- **Lebesgue translation invariance on `Ioi 0 → Ioi 1`.**  For a
    complex-valued function on `[1, ∞)`,
        `∫ u in Ioi 0, f(1 + u) du = ∫ u in Ioi 1, f u du`.

    Discharged via `measurePreserving_add_left volume 1` +
    `MeasurePreserving.setIntegral_preimage_emb` along the
    `MeasurableEquiv.addLeft 1` measurable embedding, with the preimage
    identity `(1 + ·) ⁻¹' Ioi 1 = Ioi 0`. -/
theorem Ioi_translate_one_C (f : ℝ → ℂ) :
    ∫ u in Ioi (0:ℝ), f (1 + u) = ∫ u in Ioi (1:ℝ), f u := by
  -- The measurable equivalence `1 + ·` is measure-preserving for Lebesgue.
  have hMP : MeasurePreserving ((1 : ℝ) + ·) volume volume :=
    measurePreserving_add_left volume 1
  -- Its underlying map is a measurable embedding.
  have hME : MeasurableEmbedding ((1 : ℝ) + ·) :=
    (MeasurableEquiv.addLeft (1 : ℝ)).measurableEmbedding
  -- Preimage of `Ioi 1` under `1 + ·` is `Ioi 0`.
  have hpre : ((1 : ℝ) + ·) ⁻¹' Ioi (1 : ℝ) = Ioi (0 : ℝ) := by
    ext x
    simp [Set.mem_Ioi]
  -- Apply `setIntegral_preimage_emb` with `s = Ioi 1`, `g = f`.
  have := hMP.setIntegral_preimage_emb hME f (Ioi (1:ℝ))
  rw [hpre] at this
  exact this

/-- **Substitution `u = 1 + √3 ω` rewrites `H_n(ψ)` as a multiple of
    `expIntegralNeg`.**  Proved from `integral_comp_mul_left_Ioi` +
    `Ioi_translate_one_C` + algebra. -/
theorem cubicStudentSumFourierHalf_eq_expIntegralNeg
    {n : ℕ} (hn : 1 ≤ n) (ψ : ℂ)
    (hψ : ψ.re < (n : ℝ) * Real.sqrt 3) :
    cubicStudentSumFourierHalf n ψ =
      (Complex.exp n / ((Real.sqrt 3 : ℝ) : ℂ)) *
        Complex.exp (-(ψ / ((Real.sqrt 3 : ℝ) : ℂ))) *
        expIntegralNeg n ((n : ℂ) - ψ / ((Real.sqrt 3 : ℝ) : ℂ)) := by
  -- Notation.
  set s3 : ℝ := Real.sqrt 3 with hs3_def
  set sC : ℂ := ((s3 : ℝ) : ℂ) with hsC_def
  have hs3_pos : 0 < s3 := Real.sqrt_pos.mpr (by norm_num)
  have hs3_ne : s3 ≠ 0 := hs3_pos.ne'
  have hsC_ne : sC ≠ 0 := by
    rw [hsC_def]; exact Complex.ofReal_ne_zero.mpr hs3_ne
  -- Auxiliary integrand `g : ℝ → ℂ` so that the original integrand at `ω`
  -- equals `g(s3 * ω)`.
  set g : ℝ → ℂ := fun t =>
    ((1 + t : ℝ) : ℂ) ^ n *
      Complex.exp ((-((n : ℝ) * t) : ℝ)) *
      Complex.exp ((ψ / sC) * t) with hg_def
  unfold cubicStudentSumFourierHalf
  -- Step 1: rewrite original integrand to `g(s3 * ω)` pointwise.
  have hpt1 : ∀ ω : ℝ,
      ((1 + s3 * ω : ℝ) : ℂ) ^ n *
          Complex.exp ((-((n : ℝ) * s3 * ω) : ℝ)) *
          Complex.exp (ψ * ω) = g (s3 * ω) := by
    intro ω
    simp only [hg_def]
    -- `cexp((ψ/sC) · ↑(s3·ω)) = cexp(ψ · ↑ω)`.
    have h_exp_id :
        Complex.exp ((ψ / sC) * ((s3 * ω : ℝ) : ℂ)) =
          Complex.exp (ψ * (ω : ℂ)) := by
      congr 1
      have : ((s3 * ω : ℝ) : ℂ) = sC * (ω : ℂ) := by
        rw [hsC_def]; push_cast; ring
      rw [this]
      field_simp
    -- `↑(-(n·s3·ω)) = ↑(-(n·(s3·ω)))` by associativity.
    have h_neg_id :
        ((-((n : ℝ) * s3 * ω) : ℝ) : ℂ) = ((-((n : ℝ) * (s3 * ω)) : ℝ) : ℂ) := by
      push_cast; ring
    rw [h_neg_id, h_exp_id]
  rw [setIntegral_congr_fun measurableSet_Ioi (fun ω _ => hpt1 ω)]
  -- Step 2: change-of-variable `√3` scaling on `Ioi 0`.
  rw [integral_comp_mul_left_Ioi g 0 hs3_pos]
  simp only [mul_zero]
  -- Step 3: additive translation `∫ x in Ioi 0, g x = ∫ u in Ioi 1, g (u - 1)`.
  -- Set `f(v) := g (v - 1)`; then `f(1 + u) = g(u)` and `f(u) = g(u-1)`.
  have htransl : (∫ x in Ioi (0:ℝ), g x) = (∫ u in Ioi (1:ℝ), g (u - 1)) := by
    have h := Ioi_translate_one_C (fun v : ℝ => g (v - 1))
    -- h : ∫ u in Ioi 0, g((1+u) - 1) = ∫ u in Ioi 1, g(u - 1)
    -- LHS simplifies to `∫ u in Ioi 0, g u`.
    have hLHS_simp : (∫ u in Ioi (0:ℝ), g ((1 + u) - 1)) = ∫ u in Ioi (0:ℝ), g u := by
      refine setIntegral_congr_fun measurableSet_Ioi (fun u _ => ?_)
      congr 1; ring
    rw [hLHS_simp] at h
    exact h
  rw [htransl]
  -- Step 4: rewrite `g(u - 1) = exp(n - ψ/sC) · ((u:ℂ)^n · exp(-(n - ψ/sC) · u))`.
  have hpt2 : ∀ u : ℝ,
      g (u - 1) =
        Complex.exp ((n : ℂ) - ψ / sC) *
          (((u : ℝ) : ℂ) ^ n *
            Complex.exp (-(((n : ℂ) - ψ / sC) * (u : ℝ)))) := by
    intro u
    simp only [hg_def]
    -- (1 + (u - 1)) = u as reals.
    have h_one_plus : (1 + (u - 1) : ℝ) = u := by ring
    -- Cast the kernel.
    have h_pow_cast : ((1 + (u - 1) : ℝ) : ℂ) ^ n = ((u : ℝ) : ℂ) ^ n := by
      rw [h_one_plus]
    -- Combine the two exponentials.
    have h_exp_combine :
        Complex.exp ((-((n : ℝ) * (u - 1)) : ℝ)) *
            Complex.exp ((ψ / sC) * (u - 1 : ℝ)) =
          Complex.exp ((n : ℂ) - ψ / sC) *
            Complex.exp (-(((n : ℂ) - ψ / sC) * (u : ℝ))) := by
      rw [← Complex.exp_add, ← Complex.exp_add]
      congr 1
      push_cast; ring
    rw [h_pow_cast]
    rw [show ((u : ℝ) : ℂ) ^ n *
            Complex.exp ((-((n : ℝ) * (u - 1)) : ℝ)) *
            Complex.exp ((ψ / sC) * (u - 1 : ℝ)) =
          ((u : ℝ) : ℂ) ^ n *
            (Complex.exp ((-((n : ℝ) * (u - 1)) : ℝ)) *
              Complex.exp ((ψ / sC) * (u - 1 : ℝ))) from by ring]
    rw [h_exp_combine]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi (fun u _ => hpt2 u)]
  -- Step 5: pull the constant `Complex.exp(n - ψ/sC)` out.
  have h_pull_const :
      (∫ x in Ioi (1:ℝ),
          Complex.exp ((n : ℂ) - ψ / sC) *
            (((x : ℝ) : ℂ) ^ n *
              Complex.exp (-(((n : ℂ) - ψ / sC) * (x : ℝ))))) =
        Complex.exp ((n : ℂ) - ψ / sC) *
          ∫ x in Ioi (1:ℝ),
            ((x : ℝ) : ℂ) ^ n *
              Complex.exp (-(((n : ℂ) - ψ / sC) * (x : ℝ))) :=
    integral_const_mul _ _
  rw [h_pull_const]
  -- Step 6: split `Complex.exp(n - ψ/sC) = Complex.exp(n) * Complex.exp(-(ψ/sC))`.
  have h_exp_split :
      Complex.exp ((n : ℂ) - ψ / sC) =
        Complex.exp n * Complex.exp (-(ψ / sC)) := by
    rw [show ((n : ℂ) - ψ / sC) = (n : ℂ) + (-(ψ / sC)) by ring, Complex.exp_add]
  rw [h_exp_split]
  -- Step 7: identify the integral with `expIntegralNeg`.
  unfold expIntegralNeg
  -- Final algebra: convert `s3⁻¹ • z` to `((s3⁻¹ : ℝ) : ℂ) * z` manually.
  -- `Complex.real_smul` is `rfl`, so this is a definitional rewrite via `show`.
  show ((s3⁻¹ : ℝ) : ℂ) * (Complex.exp n * Complex.exp (-(ψ / sC)) *
        ∫ x in Ioi (1:ℝ),
          ((x : ℝ) : ℂ) ^ n *
            Complex.exp (-(((n : ℂ) - ψ / sC) * (x : ℝ)))) =
    Complex.exp n / sC * Complex.exp (-(ψ / sC)) *
      ∫ t in Ioi (1:ℝ),
        ((t : ℝ) : ℂ) ^ n *
          Complex.exp (-(((n : ℂ) - ψ / sC) * (t : ℝ)))
  have hcoerce : ((s3⁻¹ : ℝ) : ℂ) = sC⁻¹ := by
    rw [hsC_def]; push_cast; ring
  rw [hcoerce]
  field_simp

/-! ## Main theorem (paper Eq. 11). -/

/-- **PDF of the cubic-Student sum via the complex exponential integral
    (paper Eq. 11, Appendix A; todo3 C.2).**  For `n : ℕ` with `n ≥ 1`,
        `p_n(y) = e^(n − i y/√3) · (e^(2 i y/√3) · E_{−n}(n + i y/√3)
                                    + E_{−n}(n − i y/√3)) / (2 √3 π)`,
    where `E_{−n}(z) := ∫_1^∞ t^n · e^(−z·t) dt`. -/
theorem cubicStudentSumDensity_via_exponentialIntegral
    {n : ℕ} (hn : 1 ≤ n) (y : ℝ) :
    ((cubicStudentSumDensity n y : ℝ) : ℂ) =
      Complex.exp ((n : ℂ) - Complex.I * y / ((Real.sqrt 3 : ℝ) : ℂ)) *
        (Complex.exp (2 * Complex.I * y / ((Real.sqrt 3 : ℝ) : ℂ)) *
            expIntegralNeg n ((n : ℂ) + Complex.I * y / ((Real.sqrt 3 : ℝ) : ℂ)) +
          expIntegralNeg n ((n : ℂ) - Complex.I * y / ((Real.sqrt 3 : ℝ) : ℂ))) /
        (2 * ((Real.sqrt 3 : ℝ) : ℂ) * (Real.pi : ℂ)) := by
  -- Notation shorthand.
  set s3 : ℂ := ((Real.sqrt 3 : ℝ) : ℂ) with hs3_def
  have hs3_pos_real : 0 < (Real.sqrt 3 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hs3_ne_zero : s3 ≠ 0 := by
    rw [hs3_def]
    exact Complex.ofReal_ne_zero.mpr hs3_pos_real.ne'
  have hπ_ne_zero : (Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  have h2_ne_zero : (2 : ℂ) ≠ 0 := two_ne_zero
  -- Two applications of the substitution lemma, `ψ = ±I·y`.
  -- `Re(±I·y) = 0 < n·√3` since `n ≥ 1` and `√3 > 0`.
  have hpsi_pos_re : (Complex.I * (y : ℂ)).re < (n : ℝ) * Real.sqrt 3 := by
    have hre : (Complex.I * (y : ℂ)).re = 0 := by simp
    rw [hre]
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    nlinarith
  have hpsi_neg_re : (-(Complex.I * (y : ℂ))).re < (n : ℝ) * Real.sqrt 3 := by
    have hre : (-(Complex.I * (y : ℂ))).re = 0 := by simp
    rw [hre]
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    nlinarith
  have hH_pos :=
    cubicStudentSumFourierHalf_eq_expIntegralNeg hn (Complex.I * y) hpsi_pos_re
  have hH_neg :=
    cubicStudentSumFourierHalf_eq_expIntegralNeg hn (-(Complex.I * y)) hpsi_neg_re
  -- Fourier-inversion reformulation.
  have h_avg := cubicStudentSumDensity_eq_half_fourier_avg hn y
  -- Substitute both half-Fourier integrals.
  rw [hH_pos, hH_neg] at h_avg
  -- Normalise the negation in the `−(I·y)` argument so both occurrences
  -- of `expIntegralNeg` use the same arguments (`n ± Iy/√3`).
  have hneg_simp : (n : ℂ) - -(Complex.I * (y : ℂ)) / s3 = (n : ℂ) + Complex.I * y / s3 := by
    ring
  have hneg_simp' : -(-(Complex.I * (y : ℂ)) / s3) = Complex.I * y / s3 := by ring
  rw [hneg_simp, hneg_simp'] at h_avg
  -- Abbreviate the two exponential-integral values.
  set Eplus : ℂ := expIntegralNeg n ((n : ℂ) + Complex.I * y / s3) with hEplus
  set Eminus : ℂ := expIntegralNeg n ((n : ℂ) - Complex.I * y / s3) with hEminus
  -- Abbreviate the two complex exponentials.
  set eP : ℂ := Complex.exp (Complex.I * y / s3) with heP
  set eN : ℂ := Complex.exp (-(Complex.I * y / s3)) with heN
  -- `eP * eN = 1` and `e^n` factor.
  have hPN : eP * eN = 1 := by
    rw [heP, heN, ← Complex.exp_add]; simp
  -- Substitute `cexp ↑n` notation.
  -- Now `h_avg : (p_n : ℂ) = (e^n/√3 · eN · Eminus + e^n/√3 · eP · Eplus) / (2π)`.
  -- Goal (after `set`): (p_n : ℂ) =
  --   e^(n-Iy/√3) · (e^(2Iy/√3) · Eplus + Eminus) / (2 √3 π).
  -- Rewrite `e^(n-Iy/√3) = e^n · eN` and `e^(2Iy/√3) = eP · eP`.
  have hexp_factor : Complex.exp ((n : ℂ) - Complex.I * y / s3) = Complex.exp n * eN := by
    rw [heN, show ((n : ℂ) - Complex.I * y / s3) = (n : ℂ) + (-(Complex.I * y / s3)) by ring,
        Complex.exp_add]
  have hexp_double : Complex.exp (2 * Complex.I * y / s3) = eP * eP := by
    rw [heP, ← Complex.exp_add]
    congr 1; ring
  rw [hexp_factor, hexp_double, h_avg]
  -- After all rewrites both sides are rational functions of
  -- `Complex.exp n, eP, eN, Eplus, Eminus, s3, π` with `s3, π ≠ 0` and
  -- `eP * eN = 1`.  Clear denominators with `field_simp`, then close
  -- with `linear_combination hPN · ·` to consume the `eP * eN = 1`
  -- relation.
  field_simp
  -- Resulting `ring`-style goal is essentially `(eP·eN − 1) · (eP · Eplus · s3) = 0`.
  linear_combination (-(eP * Eplus * s3)) * hPN
