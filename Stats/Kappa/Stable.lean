module

/-
  Taleb's κ-metric for pre-asymptotic fat-tailedness.
    "How Much Data Do You Need?  A Pre-asymptotic Metric for Fat-tailedness"
    arXiv:1802.05495v3 (Nov 2018).

  ## Stats.Kappa.Stable — α-stable distribution infrastructure.

  Paper Eq. 4 defines the α-stable characteristic function in two
  cases:
      α ≠ 1:  ϕ(t) = exp(i μ t − σ^α |t|^α (1 − i β · sgn(t) · tan(π α/2)))
      α = 1:  ϕ(t) = exp(i μ t − σ |t| (1 + (2 i / π) β · sgn(t) · log|t|))

  The stable class is closed under iid summation with `σ_n = n^(1/α) σ`
  and `μ_n = n μ`: a direct consequence of `ϕ_X(t)^n` evaluation
  combined with the characteristic-function multiplicativity for iid
  sums (Mathlib has `ProbabilityTheory.charFun` infrastructure for the
  iid step; we take the multiplicativity as a hypothesis here, in the
  same shell-out pattern used for the Loulakis lognormal bound and the
  Pearson IV integration-by-parts step).

  Combined with `kappa_stable_invariance` (Stats.Kappa.Basic), the
  stable class has constant κ_{n₀, n} = 2 − ᾱ across all `(n₀, n)`.

  Theorems delivered (paper Section IV-A, todo B.4):

  * `stableCharacteristicFunction` — Eq. 4 closed form (todo B.4.1).
  * `StableClass` — class membership predicate (todo B.4.2).
  * `stable_charfun_pow_alpha_ne_one` — algebraic `ϕ(t)^n` identity for
    α ≠ 1 (algebraic content of todo B.4.3).
  * `stable_charfun_pow_alpha_eq_one` — same for the α = 1 case.
  * `stable_sum_stable` — full sum-of-stable closure given iid charfun
    multiplicativity (todo B.4.3).
  * `stable_class_kappa_invariance` — κ_{n₀, n} = 2 − ᾱ for stable
    iid sums (todo B.4.4).

  See `Stats/Kappa.lean` for the umbrella module.
-/
public import Stats.Kappa.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Real.Sign

@[expose] public section

open Real Complex Set Filter Topology

namespace TailOptionPricing

/-! ## α-stable characteristic function (paper Eq. 4, todo B.4.1). -/

/-- **α-stable characteristic function** (paper Eq. 4, todo B.4.1).
    Two-case definition, paper Eq. 4 verbatim from arXiv LaTeX source
    `kappa-n-final.tex` line 322-325:
        α ≠ 1: `ϕ(t) = exp( i μ t − |t σ|^α (1 − i β · sgn(t)·tan(π α/2)) )`
        α = 1: `ϕ(t) = exp( i t · (2β·σ·log(σ)/π + μ)
                            − |t σ| · (1 + (2 i β / π) · sgn(t) · log|t σ|) )`
    Defined as a `ℂ`-valued function of `t : ℝ`.  Parameters:
    `α ∈ (0, 2]` (stability index), `β ∈ [−1, 1]` (skewness),
    `μ ∈ ℝ` (location), `σ > 0` (scale).  The parameter constraints
    are enforced at the `StableClass` predicate level (B.4.2); the
    function itself is well-defined for arbitrary real parameters.

    Notes on the α = 1 case (paper Section IV-A):

    * The location parameter is shifted by `(2 β/π) · σ · log σ` — this
      is paper Eq. 4 verbatim, not a typo or rescaling artefact.  Audit
      2026-05-13 pass 5: the `σ` factor was previously omitted from the
      Lean transcription, now restored to match LaTeX source.
    * The `log|tσ|` inside the second-term parenthesis differs from
      the α ≠ 1 case, where the scale is absorbed into `|tσ|^α`.

    For `σ = 1` the α = 1 branch reduces to
        `exp(i μ t − |t| (1 + (2 i β/π) sgn(t) log|t|))`,
    which is the standard Cauchy-with-asymmetry form usually quoted
    in textbooks (the `σ·log σ` shift vanishes). -/
noncomputable def stableCharacteristicFunction (α β μ σ : ℝ) (t : ℝ) : ℂ :=
  if α = 1 then
    Complex.exp (
      Complex.I * (t * (2 * β * σ * Real.log σ / Real.pi + μ) : ℝ) -
        (|t * σ| : ℝ) *
          (1 + ((2 / Real.pi) * β * Real.sign t * Real.log |t * σ| : ℝ)
              * Complex.I))
  else
    Complex.exp (
      Complex.I * (μ * t : ℝ) -
        (σ ^ α * |t| ^ α : ℝ) *
          (1 - (β * Real.sign t * Real.tan (Real.pi * α / 2) : ℝ)
              * Complex.I))

/-! ## Stable class predicate (paper Section IV-A, todo B.4.2). -/

/-- **Stable class membership predicate** (paper Section IV-A, todo B.4.2).
    `StableClass φ α β μ σ` asserts that the (complex-valued)
    characteristic function `φ : ℝ → ℂ` matches the paper-Eq. 4 stable
    closed form with parameters
        `α ∈ (0, 2]`, `β ∈ [−1, 1]`, `μ ∈ ℝ`, `σ > 0`.
    Encodes the parameter constraints plus the verbatim equality
    `φ t = stableCharacteristicFunction α β μ σ t` for every `t : ℝ`. -/
structure StableClass (φ : ℝ → ℂ) (α β μ σ : ℝ) : Prop where
  alpha_pos : 0 < α
  alpha_le_two : α ≤ 2
  beta_ge : -1 ≤ β
  beta_le : β ≤ 1
  sigma_pos : 0 < σ
  matches_charfun : ∀ t, φ t = stableCharacteristicFunction α β μ σ t

/-! ## Algebraic power identity for the stable characteristic function
    (paper Eq. 4, multiplicativity under iid sums; algebraic content
    of todo B.4.3). -/

/-- **Stable charfun `ϕ(t)^n` identity, α ≠ 1 case** (paper Section IV-A).
    For `α ≠ 1` and `n ≥ 1`, the `n`-th power of the stable
    characteristic function with parameters `(α, β, μ, σ)` equals the
    stable characteristic function with the rescaled parameters
    `(α, β, n·μ, n^(1/α)·σ)`:
        `ϕ_{α, β, μ, σ}(t)^n = ϕ_{α, β, n μ, n^(1/α) σ}(t)`.
    Algebraic consequence of `Complex.exp_nat_mul` plus the scaling
    identity `n · σ^α = (n^(1/α) · σ)^α` for `n > 0`, `α > 0`. -/
theorem stable_charfun_pow_alpha_ne_one
    (α β μ σ : ℝ) (n : ℕ) (hn : 0 < n)
    (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) (hσ_pos : 0 < σ) (t : ℝ) :
    (stableCharacteristicFunction α β μ σ t) ^ n
      = stableCharacteristicFunction α β ((n : ℝ) * μ)
          ((n : ℝ) ^ (1 / α) * σ) t := by
  unfold stableCharacteristicFunction
  rw [ite_eq_right hα_ne_one, ite_eq_right hα_ne_one]
  -- Rewrite LHS = exp(n · z₁); reduce to exp(n · z₁) = exp(z₂).
  rw [← Complex.exp_nat_mul]
  congr 1
  -- Key real-line scaling identity: (n^(1/α) · σ)^α = n · σ^α.
  have hn_real_pos : (0:ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have h_pow_id : ((n : ℝ) ^ (1 / α) * σ) ^ α = (n : ℝ) * σ ^ α := by
    rw [Real.mul_rpow (le_of_lt (Real.rpow_pos_of_pos hn_real_pos _))
        hσ_pos.le]
    rw [← Real.rpow_mul hn_real_pos.le]
    rw [show (1 / α) * α = 1 from by field_simp]
    rw [Real.rpow_one]
  -- Rewrite the awkward `(n^(1/α)σ)^α` term in the RHS via h_pow_id (a
  -- real-line identity, lifted to ℂ).
  rw [h_pow_id]
  push_cast
  ring

/-- **Stable charfun `ϕ(t)^n` identity, α = 1 case** (paper Section IV-A).
    For `α = 1`, raising the stable charfun to the `n`-th power gives
    `exp(n · z)` where `z` is the α = 1 exponent of `ϕ(t)`.  Stated as
    an `exp(n · z)` form rather than as a rescaled `stableCharacteristicFunction`
    because the iid sum's α = 1 closure has a non-trivial location-parameter
    rescaling involving an extra `2β log(n) · σ · t / π` term coming from
    the `log|tσ|` factor (not a simple `μ_n = n μ`, `σ_n = nσ` scaling).

    Specifically, expanding `n · z = it·n·(2β log σ/π + μ)
                                     − n|tσ|·(1 + (2iβ/π) sgn(t) log|tσ|)`
    and matching against `Stable(1, β, μ_n, n σ)` would require
        `μ_n = nμ + 2β log σ (n − 1)/π − 2β log n/π + 2β nσ log n/π`,
    which is the correct paper-form rescaling but cumbersome to maintain
    as a separate theorem.  We leave the α = 1 closure here in the
    `exp(n · z)` form; the κ-metric application uses only α ≠ 1 (via
    `stable_sum_stable`). -/
theorem stable_charfun_pow_alpha_eq_one
    (β μ σ : ℝ) (n : ℕ) (t : ℝ) :
    (stableCharacteristicFunction 1 β μ σ t) ^ n
      = Complex.exp (
          ((n : ℝ) : ℂ) *
            (Complex.I * ((t * (2 * β * σ * Real.log σ / Real.pi + μ) : ℝ) : ℂ) -
              ((|t * σ| : ℝ) : ℂ) *
                (1 + (((2 / Real.pi) * β * Real.sign t * Real.log |t * σ| : ℝ) : ℂ)
                    * Complex.I))) := by
  unfold stableCharacteristicFunction
  rw [ite_eq_left rfl]
  rw [← Complex.exp_nat_mul]
  push_cast
  ring_nf

/-! ## Sum of iid stable r.v.'s is stable (paper Section IV-A, todo B.4.3). -/

/-- **Iid sum of stable r.v.'s is stable** (paper Section IV-A, todo B.4.3).
    Given a charfun `φ` in the α-stable class with `α ≠ 1`, and a
    `Sn_charfun` representing the iid n-fold sum's characteristic
    function (i.e. `Sn_charfun(t) = φ(t)^n`, the hypothesis below), the
    sum's charfun is itself in the stable class with rescaled
    parameters `μ_n = n μ`, `σ_n = n^(1/α) σ`.

    The iid-sum hypothesis `h_iid : Sn_charfun(t) = φ(t)^n` for all `t`
    is precisely the iid-characteristic-function multiplicativity
    statement (Mathlib `ProbabilityTheory.charFun_iid_sum`-style fact);
    by passing it in we sidestep the Mathlib gap of formalising iid
    random vectors and their joint charfun.  The algebraic remainder is
    a direct application of `stable_charfun_pow_alpha_ne_one`. -/
theorem stable_sum_stable
    {φ Sn_charfun : ℝ → ℂ} {α β μ σ : ℝ} {n : ℕ}
    (hn : 0 < n) (hα_ne_one : α ≠ 1)
    (hX : StableClass φ α β μ σ)
    (h_iid : ∀ t, Sn_charfun t = (φ t) ^ n) :
    StableClass Sn_charfun α β ((n : ℝ) * μ) ((n : ℝ) ^ (1 / α) * σ) := by
  refine ⟨hX.alpha_pos, hX.alpha_le_two, hX.beta_ge, hX.beta_le, ?_, ?_⟩
  · -- n^(1/α) σ > 0 from n > 0, σ > 0, α > 0.
    have hn_real_pos : (0:ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
    have h_pow_pos : 0 < (n : ℝ) ^ (1 / α) :=
      Real.rpow_pos_of_pos hn_real_pos _
    exact mul_pos h_pow_pos hX.sigma_pos
  · intro t
    rw [h_iid t]
    rw [hX.matches_charfun t]
    exact stable_charfun_pow_alpha_ne_one α β μ σ n hn hX.alpha_pos
      hα_ne_one hX.sigma_pos t

/-! ## κ_{n₀, n} = 2 − ᾱ on the stable class (paper Eq. 6, todo B.4.4). -/

/-- **Stable-class κ invariance** (paper Eq. 6, todo B.4.4).
    Specialisation of `kappa_stable_invariance_alphaBar` to the stable
    class: any MAD oracle `M` that scales as `c · n^(1/ᾱ(α))` (the iid
    sum's MAD scaling, derived from the `n^(1/α)·σ` scale parameter of
    `stable_sum_stable`) has constant κ-metric `2 − ᾱ(α)` across all
    `(n₀, n)` baselines.

    The MAD-scaling hypothesis `hM_form` is the operational input from
    the probability side; for a stable iid sum it follows from the
    `σ_n = n^(1/α) σ` scale of `stable_sum_stable` combined with the
    `MAD(c·X) = c·MAD(X)` scaling property of any non-degenerate
    distribution. -/
theorem stable_class_kappa_invariance {M : ℕ → ℝ} {c α : ℝ}
    (hc : 0 < c) (hα : 0 < α)
    (hM_form : ∀ k : ℕ, 0 < k → M k = c * (k : ℝ) ^ ((1 : ℝ) / stableAlphaBar α))
    {n₀ n : ℕ} (hn₀ : 0 < n₀) (h_lt : n₀ < n) :
    kappa M n₀ n = 2 - stableAlphaBar α :=
  kappa_stable_invariance_alphaBar hc hα hM_form hn₀ h_lt

end TailOptionPricing
